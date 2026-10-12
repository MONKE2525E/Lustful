// `lust daemon`: keeps a warm compile session per file and serves requests from the `lust` client
// over a Unix socket (see protocol.rs). One request at a time.
// One daemon per socket: it holds an flock on `<socket>.lock` (which holds its pid) for its
// whole life. A second daemon sees the lock taken and exits without touching the socket, so
// a stale socket file can always be removed safely by the lock holder.
// The daemon exits on its own after an idle span (`LUST_DAEMON_IDLE`, default 30 minutes;
// see protocol::daemon_idle) and removes its socket on the way out.
// Two safety nets make a warm answer as trustworthy as a cold compile:
//   - A panic in one request is caught. That file's session is dropped, the request is answered
//     by a fresh session, and the daemon keeps serving.
//   - The fresh-session guard: when the incremental answer is an error, the request is redone in
//     a fresh session. If the answers differ, the fresh session and its answer are adopted and
//     the event is logged (lines starting with "guard:"). If they match, the warm session (and
//     its caches) is kept. Success answers are trusted as they are.
use crate::driver::{self, Request, Session};
use crate::protocol::{self, Response};
use std::collections::HashMap;
use std::io::{BufReader, Seek, Write};
use std::os::unix::io::AsRawFd;
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};

unsafe extern "C" {
    fn flock(fd: i32, operation: i32) -> i32;
    fn poll(fds: *mut PollFd, nfds: u64, timeout_ms: i32) -> i32;
    fn kill(pid: i32, sig: i32) -> i32;
}
const LOCK_EX: i32 = 2;
const LOCK_NB: i32 = 4;
const POLLIN: i16 = 1;

#[repr(C)]
struct PollFd {
    fd: i32,
    events: i16,
    revents: i16,
}

/// Waits until `listener` can accept, or `timeout` passes. None timeout waits forever.
/// This is how the idle exit costs no latency: no sleep-based polling.
fn wait_readable(listener: &UnixListener, timeout: Option<std::time::Duration>) -> bool {
    let mut pfd = PollFd { fd: listener.as_raw_fd(), events: POLLIN, revents: 0 };
    let ms = timeout.map_or(-1, |d| d.as_millis().min(i32::MAX as u128) as i32);
    // SAFETY: one valid pollfd over a live listener fd, for the duration of the call.
    unsafe { poll(&mut pfd, 1, ms) > 0 && pfd.revents & POLLIN != 0 }
}

struct Entry {
    session: Session,
    /// Directory stem for this file's sessions; fresh sessions get "<dir>r<n>".
    dir: PathBuf,
    resets: u64,
}

impl Entry {
    fn fresh_dir(&mut self) -> PathBuf {
        self.resets += 1;
        let mut d = self.dir.as_os_str().to_owned();
        d.push(format!("r{}", self.resets));
        PathBuf::from(d)
    }
}

/// Compiles with the entry's warm session, with the panic net and the fresh-session guard.
fn compile_guarded(entry: &mut Entry, req: &Request) -> Response {
    let first = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| driver::compile(req, &mut entry.session)));
    match first {
        Ok(r) if r.code == 0 || r.code == 2 => r,
        first => {
            // An error answer, or a panic: redo in a fresh session and trust that instead.
            let dir = entry.fresh_dir();
            let mut fresh = Session::new(dir.clone(), true);
            let second = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| driver::compile(req, &mut fresh)));
            match second {
                Ok(r) => {
                    let same = matches!(&first, Ok(f) if f.code == r.code && f.stdout == r.stdout && f.stderr == r.stderr);
                    if same {
                        // The warm session was right; keep its caches. The fresh build failed
                        // the same way, so nothing links its base files: remove them.
                        let _ = std::fs::remove_dir_all(&dir);
                    } else {
                        let first_line = |s: &str| s.lines().next().unwrap_or("").chars().take(120).collect::<String>();
                        eprintln!(
                            "guard: fresh session disagreed for {} (warm {}, fresh {}); adopting fresh; warm: {}; fresh: {}",
                            req.file.display(),
                            first.as_ref().map_or("panic".to_string(), |f| f.code.to_string()),
                            r.code,
                            first.as_ref().map_or("<panic>".to_string(), |f| first_line(&f.stderr)),
                            first_line(&r.stderr)
                        );
                        entry.session = fresh;
                    }
                    r
                }
                Err(_) => {
                    // Even a fresh compile panicked. Drop the session so the next request starts
                    // clean, and say so plainly instead of dying.
                    eprintln!("guard: compile panicked in a fresh session for {}", req.file.display());
                    let dir = entry.fresh_dir();
                    entry.session = Session::new(dir, true);
                    Response { stderr: "error: internal: compile failed in a fresh session\n".into(), code: 3, ..Default::default() }
                }
            }
        }
    }
}

/// Serves requests until idle. Each file has its own session.
pub fn serve(sock: &Path) -> ! {
    // Single instance, decided before anything touches the socket.
    let lock_path = protocol::daemon_lock_path(sock);
    let mut lock_file = std::fs::OpenOptions::new().create(true).write(true).truncate(false).open(&lock_path).unwrap_or_else(|e| {
        eprintln!("error: cannot open {}: {e}", lock_path.display());
        std::process::exit(2);
    });
    // SAFETY: flock on a live fd. LOCK_EX | LOCK_NB: fail at once when another daemon holds it.
    if unsafe { flock(lock_file.as_raw_fd(), LOCK_EX | LOCK_NB) } != 0 {
        eprintln!("lust daemon: another daemon already serves {}", sock.display());
        std::process::exit(0);
    }
    let _ = lock_file.set_len(0);
    let _ = lock_file.rewind();
    let _ = write!(lock_file, "{}", std::process::id());
    let _ = lock_file.flush();
    // `lock_file` stays open for the whole serve; process exit releases the flock.

    let _ = std::fs::remove_file(sock);
    let listener = UnixListener::bind(sock).unwrap_or_else(|e| {
        eprintln!("error: cannot bind {}: {e}", sock.display());
        std::process::exit(2);
    });
    if listener.set_nonblocking(true).is_err() {
        eprintln!("error: cannot set {} nonblocking", sock.display());
        std::process::exit(2);
    }
    eprintln!("lust daemon: listening on {}", sock.display());
    let idle = protocol::daemon_idle();
    let mut last = std::time::Instant::now();
    let base = std::env::temp_dir().join(format!("lust-daemon-{}", std::process::id()));
    let mut sessions: HashMap<PathBuf, Entry> = HashMap::new();
    // Autostart pre-warm: the client that started us names the file it is compiling
    // cold. Checking it here fills a session, so the next command is truly warm. It
    // waits for that cold process to exit first, so it never competes with it. A
    // request that arrives meanwhile waits in the listen backlog.
    if let Ok(pid) = std::env::var("LUST_DAEMON_PREWARM_AFTER")
        && let Ok(pid) = pid.parse::<i32>()
    {
        let start = std::time::Instant::now();
        // SAFETY: signal 0 only probes whether the pid exists.
        while unsafe { kill(pid, 0) } == 0 && start.elapsed() < std::time::Duration::from_secs(60) {
            std::thread::sleep(std::time::Duration::from_millis(2));
        }
    }
    if let Ok(file) = std::env::var("LUST_DAEMON_PREWARM") {
        let file = PathBuf::from(file);
        let req = protocol::Request {
            cmd: protocol::Cmd::Check,
            out: file.with_extension(""),
            json: false,
            timings: false,
            debug: false,
            emit_c: None,
            max_errors: 20,
            run_args: None,
            harness: false,
            file: file.clone(),
        };
        let entry = sessions.entry(file).or_insert_with(|| {
            let dir = base.join("0");
            Entry { session: Session::new(dir.clone(), true), dir, resets: 0 }
        });
        let _ = compile_guarded(entry, &req);
        last = std::time::Instant::now();
    }
    loop {
        // Block in poll() until a connection lands or the idle span runs out.
        let left = idle.map(|d| d.saturating_sub(last.elapsed()));
        if !wait_readable(&listener, left) {
            if idle.is_some_and(|d| last.elapsed() >= d) {
                let _ = std::fs::remove_file(sock);
                eprintln!("lust daemon: idle timeout, exiting");
                std::process::exit(0);
            }
            continue;
        }
        let mut conn = match listener.accept() {
            Ok((conn, _)) => conn,
            Err(_) => continue,
        };
        last = std::time::Instant::now();
        let _ = conn.set_nonblocking(false);
        let req = {
            let mut reader = BufReader::new(&conn);
            protocol::read_request(&mut reader)
        };
        let resp = match req {
            Some(req) => {
                let n = sessions.len();
                let entry = sessions.entry(req.file.clone()).or_insert_with(|| {
                    let dir = base.join(n.to_string());
                    Entry { session: Session::new(dir.clone(), true), dir, resets: 0 }
                });
                compile_guarded(entry, &req)
            }
            None => Response { stderr: "error: bad request\n".into(), code: 2, ..Default::default() },
        };
        let _ = protocol::write_response(&mut conn, &resp);
        last = std::time::Instant::now();
    }
}
