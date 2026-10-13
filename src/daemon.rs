// `lust daemon`: keeps a warm compile session per crate selection (`SessionKey`,
// docs/ARCH.md section 1.8) and serves requests from the `lust` client over a Unix
// socket (see protocol.rs). One request at a time on the serve loop; background
// guard checks (below) compile in their own sessions on their own threads.
// One daemon per socket: it holds an flock on `<socket>.lock` (which holds its pid) for its
// whole life. A second daemon sees the lock taken and exits without touching the socket, so
// a stale socket file can always be removed safely by the lock holder.
// The daemon exits on its own after an idle span (`LUST_DAEMON_IDLE`, default 30 minutes;
// see protocol::daemon_idle) and removes its socket on the way out. SIGTERM and SIGINT
// take the same controlled exit (a flag plus a self-pipe wakeup; the serve loop does
// the cleanup, never the signal handler).
// Temp state: sessions work under `<temp>/lust-daemon-<pid>/`, which every controlled
// exit deletes, and which a starting daemon also deletes for any pid that is gone
// (that is what cleans up after SIGKILL and crashes). Deleting it is safe for built
// executables: base libraries live in a persistent dir, not here (see
// `resolve_base_dir` in driver/compile.rs). On exit each base dir is swept too, so
// bases of deleted executables are removed while bases of kept executables stay.
// Two safety nets watch the warm answers:
//   - A panic in one request is caught. That crate's session is dropped, the request is
//     answered by a fresh session at once, and the daemon keeps serving.
//   - The fresh-session guard: when the incremental answer is an error, the client gets
//     that answer at once and the request is redone in a fresh session in the background.
//     If the answers differ, the event is logged loudly (lines starting with "guard:"),
//     the fresh session replaces the warm one, and the next answer for that crate is
//     recomputed in another new session. If they match, the warm session (and its caches)
//     is kept. Success answers are trusted as they are. Background results are compared
//     only when the source bytes did not change during the check, and they are applied
//     on the serve loop (`GuardJobs::drain`), never on the worker thread. The fuzz gate
//     waits for all started checks to finish (`guard-check: start/done` log lines) and
//     counts any "guard:" line as a failure, as it did when the guard was synchronous.
use crate::driver::{self, Request, Session};
use crate::protocol::{self, Response, SessionKey};
use std::collections::HashMap;
use std::io::{BufReader, Seek, Write};
use std::os::unix::fs::MetadataExt;
use std::os::unix::io::AsRawFd;
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::sync::mpsc::{Receiver, Sender};

unsafe extern "C" {
    fn flock(fd: i32, operation: i32) -> i32;
    fn poll(fds: *mut PollFd, nfds: u64, timeout_ms: i32) -> i32;
    fn kill(pid: i32, sig: i32) -> i32;
    fn signal(signum: i32, handler: usize) -> usize;
    fn pipe(fds: *mut i32) -> i32;
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
    fn fcntl(fd: i32, cmd: i32, arg: i32) -> i32;
    fn getuid() -> u32;
}
const SIGINT: i32 = 2;
const SIGTERM: i32 = 15;
const F_SETFD: i32 = 2;
const FD_CLOEXEC: i32 = 1;

/// Set by the SIGTERM/SIGINT handler; the serve loop sees it and exits
/// through the same cleanup as the idle timeout.
static SHUTDOWN: AtomicBool = AtomicBool::new(false);
/// The write end of the wakeup pipe the handler pokes, so a `poll` for
/// the idle timeout wakes at once instead of sleeping through a signal.
static WAKE_W: AtomicI32 = AtomicI32::new(-1);

/// Async-signal-safe: only a flag store and one pipe byte.
extern "C" fn on_shutdown_signal(_sig: i32) {
    SHUTDOWN.store(true, Ordering::SeqCst);
    let fd = WAKE_W.load(Ordering::SeqCst);
    if fd >= 0 {
        // SAFETY: `fd` is the pipe write end installed by `serve`; one byte.
        unsafe { write(fd, b"x".as_ptr(), 1) };
    }
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

/// Waits until `listener` can accept, a shutdown signal pokes the wake
/// pipe, or `timeout` passes. None timeout waits forever. True only for
/// a readable listener; the caller checks `SHUTDOWN` itself. This is how
/// the idle exit costs no latency: no sleep-based polling.
fn wait_readable(listener: &UnixListener, wake: i32, timeout: Option<std::time::Duration>) -> bool {
    let mut pfds = [PollFd { fd: listener.as_raw_fd(), events: POLLIN, revents: 0 }, PollFd { fd: wake, events: POLLIN, revents: 0 }];
    let ms = timeout.map_or(-1, |d| d.as_millis().min(i32::MAX as u128) as i32);
    // SAFETY: two valid pollfds over live fds, for the duration of the call.
    unsafe { poll(pfds.as_mut_ptr(), 2, ms) > 0 && pfds[0].revents & POLLIN != 0 }
}

/// The pid in a lust temp name (`lust-daemon-<pid>`, `lust-<pid>`,
/// `lust-test-<pid>`, `lust-rustc-check-<pid>.rmeta`), if the name is
/// exactly one of those shapes. Prefixes only: a name like
/// `lust-daemon-glue-<random>` is a test harness dir, not pid-owned.
fn stale_temp_pid(name: &str) -> Option<u32> {
    let digits = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit());
    if let Some(rest) = name.strip_prefix("lust-rustc-check-")
        && let Some(pid) = rest.strip_suffix(".rmeta")
    {
        return if digits(pid) { pid.parse().ok() } else { None };
    }
    for prefix in ["lust-daemon-", "lust-test-", "lust-"] {
        if let Some(rest) = name.strip_prefix(prefix) {
            return if digits(rest) { rest.parse().ok() } else { None };
        }
    }
    None
}

/// True when a process with `pid` exists. Signal 0 plus the /proc
/// fallback for a pid owned by another user (where signal 0 fails).
/// A reused pid reads as alive, which only keeps a stale dir longer.
fn pid_alive(pid: u32) -> bool {
    // SAFETY: signal 0 only probes whether the pid exists.
    (pid > 0 && unsafe { kill(pid as i32, 0) } == 0) || Path::new(&format!("/proc/{pid}")).exists()
}

/// Deletes lust temp dirs and files from processes that are gone:
/// at daemon start, this is the cleanup for daemons and cold compiles
/// that died without one (SIGKILL, crash). Only exact pid-named
/// entries owned by the current user are removed; symlinks and
/// anything still running are left alone. Built executables do not
/// depend on these dirs (base libraries moved to a persistent dir).
fn sweep_stale_temp_dirs() {
    let tmp = std::env::temp_dir();
    let me = std::process::id();
    // SAFETY: getuid has no arguments and cannot fail.
    let uid = unsafe { getuid() };
    let Ok(rd) = std::fs::read_dir(&tmp) else { return };
    for e in rd.flatten() {
        let name = e.file_name().to_string_lossy().into_owned();
        let Some(pid) = stale_temp_pid(&name) else { continue };
        if pid == me || pid_alive(pid) {
            continue;
        }
        let path = e.path();
        let Ok(meta) = path.symlink_metadata() else { continue };
        if meta.uid() != uid {
            continue;
        }
        if meta.is_dir() {
            let _ = std::fs::remove_dir_all(&path);
        } else if meta.is_file() {
            let _ = std::fs::remove_file(&path);
        }
    }
}

/// The one controlled daemon exit (idle timeout and shutdown signals):
/// sweep each session's base dir (dead executables lose their bases,
/// kept executables keep theirs), delete the per-daemon temp dir and
/// the socket, then exit. Guard workers may still run on a signal
/// exit; they die with the process, and any dir they recreate in the
/// last instant is stale-pid swept by the next daemon.
fn shutdown(sock: &Path, base: &Path, sessions: &HashMap<SessionKey, Entry>, why: &str) -> ! {
    let mut base_dirs: Vec<PathBuf> = Vec::new();
    for entry in sessions.values() {
        if let Some(dir) = entry.session.base_dir()
            && !base_dirs.iter().any(|d| d == dir)
        {
            base_dirs.push(dir.to_path_buf());
        }
    }
    for dir in &base_dirs {
        driver::sweep_bases(dir);
    }
    let _ = std::fs::remove_dir_all(base);
    let _ = std::fs::remove_file(sock);
    eprintln!("lust daemon: {why}, exiting");
    std::process::exit(0);
}

/// The per-request refresh key of one crate selection: the Cargo graph
/// key (protocol::graph_key, section 1.1) mixed with the build script
/// output hash (driver::buildscript). Routing by SessionKey alone would
/// reuse a session resolved under an old Cargo.toml, lock file, config,
/// or build script; when this key moves, the entry's session is
/// replaced before the request is served.
fn refresh_key(key: &SessionKey) -> u64 {
    // Build script first: a stale record re-runs Cargo, which can
    // create or update Cargo.lock, and the graph key must describe
    // the graph as it stands after that run, not before it.
    let build_script = match protocol::manifest_dir(key) {
        Some(dir) => match crate::driver::buildscript::refresh(&dir, &crate::driver::cache::cache_dir(&key.krate.root)) {
            r @ crate::driver::buildscript::Refresh::Failed { .. } => {
                if let crate::driver::buildscript::Refresh::Failed { error, .. } = &r {
                    eprintln!("lust daemon: build script refresh failed for {}: {error}", dir.display());
                }
                r.hash()
            }
            r => r.hash(),
        },
        None => 0,
    };
    protocol::graph_key(key) ^ build_script.rotate_left(17)
}

struct Entry {
    session: Session,
    /// Directory stem for this crate's sessions; fresh sessions get "<dir>r<n>".
    dir: PathBuf,
    resets: u64,
    /// The refresh key (graph key + build script hash) the current
    /// session was resolved under. See `refresh_key`.
    refresh_key: u64,
    /// Requests served for this key. A background guard carries the count at
    /// its spawn, so a slow older result cannot replace a session that a
    /// newer guard already replaced (`replaced_gen`).
    served: u64,
    replaced_gen: u64,
    /// A background guard found a mismatch: the next request for this key is
    /// recomputed in a brand-new session before it is answered.
    recompute_next: bool,
}

impl Entry {
    fn fresh_dir(&mut self) -> PathBuf {
        self.resets += 1;
        let mut d = self.dir.as_os_str().to_owned();
        d.push(format!("r{}", self.resets));
        PathBuf::from(d)
    }

    fn new(dir: PathBuf, key: SessionKey) -> Entry {
        let rk = refresh_key(&key);
        Entry {
            session: Session::new(dir.clone(), true, key),
            dir,
            resets: 0,
            refresh_key: rk,
            served: 0,
            replaced_gen: 0,
            recompute_next: false,
        }
    }
}

/// Replaces the entry's session with a brand-new one and deletes the
/// old session's object dir. Object dirs are pure temp state now that
/// base libraries live in a persistent dir, so a replaced session
/// (panic recovery, guard mismatch, graph change) must not leave its
/// dir behind for the daemon's whole life.
fn replace_session(entry: &mut Entry, key: &SessionKey) {
    let dir = entry.fresh_dir();
    let old = std::mem::replace(&mut entry.session, Session::new(dir, true, key.clone()));
    let _ = std::fs::remove_dir_all(old.obj_dir());
}

/// What one background fresh-session check found.
enum GuardOutcome {
    /// A fresh compile of the same source bytes; its session travels along
    /// for adoption on a mismatch.
    Fresh(Response),
    /// The fresh compile panicked.
    Panicked,
    /// The source bytes changed during the check: no comparison is possible.
    Stale,
}

/// One finished background check, sent from its worker thread to the serve loop.
struct GuardDone {
    seq: u64,
    key: SessionKey,
    served: u64,
    /// The answer the client already got.
    warm: Response,
    /// The fresh session's object dir (removed unless the session is adopted).
    dir: PathBuf,
    session: Option<Session>,
    outcome: GuardOutcome,
}

/// Background fresh-session checks: spawn on the serve loop, apply on the
/// serve loop. Workers only compile in their own fresh session and send the
/// result back; they never touch the session map. Start and done log lines
/// come in pairs by sequence number, so a reader of the daemon log (the fuzz
/// gate) can wait until every started check has been applied.
struct GuardJobs {
    tx: Sender<GuardDone>,
    rx: Receiver<GuardDone>,
    next_seq: u64,
    pending: usize,
}

impl GuardJobs {
    fn new() -> GuardJobs {
        let (tx, rx) = std::sync::mpsc::channel();
        GuardJobs { tx, rx, next_seq: 0, pending: 0 }
    }

    /// Redoes `req` in a fresh session on a new thread. `src` is the source
    /// bytes read on the serve loop right after the warm compile; the worker
    /// compares only when the file still holds exactly those bytes before
    /// and after its compile, so an edit in between reads as stale, never as
    /// a guard mismatch.
    fn spawn(&mut self, req: Request, warm: Response, src: Vec<u8>, dir: PathBuf, served: u64) {
        self.next_seq += 1;
        let seq = self.next_seq;
        self.pending += 1;
        eprintln!("guard-check: start {seq} for {}", req.file.display());
        let tx = self.tx.clone();
        let key = req.session.clone();
        std::thread::spawn(move || {
            let work_dir = dir.clone();
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let same = |req: &Request| std::fs::read(&req.file).ok().as_deref() == Some(&src[..]);
                if !same(&req) {
                    return (GuardOutcome::Stale, None);
                }
                let mut fresh = Session::new(work_dir, true, req.session.clone());
                match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| driver::compile(&req, &mut fresh))) {
                    Ok(resp) if same(&req) => (GuardOutcome::Fresh(resp), Some(fresh)),
                    Ok(_) => (GuardOutcome::Stale, None),
                    Err(_) => (GuardOutcome::Panicked, None),
                }
            }));
            // A panic anywhere in the worker still produces a done record, so
            // `pending` and the log's start/done counts always settle.
            let (outcome, session) = result.unwrap_or((GuardOutcome::Panicked, None));
            let _ = tx.send(GuardDone { seq, key, served, warm, dir, session, outcome });
        });
    }

    /// Applies every finished check. Runs only on the serve loop.
    fn drain(&mut self, sessions: &mut HashMap<SessionKey, Entry>) {
        while let Ok(done) = self.rx.try_recv() {
            self.pending -= 1;
            apply_guard(sessions, done);
        }
    }
}

/// First line of a response's stderr, for guard log lines.
fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or("").chars().take(120).collect()
}

/// Applies one finished background check to the session map. On a real
/// mismatch the fresh session is adopted and the next answer for the key is
/// marked recomputed; a result from before the last such replacement is
/// dropped (its bug is already reported, its session already replaced).
fn apply_guard(sessions: &mut HashMap<SessionKey, Entry>, mut done: GuardDone) {
    let file = done.key.krate.root.display().to_string();
    let seq = done.seq;
    match done.outcome {
        GuardOutcome::Stale => {
            let _ = std::fs::remove_dir_all(&done.dir);
            eprintln!("guard-check: done {seq} stale for {file} (source changed during the check)");
        }
        GuardOutcome::Panicked => {
            let _ = std::fs::remove_dir_all(&done.dir);
            if let Some(entry) = sessions.get_mut(&done.key)
                && done.served > entry.replaced_gen
            {
                eprintln!("guard: background fresh compile panicked for {file}; dropping the session, next answer recomputed");
                replace_session(entry, &done.key);
                entry.replaced_gen = done.served;
                entry.recompute_next = true;
            }
            eprintln!("guard-check: done {seq} panic for {file}");
        }
        GuardOutcome::Fresh(ref fresh) => {
            let same = fresh.code == done.warm.code && fresh.stdout == done.warm.stdout && fresh.stderr == done.warm.stderr;
            if same {
                // The warm session was right; keep its caches. The fresh
                // build failed the same way, so nothing links its base
                // files: remove them.
                let _ = std::fs::remove_dir_all(&done.dir);
                eprintln!("guard-check: done {seq} match for {file}");
                return;
            }
            match sessions.get_mut(&done.key) {
                Some(entry) if done.served > entry.replaced_gen => {
                    eprintln!(
                        "guard: background fresh session disagreed for {file} (warm {}, fresh {}); adopting fresh, next answer recomputed; warm: {}; fresh: {}",
                        done.warm.code,
                        fresh.code,
                        first_line(&done.warm.stderr),
                        first_line(&fresh.stderr)
                    );
                    let old = std::mem::replace(&mut entry.session, done.session.take().expect("a fresh outcome carries its session"));
                    let _ = std::fs::remove_dir_all(old.obj_dir());
                    entry.replaced_gen = done.served;
                    entry.recompute_next = true;
                    eprintln!("guard-check: done {seq} mismatch for {file}");
                }
                _ => {
                    let _ = std::fs::remove_dir_all(&done.dir);
                    eprintln!("guard-check: done {seq} mismatch for {file} (already replaced by a newer check)");
                }
            }
        }
    }
}

/// Compiles `req` in a brand-new session, which replaces the entry's. The
/// bool is false when even the fresh compile panicked (the entry then holds
/// another new empty session and the answer is the code 3 plain failure).
fn compile_fresh(entry: &mut Entry, req: &Request) -> (Response, bool) {
    let dir = entry.fresh_dir();
    let mut fresh = Session::new(dir, true, req.session.clone());
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| driver::compile(req, &mut fresh))) {
        Ok(r) => {
            let old = std::mem::replace(&mut entry.session, fresh);
            let _ = std::fs::remove_dir_all(old.obj_dir());
            (r, true)
        }
        Err(_) => {
            eprintln!("guard: compile panicked in a fresh session for {}", req.file.display());
            let _ = std::fs::remove_dir_all(fresh.obj_dir());
            replace_session(entry, &req.session);
            (Response { stderr: "error: internal: compile failed in a fresh session\n".into(), code: 3, ..Default::default() }, false)
        }
    }
}

/// Compiles with the entry's warm session, with the panic net and the
/// fresh-session guard. An error answer goes to the client at once and is
/// rechecked in the background (`jobs`); a panic, or a request marked
/// recomputed by an earlier mismatch, is answered from a fresh session here.
fn compile_guarded(entry: &mut Entry, req: &Request, jobs: &mut GuardJobs) -> Response {
    entry.served += 1;
    let served = entry.served;
    if entry.recompute_next {
        entry.recompute_next = false;
        eprintln!("guard-check: recomputing {} in a fresh session (marked by a background mismatch)", req.file.display());
        // This answer already comes from a fresh session, so no background
        // check is spawned for it.
        return compile_fresh(entry, req).0;
    }
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| driver::compile(req, &mut entry.session))) {
        Ok(r) if r.code == 0 || r.code == 2 => r,
        Ok(r) if r.code == 3 && r.stderr.contains("function count mismatch") => {
            // The warm session's scan and Ast disagree on the fn list
            // (unusual shapes: items moved into bodies). The session
            // state is not a sound basis for an answer, like after a
            // panic: redo in a fresh session at once and hand that out.
            eprintln!("lust daemon: session fn count mismatch for {}; recomputed in a fresh session", req.file.display());
            compile_fresh(entry, req).0
        }
        Ok(r) => {
            // An error answer: hand it out now, verify it in the background.
            // Without the current source bytes no honest comparison is
            // possible, so a read failure here just skips the check.
            if let Ok(src) = std::fs::read(&req.file) {
                let dir = entry.fresh_dir();
                jobs.spawn(req.clone(), r.clone(), src, dir, served);
            }
            r
        }
        Err(_) => {
            // A panic has no answer to hand out and the session may be
            // corrupt: redo in a fresh session at once, as before.
            let (r, fresh_ok) = compile_fresh(entry, req);
            if fresh_ok {
                eprintln!(
                    "guard: compile panicked in the warm session for {}; answered from a fresh session (fresh {}); fresh: {}",
                    req.file.display(),
                    r.code,
                    first_line(&r.stderr)
                );
            }
            r
        }
    }
}

/// The session entry for `key`, made on first use. New keys get the next
/// directory number (entries are never removed, so numbers stay unique)
/// and one log line naming the full key and its directory.
fn entry_for<'m>(sessions: &'m mut HashMap<SessionKey, Entry>, base: &Path, key: &SessionKey) -> &'m mut Entry {
    use std::collections::hash_map::Entry as MapEntry;
    let n = sessions.len();
    match sessions.entry(key.clone()) {
        MapEntry::Occupied(e) => e.into_mut(),
        MapEntry::Vacant(v) => {
            let dir = base.join(n.to_string());
            eprintln!("lust daemon: new session for crate {} in {}", key.describe(), dir.display());
            v.insert(Entry::new(dir, key.clone()))
        }
    }
}

/// Serves requests until idle. Each crate selection (`SessionKey`) has its own session.
pub fn serve(sock: &Path) -> ! {
    // Clean up temp dirs of daemons and cold compiles that died without
    // a cleanup (SIGKILL, crash). Pid and owner checks protect anything
    // live, including a daemon already serving this socket.
    sweep_stale_temp_dirs();
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
    // Shutdown signals take the controlled exit: the handler only sets
    // a flag and pokes this pipe (see `wait_readable` and `shutdown`).
    let mut wake_fds = [0i32; 2];
    // SAFETY: `wake_fds` has room for the two fds pipe(2) writes.
    if unsafe { pipe(wake_fds.as_mut_ptr()) } != 0 {
        eprintln!("error: cannot create the daemon wakeup pipe");
        std::process::exit(2);
    }
    let (wake_r, wake_w) = (wake_fds[0], wake_fds[1]);
    // SAFETY: fcntl F_SETFD on the fds just made; tcc children must not inherit them.
    unsafe {
        fcntl(wake_r, F_SETFD, FD_CLOEXEC);
        fcntl(wake_w, F_SETFD, FD_CLOEXEC);
        WAKE_W.store(wake_w, Ordering::SeqCst);
        signal(SIGINT, on_shutdown_signal as usize);
        signal(SIGTERM, on_shutdown_signal as usize);
    }
    eprintln!("lust daemon: listening on {}", sock.display());
    let idle = protocol::daemon_idle();
    let mut last = std::time::Instant::now();
    let base = std::env::temp_dir().join(format!("lust-daemon-{}", std::process::id()));
    let mut sessions: HashMap<SessionKey, Entry> = HashMap::new();
    let mut jobs = GuardJobs::new();
    // Autostart pre-warm: the client that started us names the file it is compiling
    // cold. Checking it here fills a session, so the next command is truly warm. It
    // waits for that cold process to exit first, so it never competes with it. A
    // request that arrives meanwhile waits in the listen backlog.
    if let Ok(pid) = std::env::var("LUST_DAEMON_PREWARM_AFTER")
        && let Ok(pid) = pid.parse::<i32>()
    {
        let start = std::time::Instant::now();
        // SAFETY: signal 0 only probes whether the pid exists.
        while unsafe { kill(pid, 0) } == 0 && start.elapsed() < std::time::Duration::from_secs(60) && !SHUTDOWN.load(Ordering::SeqCst) {
            std::thread::sleep(std::time::Duration::from_millis(2));
        }
    }
    if !SHUTDOWN.load(Ordering::SeqCst)
        && let Ok(file) = std::env::var("LUST_DAEMON_PREWARM")
    {
        let file = PathBuf::from(file);
        let req = protocol::Request {
            cmd: protocol::Cmd::Check,
            session: SessionKey::synthetic(&file, false),
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
        let entry = entry_for(&mut sessions, &base, &req.session);
        let _ = compile_guarded(entry, &req, &mut jobs);
        last = std::time::Instant::now();
    }
    loop {
        if SHUTDOWN.load(Ordering::SeqCst) {
            shutdown(sock, &base, &sessions, "shutdown signal");
        }
        // Apply any finished guard checks before waiting, so a mismatch
        // replaces its session before the next request for that key.
        jobs.drain(&mut sessions);
        // Block in poll() until a connection lands or the idle span runs out.
        // While guard checks run, wake often to drain them; the idle exit
        // also waits for them, so a mismatch is never lost at shutdown.
        let mut left = idle.map(|d| d.saturating_sub(last.elapsed()));
        if jobs.pending > 0 {
            let cap = std::time::Duration::from_millis(20);
            left = Some(left.map_or(cap, |d| d.min(cap)));
        }
        if !wait_readable(&listener, wake_r, left) {
            if jobs.pending == 0 && idle.is_some_and(|d| last.elapsed() >= d) {
                shutdown(sock, &base, &sessions, "idle timeout");
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
                // Finished guard checks for this key land before its next
                // compile, so a marked recompute takes effect here.
                jobs.drain(&mut sessions);
                let entry = entry_for(&mut sessions, &base, &req.session);
                // Graph and build-script routing (sections 1.1, 1.8): if
                // a covered file changed since this session was made,
                // replace it before serving, never after.
                let rk = refresh_key(&req.session);
                if entry.refresh_key != rk {
                    eprintln!("lust daemon: graph or build script changed for crate {}; starting a fresh session", req.session.describe());
                    replace_session(entry, &req.session);
                    entry.refresh_key = rk;
                }
                compile_guarded(entry, &req, &mut jobs)
            }
            None => Response { stderr: "error: bad request\n".into(), code: 2, ..Default::default() },
        };
        let _ = protocol::write_response(&mut conn, &resp);
        last = std::time::Instant::now();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn resp(code: i32, stderr: &str) -> Response {
        Response { stdout: String::new(), stderr: stderr.into(), code, ran: false }
    }

    fn done(key: &SessionKey, seq: u64, served: u64, warm: Response, fresh: Response, dir: PathBuf) -> GuardDone {
        GuardDone {
            seq,
            key: key.clone(),
            served,
            warm,
            session: Some(Session::new(dir.clone(), true, key.clone())),
            dir,
            outcome: GuardOutcome::Fresh(fresh),
        }
    }

    /// The background mismatch path, which no live incremental bug reaches
    /// today: a differing fresh answer replaces the session and marks the
    /// next answer recomputed; an older result after that replacement is
    /// dropped; an equal answer keeps the warm session untouched.
    #[test]
    fn guard_apply_adopts_mismatch_and_drops_stale_results() {
        let base = std::env::temp_dir().join(format!("lust-guard-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        let key = SessionKey::synthetic(Path::new("/tmp/g/main.rs"), false);
        let mut sessions: HashMap<SessionKey, Entry> = HashMap::new();
        let entry = entry_for(&mut sessions, &base, &key);
        entry.served = 5;
        let warm_dir = entry.session.obj_dir().to_path_buf();

        // Mismatch at served=3: adopt the fresh session, mark recompute.
        apply_guard(&mut sessions, done(&key, 1, 3, resp(1, "warm err\n"), resp(1, "fresh err\n"), base.join("f1")));
        let entry = sessions.get(&key).unwrap();
        assert_eq!(entry.session.obj_dir(), base.join("f1").as_path(), "fresh session adopted");
        assert!(entry.recompute_next, "next answer marked recomputed");
        assert_eq!(entry.replaced_gen, 3);

        // An older result (served=2) after the replacement changes nothing.
        apply_guard(&mut sessions, done(&key, 2, 2, resp(1, "warm err\n"), resp(0, ""), base.join("f2")));
        let entry = sessions.get(&key).unwrap();
        assert_eq!(entry.session.obj_dir(), base.join("f1").as_path(), "stale result dropped");
        assert_eq!(entry.replaced_gen, 3);

        // Equal answers keep the current session and clear nothing.
        let same = resp(1, "same err\n");
        apply_guard(&mut sessions, done(&key, 3, 5, same.clone(), same, base.join("f3")));
        let entry = sessions.get(&key).unwrap();
        assert_eq!(entry.session.obj_dir(), base.join("f1").as_path(), "match keeps the session");
        assert!(entry.recompute_next, "the earlier recompute mark stands");
        assert_ne!(entry.session.obj_dir(), warm_dir.as_path());
        let _ = std::fs::remove_dir_all(&base);
    }

    /// Only exact pid-named lust temp entries are sweep candidates.
    #[test]
    fn stale_temp_pid_parses_only_pid_names() {
        assert_eq!(stale_temp_pid("lust-daemon-123"), Some(123));
        assert_eq!(stale_temp_pid("lust-123"), Some(123));
        assert_eq!(stale_temp_pid("lust-test-123"), Some(123));
        assert_eq!(stale_temp_pid("lust-rustc-check-123.rmeta"), Some(123));
        assert_eq!(stale_temp_pid("lust-daemon-glue-abc"), None);
        assert_eq!(stale_temp_pid("lust-daemon-"), None);
        assert_eq!(stale_temp_pid("lust-daemon-12a"), None);
        assert_eq!(stale_temp_pid("lust-runtime-0123456789abcdef.o"), None);
        assert_eq!(stale_temp_pid("other-123"), None);
    }

    /// The startup sweep deletes dead-pid lust dirs and files, and keeps
    /// live-pid dirs and non-pid names.
    #[test]
    fn sweep_removes_dead_pid_dirs_and_keeps_live_ones() {
        let tmp = std::env::temp_dir();
        // A pid far above pid_max is never alive on Linux.
        let dead = 4_000_000_001u32;
        let dead_dir = tmp.join(format!("lust-daemon-{dead}"));
        let dead_cold = tmp.join(format!("lust-{dead}"));
        let dead_file = tmp.join(format!("lust-rustc-check-{dead}.rmeta"));
        let live_dir = tmp.join(format!("lust-daemon-{}", std::process::id()));
        let other_dir = tmp.join(format!("lust-daemon-glue-sweeptest{}", std::process::id()));
        for d in [&dead_dir, &dead_cold, &live_dir, &other_dir] {
            let _ = std::fs::remove_dir_all(d);
            std::fs::create_dir_all(d).unwrap();
            std::fs::write(d.join("x.o"), b"x").unwrap();
        }
        std::fs::write(&dead_file, b"x").unwrap();
        sweep_stale_temp_dirs();
        assert!(!dead_dir.exists(), "dead daemon dir swept");
        assert!(!dead_cold.exists(), "dead cold dir swept");
        assert!(!dead_file.exists(), "dead rmeta file swept");
        assert!(live_dir.exists(), "own pid dir kept");
        assert!(other_dir.exists(), "non-pid name kept");
        let _ = std::fs::remove_dir_all(&live_dir);
        let _ = std::fs::remove_dir_all(&other_dir);
    }

    /// A replaced session's object dir is deleted at replacement time,
    /// not left until daemon exit.
    #[test]
    fn replace_session_deletes_the_old_obj_dir() {
        let base = std::env::temp_dir().join(format!("lust-replace-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        let key = SessionKey::synthetic(Path::new("/tmp/g/main.rs"), false);
        let mut sessions: HashMap<SessionKey, Entry> = HashMap::new();
        let entry = entry_for(&mut sessions, &base, &key);
        let old_dir = entry.session.obj_dir().to_path_buf();
        std::fs::create_dir_all(&old_dir).unwrap();
        std::fs::write(old_dir.join("u1.o"), b"x").unwrap();
        replace_session(entry, &key);
        assert_ne!(entry.session.obj_dir(), old_dir.as_path(), "session moved to a fresh dir");
        assert!(!old_dir.exists(), "old obj dir deleted");
        let _ = std::fs::remove_dir_all(&base);
    }
}
