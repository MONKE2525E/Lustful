// `lust`: the thin command-line client. If a daemon serves this directory, it sends the request
// there (a warm, incremental compile). Otherwise it hands the command to `lust-core`, the compiler,
// and starts a daemon in the background so the next command is warm (autostart, below).
// It has no custom allocator and few dependencies, so it starts in about a millisecond.
//
//   lust check <file.rs> [--json] [--timings]     lust check <file.rs> --rustc (oracle)
//   lust build <file.rs> [-o <out>] [-g] [--emit-c <prefix>] [--timings]
//   lust build <file.rs> --release | --profile <name> [-o <out>]  (Cargo or rustc)
//   lust run   <file.rs> [-- <args>...]
//   lust daemon            serve warm, incremental compiles for this directory
//   lust port scan ...     gap report for a Rust crate (execs `lust-port`)
//
// Autostart: `LUST_NO_DAEMON=1` turns the daemon off entirely (no use, no start). The daemon detaches into its own session,
// logs to `daemon.log` in the cache dir, and exits after `LUST_DAEMON_IDLE` (default 30m).
#[path = "protocol.rs"]
mod protocol;

use protocol::Invocation;
use std::io::Write as _;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};

unsafe extern "C" {
    fn setsid() -> i32;
    fn kill(pid: i32, sig: i32) -> i32;
}

/// True when an env flag is set to a value other than "" or "0".
fn env_on(name: &str) -> bool {
    matches!(std::env::var(name), Ok(v) if !v.is_empty() && v != "0")
}

/// True when a process with this pid exists (signal 0 sends nothing).
fn pid_alive(pid: i32) -> bool {
    pid > 0 && unsafe { kill(pid, 0) } == 0
}

/// The pid written in a lock file, if it parses.
fn lock_pid(lock: &Path) -> Option<i32> {
    std::fs::read_to_string(lock).ok()?.trim().parse().ok()
}

/// Claims the right to start the daemon by creating the lock file. A lock whose pid is
/// dead is stale (a crashed starter or an exited daemon): remove it and try once more.
/// The daemon later replaces this file's pid with its own and holds an flock on it, so
/// a lock with a live pid always means "a daemon owns this socket".
fn claim_start(lock: &Path) -> bool {
    for _ in 0..2 {
        match std::fs::OpenOptions::new().write(true).create_new(true).open(lock) {
            Ok(mut f) => {
                let _ = write!(f, "{}", std::process::id());
                return true;
            }
            Err(_) => match lock_pid(lock) {
                Some(pid) if pid_alive(pid) => return false,
                _ => {
                    // The starter may sit between create and write. Wait a moment, then
                    // re-read: a live starter's pid appears; a dead one's lock is stale.
                    std::thread::sleep(std::time::Duration::from_millis(50));
                    if lock_pid(lock).is_some_and(pid_alive) {
                        return false;
                    }
                    let _ = std::fs::remove_file(lock);
                }
            },
        }
    }
    false
}

/// The cache dir for daemon logs. The same rule as the disk cache (src/driver/cache.rs).
fn log_dir(file: &Path) -> PathBuf {
    match std::env::var_os("LUST_CACHE_DIR") {
        Some(d) if !d.is_empty() => PathBuf::from(d),
        _ => file.parent().map_or_else(|| PathBuf::from("."), Path::to_path_buf).join(".lust-cache"),
    }
}

/// Starts `lust-core daemon` detached (its own session, output to the log file), unless
/// autostart is off or another client or daemon already claims this socket. The current
/// command is still answered cold by the caller; the next one finds the daemon warm.
fn maybe_autostart(sock: &Path, file: &Path, core: &Path) {
    if env_on("LUST_NO_DAEMON") {
        return;
    }
    let lock = protocol::daemon_lock_path(sock);
    if !claim_start(&lock) {
        return;
    }
    let dir = log_dir(file);
    let _ = std::fs::create_dir_all(&dir);
    let log = std::fs::OpenOptions::new().create(true).append(true).open(dir.join("daemon.log"));
    let mut cmd = std::process::Command::new(core);
    // The daemon pre-warms a session for this file, so the next command is warm. It
    // waits for this process to exit first (exec keeps the pid, so that is the cold
    // compile), so the pre-warm never competes with the command in front of it.
    cmd.arg("daemon")
        .env("LUST_DAEMON_PREWARM", file)
        .env("LUST_DAEMON_PREWARM_AFTER", std::process::id().to_string())
        .stdin(std::process::Stdio::null());
    if let Ok(f) = log {
        if let Ok(f2) = f.try_clone() {
            cmd.stdout(f).stderr(f2);
        }
    }
    // SAFETY: pre_exec runs after fork, before exec. setsid gives the daemon its own
    // session, so it outlives this client and its terminal. It calls no Rust code.
    unsafe {
        cmd.pre_exec(|| {
            setsid();
            Ok(())
        });
    }
    match cmd.spawn() {
        Ok(_child) => {} // Not waited on: the daemon is reparented and serves in the background.
        Err(e) => {
            let _ = std::fs::remove_file(&lock);
            eprintln!("note: could not start a background daemon: {e}");
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    // `lust port scan ...` runs the standalone `lust-port` binary
    // (tools/lust-port), found next to this executable like `lust-core`.
    if args.first().map(String::as_str) == Some("port") {
        let tool = std::env::current_exe().map(|p| p.with_file_name("lust-port")).unwrap_or_else(|_| "lust-port".into());
        let err = std::process::Command::new(&tool).args(&args[1..]).exec();
        eprintln!("error: cannot run {}: {err}", tool.display());
        std::process::exit(2);
    }
    let core = std::env::current_exe().map(|p| p.with_file_name("lust-core")).unwrap_or_else(|_| "lust-core".into());
    match protocol::parse_args(&args) {
        // Release builds and the rustc oracle run right here, streaming output.
        Some(Invocation::Release { file, out, profile, debug }) => protocol::run_release(&file, out.as_deref(), profile.as_deref(), debug),
        Some(Invocation::RustcCheck { file }) => protocol::run_rustc_check(&file),
        Some(Invocation::Compile { req, run, args: run_args }) => {
            let sock = protocol::socket_path();
            // LUST_NO_DAEMON means "do not use a daemon at all": neither
            // start one nor send work to a live one.
            if !env_on("LUST_NO_DAEMON")
                && let Some(resp) = protocol::request(&sock, &req)
            {
                protocol::finish(resp, run, &req.out, &run_args);
            }
            // No daemon answered: start one for the next command, answer this one cold.
            maybe_autostart(&sock, &req.file, &core);
            let err = std::process::Command::new(&core).args(&args).exec();
            eprintln!("error: cannot run {}: {err}", core.display());
            std::process::exit(2);
        }
        // A daemon command or bad arguments: let the compiler handle it.
        _ => {
            let err = std::process::Command::new(&core).args(&args).exec();
            eprintln!("error: cannot run {}: {err}", core.display());
            std::process::exit(2);
        }
    }
}
