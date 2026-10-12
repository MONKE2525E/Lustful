// Command-line parsing and the daemon wire protocol. Shared by the thin `lust` client and the
// `lust-core` compiler, so the client stays small and starts fast.
//
// Wire format. Request: one line of tab-separated fields:
//   cmd  file  out  json  timings  debug  emit_c
// Response: "<code> <stdout len> <stderr len>\n" followed by the two byte strings.
// Both binaries include this module and each uses only part of it.
#![allow(dead_code)]

use std::io::{BufRead, BufReader, Read, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Cmd {
    Check,
    Build,
}

pub struct Request {
    pub cmd: Cmd,
    pub file: PathBuf,
    pub out: PathBuf,
    pub json: bool,
    pub timings: bool,
    pub debug: bool,
    pub emit_c: Option<PathBuf>,
}

#[derive(Default)]
pub struct Response {
    pub stdout: String,
    pub stderr: String,
    pub code: i32,
}

pub enum Invocation {
    Daemon,
    /// `run` is a build, then the client runs the program with `args`.
    Compile {
        req: Request,
        run: bool,
        args: Vec<String>,
    },
}

pub const USAGE: &str =
    "usage: lust <check|build|run> <file.rs> [--json] [--timings] [-o out] [-g] [--emit-c prefix] [-- args]\n       lust daemon";

/// Parses the command line (without the program name). Paths become absolute.
pub fn parse_args(args: &[String]) -> Option<Invocation> {
    let mut it = args.iter();
    let cmd = it.next()?;
    if cmd == "daemon" {
        return Some(Invocation::Daemon);
    }
    if !["check", "build", "run"].contains(&cmd.as_str()) {
        return None;
    }
    let mut file = PathBuf::new();
    let (mut out, mut json, mut timings, mut debug, mut emit_c, mut run_args) = (None, false, false, false, None, Vec::new());
    while let Some(a) = it.next() {
        match a.as_str() {
            "--json" => json = true,
            "--timings" => timings = true,
            "-g" => debug = true,
            "-o" => out = Some(PathBuf::from(it.next()?)),
            "--emit-c" => emit_c = Some(PathBuf::from(it.next()?)),
            "--" => run_args = it.by_ref().cloned().collect(),
            _ if file.as_os_str().is_empty() => file = a.into(),
            _ => return None,
        }
    }
    if file.as_os_str().is_empty() {
        return None;
    }
    let abs = |p: &Path| std::path::absolute(p).unwrap_or_else(|_| p.to_path_buf());
    let out = out.unwrap_or_else(|| PathBuf::from(file.file_stem().unwrap_or_default()));
    let req = Request {
        cmd: if cmd == "check" { Cmd::Check } else { Cmd::Build },
        file: abs(&file),
        out: abs(&out),
        json,
        timings,
        debug,
        emit_c: emit_c.map(|p| abs(&p)),
    };
    Some(Invocation::Compile { req, run: cmd == "run", args: run_args })
}

/// The daemon socket for the current directory.
pub fn socket_path() -> PathBuf {
    std::env::var_os("LUST_DAEMON_SOCKET").map(PathBuf::from).unwrap_or_else(|| PathBuf::from(".lust-daemon.sock"))
}

pub fn encode(r: &Request) -> String {
    let b = |x: bool| if x { "1" } else { "0" };
    let cmd = if r.cmd == Cmd::Check { "check" } else { "build" };
    let emit = r.emit_c.as_ref().map(|p| p.display().to_string()).unwrap_or_default();
    format!("{cmd}\t{}\t{}\t{}\t{}\t{}\t{emit}\n", r.file.display(), r.out.display(), b(r.json), b(r.timings), b(r.debug))
}

pub fn decode(line: &str) -> Option<Request> {
    let f: Vec<&str> = line.trim_end_matches('\n').split('\t').collect();
    if f.len() != 7 {
        return None;
    }
    Some(Request {
        cmd: if f[0] == "check" { Cmd::Check } else { Cmd::Build },
        file: f[1].into(),
        out: f[2].into(),
        json: f[3] == "1",
        timings: f[4] == "1",
        debug: f[5] == "1",
        emit_c: if f[6].is_empty() { None } else { Some(f[6].into()) },
    })
}

pub fn write_response(w: &mut impl Write, r: &Response) -> std::io::Result<()> {
    write!(w, "{} {} {}\n{}{}", r.code, r.stdout.len(), r.stderr.len(), r.stdout, r.stderr)
}

/// Sends a request to a running daemon. None if no daemon answers.
pub fn request(sock: &Path, req: &Request) -> Option<Response> {
    let mut conn = UnixStream::connect(sock).ok()?;
    conn.write_all(encode(req).as_bytes()).ok()?;
    let mut reader = BufReader::new(conn);
    let mut head = String::new();
    reader.read_line(&mut head).ok()?;
    let nums: Vec<usize> = head.split_whitespace().filter_map(|x| x.parse().ok()).collect();
    if nums.len() != 3 {
        return None;
    }
    let mut out = vec![0; nums[1]];
    let mut err = vec![0; nums[2]];
    reader.read_exact(&mut out).ok()?;
    reader.read_exact(&mut err).ok()?;
    Some(Response {
        code: nums[0] as i32,
        stdout: String::from_utf8_lossy(&out).into_owned(),
        stderr: String::from_utf8_lossy(&err).into_owned(),
    })
}

/// Prints a response. For `run`, runs the program after a successful build. Never returns.
pub fn finish(resp: Response, run: bool, out: &Path, args: &[String]) -> ! {
    print!("{}", resp.stdout);
    eprint!("{}", resp.stderr);
    let _ = std::io::stdout().flush();
    if resp.code != 0 || !run {
        std::process::exit(resp.code);
    }
    let status = std::process::Command::new(out).args(args).status().expect("cannot run the program");
    std::process::exit(status.code().unwrap_or(134));
}
