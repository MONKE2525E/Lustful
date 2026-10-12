// `lust daemon`: keeps a warm compile session per file and serves requests from the `lust` client
// over a Unix socket (see protocol.rs). One request at a time.
use crate::driver::{self, Session};
use crate::protocol::{self, Response};
use std::collections::HashMap;
use std::io::{BufRead, BufReader};
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};

/// Serves requests until killed. Each file has its own session.
pub fn serve(sock: &Path) -> ! {
    let _ = std::fs::remove_file(sock);
    let listener = UnixListener::bind(sock).unwrap_or_else(|e| {
        eprintln!("error: cannot bind {}: {e}", sock.display());
        std::process::exit(2);
    });
    eprintln!("lust daemon: listening on {}", sock.display());
    let base = std::env::temp_dir().join(format!("lust-daemon-{}", std::process::id()));
    let mut sessions: HashMap<PathBuf, Session> = HashMap::new();
    for conn in listener.incoming() {
        let Ok(mut conn) = conn else { continue };
        let mut line = String::new();
        if BufReader::new(&conn).read_line(&mut line).is_err() {
            continue;
        }
        let resp = match protocol::decode(&line) {
            Some(req) => {
                let n = sessions.len();
                let session = sessions.entry(req.file.clone()).or_insert_with(|| Session::new(base.join(n.to_string()), true));
                driver::compile(&req, session)
            }
            None => Response { stderr: "error: bad request\n".into(), code: 2, ..Default::default() },
        };
        let _ = protocol::write_response(&mut conn, &resp);
    }
    std::process::exit(0);
}
