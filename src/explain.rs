// `lust explain L####`: long-form help for one diagnostic code.
//
// The text lives in docs/errors/, one Markdown file per code, and is built into the
// binary with `include_str!`. Each file has a wrong example that must fail with that
// code and a fixed example that must pass; scripts/check-explain.sh checks both against
// lust and rustc, and also checks that every code the compiler emits has a file here.
/// All error docs, in code order.
const DOCS: &[(&str, &str)] = &[
    ("L0001", include_str!("../docs/errors/L0001.md")),
    ("L0101", include_str!("../docs/errors/L0101.md")),
    ("L0102", include_str!("../docs/errors/L0102.md")),
    ("L0103", include_str!("../docs/errors/L0103.md")),
    ("L0104", include_str!("../docs/errors/L0104.md")),
    ("L0105", include_str!("../docs/errors/L0105.md")),
    ("L0106", include_str!("../docs/errors/L0106.md")),
    ("L0107", include_str!("../docs/errors/L0107.md")),
    ("L0110", include_str!("../docs/errors/L0110.md")),
    ("L0111", include_str!("../docs/errors/L0111.md")),
    ("L0112", include_str!("../docs/errors/L0112.md")),
    ("L0113", include_str!("../docs/errors/L0113.md")),
    ("L0114", include_str!("../docs/errors/L0114.md")),
    ("L0115", include_str!("../docs/errors/L0115.md")),
    ("L0116", include_str!("../docs/errors/L0116.md")),
    ("L0117", include_str!("../docs/errors/L0117.md")),
    ("L0118", include_str!("../docs/errors/L0118.md")),
    ("L0120", include_str!("../docs/errors/L0120.md")),
    ("L0121", include_str!("../docs/errors/L0121.md")),
    ("L0122", include_str!("../docs/errors/L0122.md")),
    ("L0130", include_str!("../docs/errors/L0130.md")),
    ("L0201", include_str!("../docs/errors/L0201.md")),
    ("L0202", include_str!("../docs/errors/L0202.md")),
    ("L0203", include_str!("../docs/errors/L0203.md")),
    ("L0301", include_str!("../docs/errors/L0301.md")),
    ("L0302", include_str!("../docs/errors/L0302.md")),
    ("L0303", include_str!("../docs/errors/L0303.md")),
    ("L0304", include_str!("../docs/errors/L0304.md")),
    ("L0305", include_str!("../docs/errors/L0305.md")),
    ("L0306", include_str!("../docs/errors/L0306.md")),
    ("L0307", include_str!("../docs/errors/L0307.md")),
    ("L0308", include_str!("../docs/errors/L0308.md")),
    ("L0309", include_str!("../docs/errors/L0309.md")),
    ("L0310", include_str!("../docs/errors/L0310.md")),
    ("L0311", include_str!("../docs/errors/L0311.md")),
    ("L0312", include_str!("../docs/errors/L0312.md")),
    ("L0401", include_str!("../docs/errors/L0401.md")),
    ("L0402", include_str!("../docs/errors/L0402.md")),
    ("L0403", include_str!("../docs/errors/L0403.md")),
    ("L0404", include_str!("../docs/errors/L0404.md")),
    ("L0405", include_str!("../docs/errors/L0405.md")),
    ("L9001", include_str!("../docs/errors/L9001.md")),
];

/// The title of a doc: its first line, without the leading `# `.
fn title(doc: &str) -> &str {
    doc.lines().next().unwrap_or("").trim_start_matches("# ")
}

/// Entry point for `lust explain`. Returns the process exit code.
pub fn run(args: &[String]) -> i32 {
    match args {
        [] => {
            println!("usage: lust explain <L####>");
            println!("codes:");
            for (_, doc) in DOCS {
                println!("  {}", title(doc));
            }
            0
        }
        [arg] => {
            let want = arg.to_ascii_uppercase();
            match DOCS.iter().find(|(code, _)| *code == want) {
                Some((_, doc)) => {
                    print!("{doc}");
                    0
                }
                None => {
                    eprintln!("error: unknown error code `{arg}`");
                    eprintln!("run `lust explain` to list all codes");
                    2
                }
            }
        }
        _ => {
            eprintln!("usage: lust explain <L####>");
            2
        }
    }
}

/// Every documented code. Used by `lust capabilities`.
pub fn codes() -> Vec<(&'static str, String)> {
    DOCS.iter().map(|(code, doc)| (*code, title(doc).split(": ").nth(1).unwrap_or("").to_string())).collect()
}
