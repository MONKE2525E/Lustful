use log::{Level, LevelFilter, Log, Metadata, Record};
use std::sync::atomic::{AtomicUsize, Ordering};

struct Capture;
static CAPTURE: Capture = Capture;
static EVALUATED: AtomicUsize = AtomicUsize::new(0);
static EXPECTED_LINE: AtomicUsize = AtomicUsize::new(0);
impl Log for Capture {
    fn enabled(&self, metadata: &Metadata) -> bool { metadata.target() != "disabled" }
    fn log(&self, record: &Record) {
        println!("{} {} {}", record.level(), record.target(), record.args());
        if record.target() == "location" {
            assert_eq!(record.module_path(), Some(module_path!()));
            assert_eq!(record.module_path_static(), Some(module_path!()));
            assert_eq!(record.file(), Some(file!()));
            assert_eq!(record.file_static(), Some(file!()));
            assert_eq!(record.line(), Some(EXPECTED_LINE.load(Ordering::Relaxed) as u32));
        }
    }
    fn flush(&self) { println!("flushed"); }
}
fn evaluated() -> usize { EVALUATED.fetch_add(1, Ordering::Relaxed) }
fn main() {
    assert_eq!(log::max_level(), LevelFilter::Off);
    log::warn!("off {}", evaluated());
    assert_eq!(EVALUATED.load(Ordering::Relaxed), 0);
    assert!(!log::log_enabled!(Level::Error));
    log::set_logger(&CAPTURE).unwrap();
    assert!(log::set_logger(&CAPTURE).is_err());
    log::set_max_level(LevelFilter::Info);
    log::error!(target: "explicit", "error {}", evaluated());
    log::warn!(target: "explicit", "warn");
    let name = "named";
    log::info!(target: "explicit", "capture {name}");
    log::debug!("hidden {}", evaluated());
    log::trace!("hidden {}", evaluated());
    assert_eq!(EVALUATED.load(Ordering::Relaxed), 1);
    assert!(log::log_enabled!(Level::Warn));
    assert!(!log::log_enabled!(target: "disabled", Level::Warn));
    assert!(!log::log_enabled!(Level::Trace));
    log::warn!(logger: CAPTURE, target: "custom", "custom");
    log::info!("default target");
    log::logger().flush();
    log::set_max_level(LevelFilter::Trace);
    log::debug!(target: "explicit", "debug");
    log::trace!(target: "explicit", "trace");
    EXPECTED_LINE.store((line!() + 1) as usize, Ordering::Relaxed);
    log::info!(target: "location", "source");
    let args = format_args!("builder");
    let record = Record::builder().args(args).level(Level::Warn).target("builder")
        .file(Some("dynamic")).module_path(Some("dynamic")).line(Some(7)).build();
    assert_eq!(record.file_static(), None);
    assert_eq!(record.module_path_static(), None);
    assert_eq!(record.line(), Some(7));
    CAPTURE.log(&record);
    let empty = Record::builder().build();
    assert_eq!(empty.level(), Level::Info);
    assert_eq!(empty.target(), "");
    assert_eq!(empty.args().to_string(), "");
    assert_eq!(empty.file(), None);
    assert!(Level::Warn <= LevelFilter::Info);
    assert!(LevelFilter::Off < Level::Error);
    println!("{:>7} {} {}", Level::Warn, LevelFilter::Off, Level::Debug.as_str());
    println!("{}", log::set_logger(&CAPTURE).unwrap_err());
}
