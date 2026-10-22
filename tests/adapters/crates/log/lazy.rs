use log::{LevelFilter, Log, Metadata, Record};
use std::fmt;
use std::sync::atomic::{AtomicUsize, Ordering};
struct Tick;
static TICKS: AtomicUsize = AtomicUsize::new(0);
impl fmt::Display for Tick {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", TICKS.fetch_add(1, Ordering::Relaxed))
    }
}
struct Capture;
static LOGGER: Capture = Capture;
impl Log for Capture {
    fn enabled(&self, _: &Metadata) -> bool { panic!("log! must not call enabled") }
    fn log(&self, record: &Record) {
        println!("{}", record.args());
        println!("{}", record.args());
    }
    fn flush(&self) {}
}
fn main() {
    log::set_logger(&LOGGER).unwrap();
    log::info!("{}", Tick);
    assert_eq!(TICKS.load(Ordering::Relaxed), 0);
    log::set_max_level(LevelFilter::Info);
    log::info!("{}", Tick);
    assert_eq!(TICKS.load(Ordering::Relaxed), 2);
}
