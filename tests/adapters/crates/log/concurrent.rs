use log::{LevelFilter, Log, Metadata, Record};
use std::sync::atomic::{AtomicUsize, Ordering};
struct Counter;
static LOGGER: Counter = Counter;
static WINS: AtomicUsize = AtomicUsize::new(0);
static RECORDS: AtomicUsize = AtomicUsize::new(0);
impl Log for Counter {
    fn enabled(&self, _: &Metadata) -> bool { true }
    fn log(&self, record: &Record) {
        assert_eq!(record.args().to_string(), "thread");
        RECORDS.fetch_add(1, Ordering::Relaxed);
    }
    fn flush(&self) {}
}
fn main() {
    let mut handles = Vec::new();
    for _ in 0..8 {
        handles.push(std::thread::spawn(|| {
            if log::set_logger(&LOGGER).is_ok() { WINS.fetch_add(1, Ordering::Relaxed); }
        }));
    }
    for handle in handles { handle.join().unwrap(); }
    log::set_max_level(LevelFilter::Info);
    let mut handles = Vec::new();
    for _ in 0..8 {
        handles.push(std::thread::spawn(|| { log::info!("thread"); }));
    }
    for handle in handles { handle.join().unwrap(); }
    println!("{} {}", WINS.load(Ordering::Relaxed), RECORDS.load(Ordering::Relaxed));
}
