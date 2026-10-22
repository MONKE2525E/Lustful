use log::{LevelFilter, Log, Metadata, Record};
macro_rules! format_args { ($($args:tt)*) => { compile_error!("caller macro must not be used by log") }; }
macro_rules! module_path { () => { "wrong" }; }
struct Capture;
static LOGGER: Capture = Capture;
impl Log for Capture {
    fn enabled(&self, _: &Metadata) -> bool { true }
    fn log(&self, record: &Record) {
        assert_eq!(record.target(), std::module_path!());
        println!("{}", record.args());
    }
    fn flush(&self) {}
}
fn main() {
    log::set_logger(&LOGGER).unwrap();
    log::set_max_level(LevelFilter::Info);
    let level = "caller";
    log::info!("capture {level}");
}
