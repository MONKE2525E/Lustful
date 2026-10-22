//! Lust's source adapter for log 0.4.34 (std + alloc, no key/value features).
use std::cmp::Ordering as CmpOrdering;
use std::fmt;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Level { Error = 1, Warn, Info, Debug, Trace }
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum LevelFilter { Off, Error, Warn, Info, Debug, Trace }
impl Level {
    pub fn max() -> Self { Self::Trace }
    pub fn as_str(&self) -> &'static str {
        match self { Self::Error => "ERROR", Self::Warn => "WARN", Self::Info => "INFO", Self::Debug => "DEBUG", Self::Trace => "TRACE" }
    }
    pub fn to_level_filter(&self) -> LevelFilter {
        match self { Self::Error => LevelFilter::Error, Self::Warn => LevelFilter::Warn, Self::Info => LevelFilter::Info, Self::Debug => LevelFilter::Debug, Self::Trace => LevelFilter::Trace }
    }
}
impl LevelFilter {
    pub fn max() -> Self { Self::Trace }
    pub fn to_level(&self) -> Option<Level> {
        match self { Self::Off => None, Self::Error => Some(Level::Error), Self::Warn => Some(Level::Warn), Self::Info => Some(Level::Info), Self::Debug => Some(Level::Debug), Self::Trace => Some(Level::Trace) }
    }
    pub fn as_str(&self) -> &'static str {
        match self { Self::Off => "OFF", Self::Error => "ERROR", Self::Warn => "WARN", Self::Info => "INFO", Self::Debug => "DEBUG", Self::Trace => "TRACE" }
    }
}
impl PartialEq<LevelFilter> for Level {
    fn eq(&self, other: &LevelFilter) -> bool { (*self as usize) == (*other as usize) }
}
impl PartialOrd<LevelFilter> for Level {
    fn partial_cmp(&self, other: &LevelFilter) -> Option<CmpOrdering> { Some((*self as usize).cmp(&(*other as usize))) }
}
impl PartialEq<Level> for LevelFilter {
    fn eq(&self, other: &Level) -> bool { (*self as usize) == (*other as usize) }
}
impl PartialOrd<Level> for LevelFilter {
    fn partial_cmp(&self, other: &Level) -> Option<CmpOrdering> { Some((*self as usize).cmp(&(*other as usize))) }
}
impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.pad(self.as_str()) }
}
impl fmt::Display for LevelFilter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.pad(self.as_str()) }
}

#[derive(Clone, Debug)]
pub struct Metadata<'a> { level: Level, target: &'a str }
impl<'a> Metadata<'a> {
    pub fn builder() -> MetadataBuilder<'a> { MetadataBuilder::new() }
    pub fn level(&self) -> Level { self.level }
    pub fn target(&self) -> &'a str { self.target }
}
#[derive(Debug)]
pub struct MetadataBuilder<'a> { metadata: Metadata<'a> }
impl<'a> MetadataBuilder<'a> {
    pub fn new() -> Self { Self { metadata: Metadata { level: Level::Info, target: "" } } }
    pub fn level(&mut self, level: Level) -> &mut Self { self.metadata.level = level; self }
    pub fn target(&mut self, target: &'a str) -> &mut Self { self.metadata.target = target; self }
    pub fn build(&self) -> Metadata<'a> { self.metadata.clone() }
}
impl Default for MetadataBuilder<'_> {
    fn default() -> Self { Self::new() }
}

#[derive(Clone, Debug)]
enum SourceStr<'a> { Static(&'static str), Borrowed(&'a str) }
impl<'a> SourceStr<'a> {
    fn get(&self) -> &'a str { match self { Self::Static(s) => s, Self::Borrowed(s) => s } }
    fn as_static(&self) -> Option<&'static str> { match self { Self::Static(s) => Some(s), Self::Borrowed(_) => None } }
}
#[derive(Clone, Debug)]
pub struct Record<'a> {
    metadata: Metadata<'a>,
    args: fmt::Arguments<'a>,
    module_path: Option<SourceStr<'a>>,
    file: Option<SourceStr<'a>>,
    line: Option<u32>,
}
impl<'a> Record<'a> {
    pub fn builder() -> RecordBuilder<'a> { RecordBuilder::new() }
    pub fn args(&self) -> &fmt::Arguments<'a> { &self.args }
    pub fn metadata(&self) -> &Metadata<'a> { &self.metadata }
    pub fn level(&self) -> Level { self.metadata.level }
    pub fn target(&self) -> &'a str { self.metadata.target }
    pub fn module_path(&self) -> Option<&'a str> { self.module_path.as_ref().map(|s| s.get()) }
    pub fn module_path_static(&self) -> Option<&'static str> { self.module_path.as_ref().and_then(|s| s.as_static()) }
    pub fn file(&self) -> Option<&'a str> { self.file.as_ref().map(|s| s.get()) }
    pub fn file_static(&self) -> Option<&'static str> { self.file.as_ref().and_then(|s| s.as_static()) }
    pub fn line(&self) -> Option<u32> { self.line }
}
#[derive(Debug)]
pub struct RecordBuilder<'a> { record: Record<'a> }
impl<'a> RecordBuilder<'a> {
    pub fn new() -> Self {
        Self { record: Record { metadata: Metadata::builder().build(), args: format_args!(""), module_path: None, file: None, line: None } }
    }
    pub fn args(&mut self, args: fmt::Arguments<'a>) -> &mut Self { self.record.args = args; self }
    pub fn metadata(&mut self, metadata: Metadata<'a>) -> &mut Self { self.record.metadata = metadata; self }
    pub fn level(&mut self, level: Level) -> &mut Self { self.record.metadata.level = level; self }
    pub fn target(&mut self, target: &'a str) -> &mut Self { self.record.metadata.target = target; self }
    pub fn module_path(&mut self, path: Option<&'a str>) -> &mut Self { self.record.module_path = path.map(SourceStr::Borrowed); self }
    pub fn module_path_static(&mut self, path: Option<&'static str>) -> &mut Self { self.record.module_path = path.map(SourceStr::Static); self }
    pub fn file(&mut self, path: Option<&'a str>) -> &mut Self { self.record.file = path.map(SourceStr::Borrowed); self }
    pub fn file_static(&mut self, path: Option<&'static str>) -> &mut Self { self.record.file = path.map(SourceStr::Static); self }
    pub fn line(&mut self, line: Option<u32>) -> &mut Self { self.record.line = line; self }
    pub fn build(&self) -> Record<'a> { self.record.clone() }
}
impl Default for RecordBuilder<'_> {
    fn default() -> Self { Self::new() }
}

pub trait Log: Sync + Send {
    fn enabled(&self, metadata: &Metadata<'_>) -> bool;
    fn log(&self, record: &Record<'_>);
    fn flush(&self);
}
impl<T: Log + ?Sized> Log for &T {
    fn enabled(&self, metadata: &Metadata<'_>) -> bool { (**self).enabled(metadata) }
    fn log(&self, record: &Record<'_>) { (**self).log(record) }
    fn flush(&self) { (**self).flush() }
}
struct NopLogger;
impl Log for NopLogger {
    fn enabled(&self, _: &Metadata<'_>) -> bool { false }
    fn log(&self, _: &Record<'_>) {}
    fn flush(&self) {}
}
static NOP: NopLogger = NopLogger;
static LOGGER: OnceLock<&'static dyn Log> = OnceLock::new();
static FILTER: AtomicUsize = AtomicUsize::new(0);
#[derive(Debug, PartialEq, Eq)]
pub struct SetLoggerError(());
impl fmt::Display for SetLoggerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str("attempted to set a logger after the logging system was already initialized") }
}
#[cfg(feature = "std")]
impl std::error::Error for SetLoggerError {}
pub fn set_logger(logger: &'static dyn Log) -> Result<(), SetLoggerError> {
    LOGGER.set(logger).map_err(|_| SetLoggerError(()))
}
pub fn logger() -> &'static dyn Log { match LOGGER.get() { Some(logger) => *logger, None => &NOP } }
pub fn set_max_level(level: LevelFilter) { FILTER.store(level as usize, Ordering::Relaxed); }
pub fn max_level() -> LevelFilter {
    match FILTER.load(Ordering::Relaxed) { 0 => LevelFilter::Off, 1 => LevelFilter::Error, 2 => LevelFilter::Warn, 3 => LevelFilter::Info, 4 => LevelFilter::Debug, 5 => LevelFilter::Trace, _ => LevelFilter::Off }
}
pub const STATIC_MAX_LEVEL: LevelFilter = LevelFilter::Trace;

#[doc(hidden)]
pub fn __log<L: Log + ?Sized>(logger: &L, args: fmt::Arguments<'_>, level: Level, location: &(&str, &'static str, &'static str, u32)) {
    logger.log(&Record::builder().args(args).level(level).target(location.0)
        .module_path_static(Some(location.1)).file_static(Some(location.2)).line(Some(location.3)).build());
}
#[macro_export]
macro_rules! log {
    (logger: $logger:expr, target: $target:expr, $level:expr, $($args:tt)+) => {{
        let level = $level;
        if level <= $crate::STATIC_MAX_LEVEL && level <= $crate::max_level() {
            $crate::__log(&$logger, ::std::format_args!($($args)+), level, &($target, ::std::module_path!(), ::std::file!(), ::std::line!()));
        }
    }};
    (logger: $logger:expr, $level:expr, $($args:tt)+) => { $crate::log!(logger: $logger, target: ::std::module_path!(), $level, $($args)+) };
    (target: $target:expr, $level:expr, $($args:tt)+) => { $crate::log!(logger: $crate::logger(), target: $target, $level, $($args)+) };
    ($level:expr, $($args:tt)+) => { $crate::log!(target: ::std::module_path!(), $level, $($args)+) };
}

#[macro_export]
macro_rules! error {
    (logger: $logger:expr, target: $target:expr, $($args:tt)+) => { $crate::log!(logger: $logger, target: $target, $crate::Level::Error, $($args)+) };
    (logger: $logger:expr, $($args:tt)+) => { $crate::log!(logger: $logger, $crate::Level::Error, $($args)+) };
    (target: $target:expr, $($args:tt)+) => { $crate::log!(target: $target, $crate::Level::Error, $($args)+) };
    ($($args:tt)+) => { $crate::log!($crate::Level::Error, $($args)+) };
}

#[macro_export]
macro_rules! warn {
    (logger: $logger:expr, target: $target:expr, $($args:tt)+) => { $crate::log!(logger: $logger, target: $target, $crate::Level::Warn, $($args)+) };
    (logger: $logger:expr, $($args:tt)+) => { $crate::log!(logger: $logger, $crate::Level::Warn, $($args)+) };
    (target: $target:expr, $($args:tt)+) => { $crate::log!(target: $target, $crate::Level::Warn, $($args)+) };
    ($($args:tt)+) => { $crate::log!($crate::Level::Warn, $($args)+) };
}

#[macro_export]
macro_rules! info {
    (logger: $logger:expr, target: $target:expr, $($args:tt)+) => { $crate::log!(logger: $logger, target: $target, $crate::Level::Info, $($args)+) };
    (logger: $logger:expr, $($args:tt)+) => { $crate::log!(logger: $logger, $crate::Level::Info, $($args)+) };
    (target: $target:expr, $($args:tt)+) => { $crate::log!(target: $target, $crate::Level::Info, $($args)+) };
    ($($args:tt)+) => { $crate::log!($crate::Level::Info, $($args)+) };
}

#[macro_export]
macro_rules! debug {
    (logger: $logger:expr, target: $target:expr, $($args:tt)+) => { $crate::log!(logger: $logger, target: $target, $crate::Level::Debug, $($args)+) };
    (logger: $logger:expr, $($args:tt)+) => { $crate::log!(logger: $logger, $crate::Level::Debug, $($args)+) };
    (target: $target:expr, $($args:tt)+) => { $crate::log!(target: $target, $crate::Level::Debug, $($args)+) };
    ($($args:tt)+) => { $crate::log!($crate::Level::Debug, $($args)+) };
}

#[macro_export]
macro_rules! trace {
    (logger: $logger:expr, target: $target:expr, $($args:tt)+) => { $crate::log!(logger: $logger, target: $target, $crate::Level::Trace, $($args)+) };
    (logger: $logger:expr, $($args:tt)+) => { $crate::log!(logger: $logger, $crate::Level::Trace, $($args)+) };
    (target: $target:expr, $($args:tt)+) => { $crate::log!(target: $target, $crate::Level::Trace, $($args)+) };
    ($($args:tt)+) => { $crate::log!($crate::Level::Trace, $($args)+) };
}

#[macro_export]
macro_rules! log_enabled {
    (logger: $logger:expr, target: $target:expr, $level:expr) => {{
        let level = $level;
        level <= $crate::STATIC_MAX_LEVEL && level <= $crate::max_level()
            && $crate::Log::enabled(&$logger, &$crate::Metadata::builder().level(level).target($target).build())
    }};
    (logger: $logger:expr, $level:expr) => { $crate::log_enabled!(logger: $logger, target: ::std::module_path!(), $level) };
    (target: $target:expr, $level:expr) => { $crate::log_enabled!(logger: $crate::logger(), target: $target, $level) };
    ($level:expr) => { $crate::log_enabled!(target: ::std::module_path!(), $level) };
}

