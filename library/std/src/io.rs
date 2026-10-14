// `std::io` (W-SHIM): errors, the `Write` trait, and the standard
// output streams.
//
// Behavior follows rustc 1.99 std on Linux: `Error` Display and Debug
// texts per representation, the OS error kind table, `write_all`'s
// retry and `WriteZero` rules. The standard streams write through the
// runtime's C stdio streams, the same ones `print!` and `eprint!` use,
// so their output interleaves exactly as one std stream would.

use core::fmt;

/// `std::io::Result<T>`: a `Result` with `io::Error` as its error.
pub type Result<T> = core::result::Result<T, Error>;

/// The error type for I/O operations of `Read`, `Write`, and the
/// filesystem and process functions.
pub struct Error {
    repr: Repr,
}

/// How an `Error` was built. The variants match std's representations,
/// which decide the Display and Debug texts.
enum Repr {
    /// An OS error code (`from_raw_os_error`, failed syscalls).
    Os(i32),
    /// Only a kind (`From<ErrorKind>`).
    Simple(ErrorKind),
    /// A kind with a static message (errors std itself makes).
    SimpleMessage(ErrorKind, &'static str),
    /// A kind with a user payload (`Error::new`, `Error::other`). The
    /// payload is the text of a `&str` or `String`, the error types lust
    /// accepts here.
    Custom(ErrorKind, String),
}

/// The payloads `Error::new` and `Error::other` take in lust: `&str`
/// and `String` (std takes anything convertible into a boxed error).
/// Sealed in a private module: user code can neither name nor
/// implement it.
mod custom {
    pub trait IntoCustomError {
        fn into_custom_text(self) -> String;
    }

    impl IntoCustomError for &str {
        fn into_custom_text(self) -> String {
            String::from(self)
        }
    }

    impl IntoCustomError for String {
        fn into_custom_text(self) -> String {
            self
        }
    }
}

use custom::IntoCustomError;

impl Error {
    /// Creates an error from a kind and a payload error.
    pub fn new<E: IntoCustomError>(kind: ErrorKind, error: E) -> Error {
        Error { repr: Repr::Custom(kind, error.into_custom_text()) }
    }

    /// Creates an error of kind `Other` from a payload error.
    pub fn other<E: IntoCustomError>(error: E) -> Error {
        Error::new(ErrorKind::Other, error)
    }

    /// Creates an error from an OS error code.
    pub fn from_raw_os_error(code: i32) -> Error {
        Error { repr: Repr::Os(code) }
    }

    /// The OS error code, if this error came from the OS.
    pub fn raw_os_error(&self) -> Option<i32> {
        match self.repr {
            Repr::Os(code) => Some(code),
            _ => None,
        }
    }

    /// The general category of this error.
    pub fn kind(&self) -> ErrorKind {
        match self.repr {
            Repr::Os(code) => decode_error_kind(code),
            Repr::Simple(kind) => kind,
            Repr::SimpleMessage(kind, _) => kind,
            Repr::Custom(kind, _) => kind,
        }
    }

    /// An error with a static message, as std's `const_error!`.
    pub(crate) fn simple_message(kind: ErrorKind, message: &'static str) -> Error {
        Error { repr: Repr::SimpleMessage(kind, message) }
    }

    /// True for the kind `write_all` and `read_exact` retry on.
    pub(crate) fn is_interrupted(&self) -> bool {
        match self.repr {
            Repr::Os(code) => code == 4,
            Repr::Simple(kind) => kind == ErrorKind::Interrupted,
            Repr::SimpleMessage(kind, _) => kind == ErrorKind::Interrupted,
            Repr::Custom(kind, _) => kind == ErrorKind::Interrupted,
        }
    }
}

/// The OS text of an error code, as std's `error_string` (strerror).
fn os_error_text(code: i32) -> String {
    let mut text = String::new();
    core::intrinsics::sys_os_error_text(code, &mut text);
    text
}

impl From<ErrorKind> for Error {
    fn from(kind: ErrorKind) -> Error {
        Error { repr: Repr::Simple(kind) }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.repr {
            Repr::Os(code) => {
                let detail = os_error_text(*code);
                write!(f, "{} (os error {})", detail, code)
            }
            Repr::Simple(kind) => f.write_str(kind.as_str()),
            Repr::SimpleMessage(_, message) => f.write_str(message),
            Repr::Custom(_, text) => f.pad(text),
        }
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.repr {
            Repr::Os(code) => {
                let message = os_error_text(*code);
                f.debug_struct("Os").field("code", code).field("kind", &decode_error_kind(*code)).field("message", &message).finish()
            }
            Repr::Simple(kind) => f.debug_tuple("Kind").field(kind).finish(),
            Repr::SimpleMessage(kind, message) => f.debug_struct("Error").field("kind", kind).field("message", message).finish(),
            Repr::Custom(kind, text) => f.debug_struct("Custom").field("kind", kind).field("error", text).finish(),
        }
    }
}

/// A list specifying general categories of I/O error, in std's order
/// (the derived `Ord` and `Hash` read it). Variants std keeps unstable
/// carry a `__` prefix; their `Debug` text is std's name. std marks the
/// enum `#[non_exhaustive]`; the `__` variants give user matches the same
/// need for a wildcard arm.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ErrorKind {
    NotFound,
    PermissionDenied,
    ConnectionRefused,
    ConnectionReset,
    HostUnreachable,
    NetworkUnreachable,
    ConnectionAborted,
    NotConnected,
    AddrInUse,
    AddrNotAvailable,
    NetworkDown,
    BrokenPipe,
    AlreadyExists,
    WouldBlock,
    NotADirectory,
    IsADirectory,
    DirectoryNotEmpty,
    ReadOnlyFilesystem,
    __FilesystemLoop,
    StaleNetworkFileHandle,
    InvalidInput,
    InvalidData,
    TimedOut,
    WriteZero,
    StorageFull,
    NotSeekable,
    QuotaExceeded,
    FileTooLarge,
    ResourceBusy,
    ExecutableFileBusy,
    Deadlock,
    CrossesDevices,
    TooManyLinks,
    InvalidFilename,
    ArgumentListTooLong,
    Interrupted,
    Unsupported,
    UnexpectedEof,
    OutOfMemory,
    __InProgress,
    __TooManyOpenFiles,
    __InputOutputError,
    Other,
    __Uncategorized,
}

impl ErrorKind {
    /// The short description std's `Display` prints.
    fn as_str(&self) -> &'static str {
        match *self {
            ErrorKind::NotFound => "entity not found",
            ErrorKind::PermissionDenied => "permission denied",
            ErrorKind::ConnectionRefused => "connection refused",
            ErrorKind::ConnectionReset => "connection reset",
            ErrorKind::HostUnreachable => "host unreachable",
            ErrorKind::NetworkUnreachable => "network unreachable",
            ErrorKind::ConnectionAborted => "connection aborted",
            ErrorKind::NotConnected => "not connected",
            ErrorKind::AddrInUse => "address in use",
            ErrorKind::AddrNotAvailable => "address not available",
            ErrorKind::NetworkDown => "network down",
            ErrorKind::BrokenPipe => "broken pipe",
            ErrorKind::AlreadyExists => "entity already exists",
            ErrorKind::WouldBlock => "operation would block",
            ErrorKind::NotADirectory => "not a directory",
            ErrorKind::IsADirectory => "is a directory",
            ErrorKind::DirectoryNotEmpty => "directory not empty",
            ErrorKind::ReadOnlyFilesystem => "read-only filesystem or storage medium",
            ErrorKind::__FilesystemLoop => "filesystem loop or indirection limit (e.g. symlink loop)",
            ErrorKind::StaleNetworkFileHandle => "stale network file handle",
            ErrorKind::InvalidInput => "invalid input parameter",
            ErrorKind::InvalidData => "invalid data",
            ErrorKind::TimedOut => "timed out",
            ErrorKind::WriteZero => "write zero",
            ErrorKind::StorageFull => "no storage space",
            ErrorKind::NotSeekable => "seek on unseekable file",
            ErrorKind::QuotaExceeded => "quota exceeded",
            ErrorKind::FileTooLarge => "file too large",
            ErrorKind::ResourceBusy => "resource busy",
            ErrorKind::ExecutableFileBusy => "executable file busy",
            ErrorKind::Deadlock => "deadlock",
            ErrorKind::CrossesDevices => "cross-device link or rename",
            ErrorKind::TooManyLinks => "too many links",
            ErrorKind::InvalidFilename => "invalid filename",
            ErrorKind::ArgumentListTooLong => "argument list too long",
            ErrorKind::Interrupted => "operation interrupted",
            ErrorKind::Unsupported => "unsupported",
            ErrorKind::UnexpectedEof => "unexpected end of file",
            ErrorKind::OutOfMemory => "out of memory",
            ErrorKind::__InProgress => "in progress",
            ErrorKind::__TooManyOpenFiles => "too many open files",
            ErrorKind::__InputOutputError => "input/output error",
            ErrorKind::Other => "other error",
            ErrorKind::__Uncategorized => "uncategorized error",
        }
    }

    /// The variant name as std's derived `Debug` prints it.
    fn name(&self) -> &'static str {
        match *self {
            ErrorKind::NotFound => "NotFound",
            ErrorKind::PermissionDenied => "PermissionDenied",
            ErrorKind::ConnectionRefused => "ConnectionRefused",
            ErrorKind::ConnectionReset => "ConnectionReset",
            ErrorKind::HostUnreachable => "HostUnreachable",
            ErrorKind::NetworkUnreachable => "NetworkUnreachable",
            ErrorKind::ConnectionAborted => "ConnectionAborted",
            ErrorKind::NotConnected => "NotConnected",
            ErrorKind::AddrInUse => "AddrInUse",
            ErrorKind::AddrNotAvailable => "AddrNotAvailable",
            ErrorKind::NetworkDown => "NetworkDown",
            ErrorKind::BrokenPipe => "BrokenPipe",
            ErrorKind::AlreadyExists => "AlreadyExists",
            ErrorKind::WouldBlock => "WouldBlock",
            ErrorKind::NotADirectory => "NotADirectory",
            ErrorKind::IsADirectory => "IsADirectory",
            ErrorKind::DirectoryNotEmpty => "DirectoryNotEmpty",
            ErrorKind::ReadOnlyFilesystem => "ReadOnlyFilesystem",
            ErrorKind::__FilesystemLoop => "FilesystemLoop",
            ErrorKind::StaleNetworkFileHandle => "StaleNetworkFileHandle",
            ErrorKind::InvalidInput => "InvalidInput",
            ErrorKind::InvalidData => "InvalidData",
            ErrorKind::TimedOut => "TimedOut",
            ErrorKind::WriteZero => "WriteZero",
            ErrorKind::StorageFull => "StorageFull",
            ErrorKind::NotSeekable => "NotSeekable",
            ErrorKind::QuotaExceeded => "QuotaExceeded",
            ErrorKind::FileTooLarge => "FileTooLarge",
            ErrorKind::ResourceBusy => "ResourceBusy",
            ErrorKind::ExecutableFileBusy => "ExecutableFileBusy",
            ErrorKind::Deadlock => "Deadlock",
            ErrorKind::CrossesDevices => "CrossesDevices",
            ErrorKind::TooManyLinks => "TooManyLinks",
            ErrorKind::InvalidFilename => "InvalidFilename",
            ErrorKind::ArgumentListTooLong => "ArgumentListTooLong",
            ErrorKind::Interrupted => "Interrupted",
            ErrorKind::Unsupported => "Unsupported",
            ErrorKind::UnexpectedEof => "UnexpectedEof",
            ErrorKind::OutOfMemory => "OutOfMemory",
            ErrorKind::__InProgress => "InProgress",
            ErrorKind::__TooManyOpenFiles => "TooManyOpenFiles",
            ErrorKind::__InputOutputError => "InputOutputError",
            ErrorKind::Other => "Other",
            ErrorKind::__Uncategorized => "Uncategorized",
        }
    }
}

/// The kind of an OS error code, as std's `decode_error_kind` on Linux.
fn decode_error_kind(code: i32) -> ErrorKind {
    match code {
        1 => ErrorKind::PermissionDenied,
        2 => ErrorKind::NotFound,
        4 => ErrorKind::Interrupted,
        5 => ErrorKind::__InputOutputError,
        7 => ErrorKind::ArgumentListTooLong,
        11 => ErrorKind::WouldBlock,
        12 => ErrorKind::OutOfMemory,
        13 => ErrorKind::PermissionDenied,
        16 => ErrorKind::ResourceBusy,
        17 => ErrorKind::AlreadyExists,
        18 => ErrorKind::CrossesDevices,
        20 => ErrorKind::NotADirectory,
        21 => ErrorKind::IsADirectory,
        22 => ErrorKind::InvalidInput,
        23 => ErrorKind::__TooManyOpenFiles,
        24 => ErrorKind::__TooManyOpenFiles,
        26 => ErrorKind::ExecutableFileBusy,
        27 => ErrorKind::FileTooLarge,
        28 => ErrorKind::StorageFull,
        29 => ErrorKind::NotSeekable,
        30 => ErrorKind::ReadOnlyFilesystem,
        31 => ErrorKind::TooManyLinks,
        32 => ErrorKind::BrokenPipe,
        35 => ErrorKind::Deadlock,
        36 => ErrorKind::InvalidFilename,
        38 => ErrorKind::Unsupported,
        39 => ErrorKind::DirectoryNotEmpty,
        40 => ErrorKind::__FilesystemLoop,
        95 => ErrorKind::Unsupported,
        98 => ErrorKind::AddrInUse,
        99 => ErrorKind::AddrNotAvailable,
        100 => ErrorKind::NetworkDown,
        101 => ErrorKind::NetworkUnreachable,
        103 => ErrorKind::ConnectionAborted,
        104 => ErrorKind::ConnectionReset,
        107 => ErrorKind::NotConnected,
        110 => ErrorKind::TimedOut,
        111 => ErrorKind::ConnectionRefused,
        113 => ErrorKind::HostUnreachable,
        115 => ErrorKind::__InProgress,
        116 => ErrorKind::StaleNetworkFileHandle,
        122 => ErrorKind::QuotaExceeded,
        _ => ErrorKind::__Uncategorized,
    }
}

impl fmt::Debug for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A trait for objects which are byte-oriented sinks.
pub trait Write {
    /// Writes a buffer into this writer, returning how many bytes were
    /// written.
    fn write(&mut self, buf: &[u8]) -> Result<usize>;

    /// Flushes this output stream.
    fn flush(&mut self) -> Result<()>;

    /// Writes an entire buffer, retrying on `Interrupted`; a write of
    /// zero bytes is a `WriteZero` error.
    fn write_all(&mut self, buf: &[u8]) -> Result<()> {
        let mut rest = buf;
        while !rest.is_empty() {
            match self.write(rest) {
                Ok(0) => return Err(Error::simple_message(ErrorKind::WriteZero, "failed to write whole buffer")),
                Ok(n) => rest = &rest[n..],
                Err(e) => {
                    if !e.is_interrupted() {
                        return Err(e);
                    }
                }
            }
        }
        Ok(())
    }

    /// Writes a formatted string into this writer (`write!` and
    /// `writeln!`). In lust a `fmt::Arguments` value already holds its
    /// text, so this is one `write_all`; for std's writers that is the
    /// same output as std's piece-by-piece writes. A user type that
    /// relies on this default is rejected when a build instantiates it
    /// (L0641), since std would call its `write` once per piece.
    fn write_fmt(&mut self, args: fmt::Arguments<'_>) -> Result<()> {
        let bytes = core::intrinsics::sys_fmt_arguments_bytes(args);
        self.write_all(&bytes)
    }

    /// Creates a "by reference" adapter for this writer.
    fn by_ref(&mut self) -> &mut Self
    where
        Self: Sized,
    {
        self
    }
}

impl Write for Vec<u8> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn write_all(&mut self, buf: &[u8]) -> Result<()> {
        self.extend_from_slice(buf);
        Ok(())
    }

    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}

impl<W: Write + ?Sized> Write for &mut W {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        (**self).write(buf)
    }

    fn flush(&mut self) -> Result<()> {
        (**self).flush()
    }

    fn write_all(&mut self, buf: &[u8]) -> Result<()> {
        (**self).write_all(buf)
    }

    fn write_fmt(&mut self, fmt: fmt::Arguments<'_>) -> Result<()> {
        (**self).write_fmt(fmt)
    }
}

/// Writes `buf` to the process's stdout (fd 1) or stderr (fd 2)
/// through the runtime's stdio stream.
fn write_std(fd: i32, buf: &[u8]) -> Result<usize> {
    let n = core::intrinsics::sys_write_std(fd, buf);
    if n < 0 { Err(Error::from_raw_os_error((-n) as i32)) } else { Ok(n as usize) }
}

/// Flushes the runtime's stdio stream for fd 1 or 2.
fn flush_std(fd: i32) -> Result<()> {
    let code = core::intrinsics::sys_flush_std(fd);
    if code != 0 { Err(Error::from_raw_os_error(code)) } else { Ok(()) }
}

/// The unit value the stream locks borrow for `'static`.
static UNIT: () = ();

/// A handle to the global standard output stream of the current
/// process.
pub struct Stdout {
    _priv: (),
}

/// A locked reference to the `Stdout` handle.
pub struct StdoutLock<'a> {
    _handle: &'a (),
}

/// Constructs a new handle to the standard output of the current
/// process.
pub fn stdout() -> Stdout {
    Stdout { _priv: () }
}

impl Stdout {
    /// Locks this handle to the standard output stream.
    pub fn lock(&self) -> StdoutLock<'static> {
        StdoutLock { _handle: &UNIT }
    }
}

impl fmt::Debug for Stdout {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Stdout").finish_non_exhaustive()
    }
}

impl fmt::Debug for StdoutLock<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("StdoutLock").finish_non_exhaustive()
    }
}

impl Write for Stdout {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        write_std(1, buf)
    }

    fn flush(&mut self) -> Result<()> {
        flush_std(1)
    }
}

impl Write for StdoutLock<'_> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        write_std(1, buf)
    }

    fn flush(&mut self) -> Result<()> {
        flush_std(1)
    }
}

/// A handle to the standard error stream of a process.
pub struct Stderr {
    _priv: (),
}

/// A locked reference to the `Stderr` handle.
pub struct StderrLock<'a> {
    _handle: &'a (),
}

/// Constructs a new handle to the standard error of the current
/// process.
pub fn stderr() -> Stderr {
    Stderr { _priv: () }
}

impl Stderr {
    /// Locks this handle to the standard error stream.
    pub fn lock(&self) -> StderrLock<'static> {
        StderrLock { _handle: &UNIT }
    }
}

impl fmt::Debug for Stderr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Stderr").finish_non_exhaustive()
    }
}

impl fmt::Debug for StderrLock<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("StderrLock").finish_non_exhaustive()
    }
}

impl Write for Stderr {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        write_std(2, buf)
    }

    fn flush(&mut self) -> Result<()> {
        flush_std(2)
    }
}

impl Write for StderrLock<'_> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        write_std(2, buf)
    }

    fn flush(&mut self) -> Result<()> {
        flush_std(2)
    }
}

/// A writer which will move data into the void.
pub struct Sink {
    _priv: (),
}

/// Creates an instance of a writer which will successfully consume all
/// data.
pub const fn sink() -> Sink {
    Sink { _priv: () }
}

impl fmt::Debug for Sink {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Sink")
    }
}

impl Write for Sink {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        Ok(buf.len())
    }

    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}
