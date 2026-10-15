// `nix::errno`: the Errno type, as a code-carrying struct with
// upstream's variant names for the common codes. Display is
// upstream's form (`EPERM: Operation not permitted`); the text
// table covers the codes listed, and an unlisted code prints
// its io::Error text instead (README).

use core::fmt;

/// An error number.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Errno(i32);

impl Errno {
    pub const EPERM: Errno = Errno(1);
    pub const ENOENT: Errno = Errno(2);
    pub const ESRCH: Errno = Errno(3);
    pub const EINTR: Errno = Errno(4);
    pub const EIO: Errno = Errno(5);
    pub const ENXIO: Errno = Errno(6);
    pub const E2BIG: Errno = Errno(7);
    pub const ENOEXEC: Errno = Errno(8);
    pub const EBADF: Errno = Errno(9);
    pub const ECHILD: Errno = Errno(10);
    pub const EAGAIN: Errno = Errno(11);
    pub const ENOMEM: Errno = Errno(12);
    pub const EACCES: Errno = Errno(13);
    pub const EFAULT: Errno = Errno(14);
    pub const EBUSY: Errno = Errno(16);
    pub const EEXIST: Errno = Errno(17);
    pub const EXDEV: Errno = Errno(18);
    pub const ENODEV: Errno = Errno(19);
    pub const ENOTDIR: Errno = Errno(20);
    pub const EISDIR: Errno = Errno(21);
    pub const EINVAL: Errno = Errno(22);
    pub const ENFILE: Errno = Errno(23);
    pub const EMFILE: Errno = Errno(24);
    pub const ENOTTY: Errno = Errno(25);
    pub const EFBIG: Errno = Errno(27);
    pub const ENOSPC: Errno = Errno(28);
    pub const ESPIPE: Errno = Errno(29);
    pub const EROFS: Errno = Errno(30);
    pub const EMLINK: Errno = Errno(31);
    pub const EPIPE: Errno = Errno(32);
    pub const ERANGE: Errno = Errno(34);
    pub const ENAMETOOLONG: Errno = Errno(36);
    pub const ENOSYS: Errno = Errno(38);
    pub const ENOTEMPTY: Errno = Errno(39);
    pub const ELOOP: Errno = Errno(40);

    /// The Errno from a raw error number.
    pub fn from_raw(code: i32) -> Errno {
        Errno(code)
    }

    /// The result form of a raw return value: `Ok` for a value
    /// that is not -1, else the current errno is the caller's
    /// job here (the adapter's shims already return it).
    pub fn result<T>(value: T) -> crate::Result<T> {
        Ok(value)
    }

    /// The strerror text of this code, for the listed codes.
    pub fn desc(self) -> &'static str {
        match self.0 {
            1 => "Operation not permitted",
            2 => "No such file or directory",
            3 => "No such process",
            4 => "Interrupted system call",
            5 => "Input/output error",
            6 => "No such device or address",
            7 => "Argument list too long",
            8 => "Exec format error",
            9 => "Bad file descriptor",
            10 => "No child processes",
            11 => "Resource temporarily unavailable",
            12 => "Cannot allocate memory",
            13 => "Permission denied",
            14 => "Bad address",
            16 => "Device or resource busy",
            17 => "File exists",
            18 => "Invalid cross-device link",
            19 => "No such device",
            20 => "Not a directory",
            21 => "Is a directory",
            22 => "Invalid argument",
            23 => "Too many open files in system",
            24 => "Too many open files",
            25 => "Inappropriate ioctl for device",
            27 => "File too large",
            28 => "No space left on device",
            29 => "Illegal seek",
            30 => "Read-only file system",
            31 => "Too many links",
            32 => "Broken pipe",
            34 => "Numerical result out of range",
            36 => "File name too long",
            38 => "Function not implemented",
            39 => "Directory not empty",
            40 => "Too many levels of symbolic links",
            _ => "Unknown error",
        }
    }

    /// The variant name of this code, for Debug.
    fn name(self) -> &'static str {
        match self.0 {
            1 => "EPERM",
            2 => "ENOENT",
            3 => "ESRCH",
            4 => "EINTR",
            5 => "EIO",
            6 => "ENXIO",
            7 => "E2BIG",
            8 => "ENOEXEC",
            9 => "EBADF",
            10 => "ECHILD",
            11 => "EAGAIN",
            12 => "ENOMEM",
            13 => "EACCES",
            14 => "EFAULT",
            16 => "EBUSY",
            17 => "EEXIST",
            18 => "EXDEV",
            19 => "ENODEV",
            20 => "ENOTDIR",
            21 => "EISDIR",
            22 => "EINVAL",
            23 => "ENFILE",
            24 => "EMFILE",
            25 => "ENOTTY",
            27 => "EFBIG",
            28 => "ENOSPC",
            29 => "ESPIPE",
            30 => "EROFS",
            31 => "EMLINK",
            32 => "EPIPE",
            34 => "ERANGE",
            36 => "ENAMETOOLONG",
            38 => "ENOSYS",
            39 => "ENOTEMPTY",
            40 => "ELOOP",
            _ => "UnknownErrno",
        }
    }
}

impl fmt::Debug for Errno {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

impl fmt::Display for Errno {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name(), self.desc())
    }
}

impl From<Errno> for std::io::Error {
    fn from(err: Errno) -> std::io::Error {
        std::io::Error::from_raw_os_error(err.0)
    }
}
