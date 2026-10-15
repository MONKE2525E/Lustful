// `rustix::fd`: fd handles of this adapter. Upstream these are
// std's `BorrowedFd` and `OwnedFd`; lust std has no way for an
// adapter to build those from a raw fd without `unsafe`, so the
// adapter's own types carry the same operations (README).

use crate::io::{Errno, Result};
use core::fmt;

/// A raw file descriptor number.
pub type RawFd = i32;

/// The unit value every BorrowedFd marker points at.
static UNIT: () = ();

/// A borrowed file descriptor.
#[derive(Copy, Clone)]
pub struct BorrowedFd<'fd> {
    fd: RawFd,
    marker: &'fd (),
}

impl<'fd> BorrowedFd<'fd> {
    /// Borrows a raw fd. Upstream this is `unsafe` (the caller
    /// promises the fd stays open); the adapter cannot spell
    /// `unsafe fn`, so the promise is the caller's unchecked
    /// word here too, as README.md lists.
    pub const fn borrow_raw(fd: RawFd) -> BorrowedFd<'fd> {
        BorrowedFd { fd, marker: &UNIT }
    }

    /// The raw fd number (also the `AsRawFd` impl's answer).
    pub fn as_raw_fd(&self) -> RawFd {
        self.fd
    }

    /// The fd of `AT_FDCWD` (the `CWD` constant's fd).
    pub(crate) const fn cwd() -> BorrowedFd<'static> {
        BorrowedFd { fd: -100, marker: &UNIT }
    }
}

impl fmt::Debug for BorrowedFd<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BorrowedFd").field("fd", &self.fd).finish()
    }
}

/// An owned file descriptor: closes on drop.
pub struct OwnedFd {
    fd: RawFd,
}

impl OwnedFd {
    /// Takes ownership of a raw fd the runtime just opened.
    pub(crate) fn from_raw(fd: RawFd) -> OwnedFd {
        OwnedFd { fd }
    }

    /// A duplicate of this fd (`F_DUPFD_CLOEXEC`, as std's
    /// `try_clone` of an OwnedFd).
    pub fn try_clone(&self) -> Result<OwnedFd> {
        let n = core::intrinsics::sys_fd_dup(self.fd);
        if n < 0 {
            Err(Errno::from_raw_os_error(-n))
        } else {
            Ok(OwnedFd { fd: n })
        }
    }
}

impl Drop for OwnedFd {
    fn drop(&mut self) {
        let _ = core::intrinsics::sys_fd_close(self.fd);
    }
}

impl fmt::Debug for OwnedFd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OwnedFd").field("fd", &self.fd).finish()
    }
}

/// A trait to borrow a file descriptor from an object.
pub trait AsFd {
    /// Borrows the file descriptor.
    fn as_fd(&self) -> BorrowedFd<'_>;
}

impl AsFd for BorrowedFd<'_> {
    fn as_fd(&self) -> BorrowedFd<'_> {
        *self
    }
}

impl AsFd for OwnedFd {
    fn as_fd(&self) -> BorrowedFd<'_> {
        BorrowedFd { fd: self.fd, marker: &UNIT }
    }
}

impl<T: AsFd + ?Sized> AsFd for &T {
    fn as_fd(&self) -> BorrowedFd<'_> {
        (**self).as_fd()
    }
}

impl<T: AsFd + ?Sized> AsFd for &mut T {
    fn as_fd(&self) -> BorrowedFd<'_> {
        (**self).as_fd()
    }
}

/// A trait to extract a raw file descriptor from an object.
pub trait AsRawFd {
    /// Extracts the raw file descriptor.
    fn as_raw_fd(&self) -> RawFd;
}

impl AsRawFd for BorrowedFd<'_> {
    fn as_raw_fd(&self) -> RawFd {
        self.fd
    }
}

impl AsRawFd for OwnedFd {
    fn as_raw_fd(&self) -> RawFd {
        self.fd
    }
}

impl<T: AsRawFd + ?Sized> AsRawFd for &T {
    fn as_raw_fd(&self) -> RawFd {
        (**self).as_raw_fd()
    }
}

impl<T: AsRawFd + ?Sized> AsRawFd for &mut T {
    fn as_raw_fd(&self) -> RawFd {
        (**self).as_raw_fd()
    }
}

/// A trait to convert an object into a raw file descriptor.
pub trait IntoRawFd {
    /// Consumes `self` and returns its raw fd without closing it.
    fn into_raw_fd(self) -> RawFd;
}

impl IntoRawFd for OwnedFd {
    fn into_raw_fd(self) -> RawFd {
        let fd = self.fd;
        core::mem::forget(self);
        fd
    }
}

// The std stream types ts-rust passes to rustix calls. Their
// fds are the constants 0, 1, and 2 by definition; lust std has
// no AsRawFd impl an adapter could read another type's fd
// through, so `File` and other std fd holders cannot be passed
// to this adapter's calls yet (README).
macro_rules! std_stream_as_fd {
    ($t:ty, $fd:expr) => {
        impl AsFd for $t {
            fn as_fd(&self) -> BorrowedFd<'_> {
                BorrowedFd { fd: $fd, marker: &UNIT }
            }
        }
    };
}

std_stream_as_fd!(std::io::Stdin, 0);
std_stream_as_fd!(std::io::Stdout, 1);
std_stream_as_fd!(std::io::Stderr, 2);
