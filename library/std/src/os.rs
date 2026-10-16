// `std::os` (W-SHIM; w-cinterop3): the Unix metadata
// extension trait. The values are the stat fields the fs
// module already reads, so each method returns exactly what
// std returns for the same file. `fd` and `unix::ffi` are
// tf-adapters (F1). Not here: the Linux `st_*` spelling of
// MetadataExt, and the other `*Ext` traits.
// The items this module does not define stay with the
// compiler's std compat handling (`std_platform_compat_path`
// in src/ty/lang.rs, fx-stdos): this partial module must not
// hide `std::os::unix::fs` items that resolved before it.

/// `std::os::fd`: raw and owned Unix file descriptors, as std
/// defines them on Linux. `borrow_raw` and `from_raw_fd` are
/// `unsafe` in std; lust source cannot spell `unsafe fn`, so they
/// are safe fns here that only shipped crates may call: user code
/// that names one, or implements `FromRawFd`, rejects with L0404
/// (`UPSTREAM_UNSAFE_FNS` in src/check/platform.rs).
pub mod fd {
    use crate::fs::File;
    use crate::io;
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
        /// Borrows a raw fd. The caller promises the fd stays open
        /// for `'fd` (std marks this `unsafe`; see the module note).
        pub const fn borrow_raw(fd: RawFd) -> BorrowedFd<'fd> {
            BorrowedFd { fd, marker: &UNIT }
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
        /// A duplicate of this fd (`F_DUPFD_CLOEXEC`, as std).
        pub fn try_clone(&self) -> io::Result<OwnedFd> {
            let n = core::intrinsics::sys_fd_dup(self.fd);
            if n < 0 {
                Err(io::Error::from_raw_os_error(-n))
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

    /// A trait to extract a raw file descriptor from an object.
    pub trait AsRawFd {
        /// Extracts the raw file descriptor.
        fn as_raw_fd(&self) -> RawFd;
    }

    /// A trait to convert an object into a raw file descriptor.
    pub trait IntoRawFd {
        /// Consumes `self`, returns its fd without closing it.
        fn into_raw_fd(self) -> RawFd;
    }

    /// A trait to build an object from a raw file descriptor.
    /// std marks this trait and fn `unsafe` (module note).
    pub trait FromRawFd {
        /// Takes ownership of `fd`.
        fn from_raw_fd(fd: RawFd) -> Self;
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

    impl AsFd for File {
        fn as_fd(&self) -> BorrowedFd<'_> {
            BorrowedFd { fd: self.__raw_fd(), marker: &UNIT }
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

    impl AsRawFd for File {
        fn as_raw_fd(&self) -> RawFd {
            self.__raw_fd()
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

    impl IntoRawFd for OwnedFd {
        fn into_raw_fd(self) -> RawFd {
            let fd = self.fd;
            core::mem::forget(self);
            fd
        }
    }

    impl IntoRawFd for File {
        fn into_raw_fd(self) -> RawFd {
            self.__into_raw_fd()
        }
    }

    impl FromRawFd for OwnedFd {
        fn from_raw_fd(fd: RawFd) -> OwnedFd {
            OwnedFd { fd }
        }
    }

    impl FromRawFd for File {
        fn from_raw_fd(fd: RawFd) -> File {
            File::__from_raw_fd(fd)
        }
    }

    impl From<File> for OwnedFd {
        fn from(file: File) -> OwnedFd {
            OwnedFd { fd: file.__into_raw_fd() }
        }
    }

    impl From<OwnedFd> for File {
        fn from(fd: OwnedFd) -> File {
            File::__from_raw_fd(fd.into_raw_fd())
        }
    }

    // The std streams: fds 0, 1, 2 by definition, as in std.
    impl AsFd for io::Stdin {
        fn as_fd(&self) -> BorrowedFd<'_> {
            BorrowedFd { fd: 0, marker: &UNIT }
        }
    }

    impl AsFd for io::Stdout {
        fn as_fd(&self) -> BorrowedFd<'_> {
            BorrowedFd { fd: 1, marker: &UNIT }
        }
    }

    impl AsFd for io::Stderr {
        fn as_fd(&self) -> BorrowedFd<'_> {
            BorrowedFd { fd: 2, marker: &UNIT }
        }
    }

    impl AsRawFd for io::Stdin {
        fn as_raw_fd(&self) -> RawFd {
            0
        }
    }

    impl AsRawFd for io::Stdout {
        fn as_raw_fd(&self) -> RawFd {
            1
        }
    }

    impl AsRawFd for io::Stderr {
        fn as_raw_fd(&self) -> RawFd {
            2
        }
    }
}

pub mod unix {
    /// Unix-specific extensions to `std::ffi`: `OsStr` and
    /// `OsString` as raw bytes.
    pub mod ffi {
        use crate::ffi::{os_str_from_bytes, OsStr, OsString};

        /// Unix-specific extensions to `OsStr`.
        pub trait OsStrExt {
            /// The `OsStr` of the raw bytes, as given.
            fn from_bytes(slice: &[u8]) -> &OsStr;
            /// The raw bytes of this string.
            fn as_bytes(&self) -> &[u8];
        }

        impl OsStrExt for OsStr {
            fn from_bytes(slice: &[u8]) -> &OsStr {
                os_str_from_bytes(slice)
            }
            fn as_bytes(&self) -> &[u8] {
                self.as_encoded_bytes()
            }
        }

        /// Unix-specific extensions to `OsString`.
        pub trait OsStringExt {
            /// The `OsString` of the raw bytes, as given.
            fn from_vec(vec: Vec<u8>) -> OsString;
            /// The raw bytes of this string.
            fn into_vec(self) -> Vec<u8>;
        }

        impl OsStringExt for OsString {
            fn from_vec(vec: Vec<u8>) -> OsString {
                OsString::__from_vec(vec)
            }
            fn into_vec(self) -> Vec<u8> {
                self.into_encoded_bytes()
            }
        }
    }

    /// The `std::os::unix::io` spelling of `std::os::fd`.
    pub mod io {
        pub use crate::os::fd::{AsFd, AsRawFd, BorrowedFd, FromRawFd, IntoRawFd, OwnedFd, RawFd};
    }

    /// Operating-system specific extensions.
    pub mod fs {
        use crate::fs::Metadata;

        /// Unix-specific extensions to `fs::Metadata`: the raw
        /// stat fields, as std exposes them.
        pub trait MetadataExt {
            /// The device number (`st_dev`).
            fn dev(&self) -> u64;
            /// The inode number (`st_ino`).
            fn ino(&self) -> u64;
            /// The file mode bits (`st_mode`).
            fn mode(&self) -> u32;
            /// The hard link count (`st_nlink`).
            fn nlink(&self) -> u64;
            /// The owner's user id (`st_uid`).
            fn uid(&self) -> u32;
            /// The owner's group id (`st_gid`).
            fn gid(&self) -> u32;
            /// The device number for special files (`st_rdev`).
            fn rdev(&self) -> u64;
            /// The size in bytes (`st_size`).
            fn size(&self) -> u64;
            /// Last access time, seconds since the epoch.
            fn atime(&self) -> i64;
            /// Last access time, the nanoseconds part.
            fn atime_nsec(&self) -> i64;
            /// Last modification time, seconds since the epoch.
            fn mtime(&self) -> i64;
            /// Last modification time, the nanoseconds part.
            fn mtime_nsec(&self) -> i64;
            /// Last status change time, seconds since the epoch.
            fn ctime(&self) -> i64;
            /// Last status change time, the nanoseconds part.
            fn ctime_nsec(&self) -> i64;
            /// The preferred block size for file system I/O.
            fn blksize(&self) -> u64;
            /// The number of 512-byte blocks allocated.
            fn blocks(&self) -> u64;
        }

        impl MetadataExt for Metadata {
            fn dev(&self) -> u64 {
                self.dev
            }
            fn ino(&self) -> u64 {
                self.ino
            }
            fn mode(&self) -> u32 {
                self.mode as u32
            }
            fn nlink(&self) -> u64 {
                self.nlink
            }
            fn uid(&self) -> u32 {
                self.uid
            }
            fn gid(&self) -> u32 {
                self.gid
            }
            fn rdev(&self) -> u64 {
                self.rdev
            }
            fn size(&self) -> u64 {
                self.len()
            }
            fn atime(&self) -> i64 {
                self.atime
            }
            fn atime_nsec(&self) -> i64 {
                self.atime_nsec
            }
            fn mtime(&self) -> i64 {
                self.mtime
            }
            fn mtime_nsec(&self) -> i64 {
                self.mtime_nsec
            }
            fn ctime(&self) -> i64 {
                self.ctime
            }
            fn ctime_nsec(&self) -> i64 {
                self.ctime_nsec
            }
            fn blksize(&self) -> u64 {
                self.blksize
            }
            fn blocks(&self) -> u64 {
                self.blocks
            }
        }

        /// Creates a symbolic link pointing at `original`
        /// (`symlink(2)`), as std's `os::unix::fs::symlink` does.
        pub fn symlink<P: AsRef<crate::path::Path>, Q: AsRef<crate::path::Path>>(
            original: P,
            link: Q,
        ) -> crate::io::Result<()> {
            let a = original.as_ref().as_os_str().as_encoded_bytes();
            let b = link.as_ref().as_os_str().as_encoded_bytes();
            crate::fs::status(core::intrinsics::sys_symlink(a, b))
        }
    }
}
