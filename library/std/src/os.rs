// `std::os` (W-SHIM; w-cinterop3): the Unix metadata
// extension trait. The values are the stat fields the fs
// module already reads, so each method returns exactly what
// std returns for the same file. Not here: the fd traits
// (`std::os::fd`, OwnedFd has no lust form yet), the Linux
// `st_*` spelling of this trait, and the other `*Ext` traits.
// The items this module does not define stay with the
// compiler's std compat handling (`std_platform_compat_path`
// in src/ty/lang.rs, fx-stdos): this partial module must not
// hide `std::os::unix::fs` items that resolved before it.

pub mod unix {
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
    }
}
