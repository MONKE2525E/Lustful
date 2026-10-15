// `rustix::fs`: the flag types and the file calls ts-rust's
// core files use, over sysx. Flag Debug forms are the derived
// tuple forms, not upstream's name lists (README).

use crate::fd::{AsFd, BorrowedFd, OwnedFd};
use crate::io::{Errno, Result};
use crate::path::Arg;
use crate::{rec_i64, rec_u64};

/// `AT_FDCWD`: the current working directory as a dirfd.
pub const CWD: BorrowedFd<'static> = BorrowedFd::cwd();

/// The path bytes of `path`, or EINVAL for an interior NUL.
fn path_bytes<P: Arg>(path: &P) -> Result<Vec<u8>> {
    let bytes = path.as_path_bytes();
    if bytes.contains(&0) {
        return Err(Errno::INVAL);
    }
    Ok(bytes)
}

/// `OFlags` flags.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct OFlags(u32);

impl OFlags {
    pub const RDONLY: OFlags = OFlags(0);
    pub const WRONLY: OFlags = OFlags(1);
    pub const RDWR: OFlags = OFlags(2);
    pub const ACCMODE: OFlags = OFlags(3);
    pub const CREATE: OFlags = OFlags(0o100);
    pub const EXCL: OFlags = OFlags(0o200);
    pub const NOCTTY: OFlags = OFlags(0o400);
    pub const TRUNC: OFlags = OFlags(0o1000);
    pub const APPEND: OFlags = OFlags(0o2000);
    pub const NONBLOCK: OFlags = OFlags(0o4000);
    pub const DSYNC: OFlags = OFlags(0o10000);
    pub const SYNC: OFlags = OFlags(0o4010000);
    pub const DIRECTORY: OFlags = OFlags(0o200000);
    pub const NOFOLLOW: OFlags = OFlags(0o400000);
    pub const CLOEXEC: OFlags = OFlags(0o2000000);
    pub const PATH: OFlags = OFlags(0o10000000);

    /// No flags.
    pub const fn empty() -> OFlags { OFlags(0) }
    /// The raw bits.
    pub const fn bits(self) -> u32 { self.0 }
    /// Flags from raw bits, keeping unknown bits.
    pub const fn from_bits_retain(bits: u32) -> OFlags { OFlags(bits) }
    /// True when every bit of `other` is set in `self`.
    pub const fn contains(self, other: OFlags) -> bool { self.0 & other.0 == other.0 }
    /// True when no bit is set.
    pub const fn is_empty(self) -> bool { self.0 == 0 }
}

impl core::ops::BitOr for OFlags {
    type Output = OFlags;
    fn bitor(self, other: OFlags) -> OFlags { OFlags(self.0 | other.0) }
}

impl core::ops::BitOrAssign for OFlags {
    fn bitor_assign(&mut self, other: OFlags) { self.0 |= other.0; }
}

impl core::ops::BitAnd for OFlags {
    type Output = OFlags;
    fn bitand(self, other: OFlags) -> OFlags { OFlags(self.0 & other.0) }
}

/// `Mode` flags.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Mode(u32);

impl Mode {
    pub const IRWXU: Mode = Mode(0o700);
    pub const IRUSR: Mode = Mode(0o400);
    pub const IWUSR: Mode = Mode(0o200);
    pub const IXUSR: Mode = Mode(0o100);
    pub const IRWXG: Mode = Mode(0o070);
    pub const IRGRP: Mode = Mode(0o040);
    pub const IWGRP: Mode = Mode(0o020);
    pub const IXGRP: Mode = Mode(0o010);
    pub const IRWXO: Mode = Mode(0o007);
    pub const IROTH: Mode = Mode(0o004);
    pub const IWOTH: Mode = Mode(0o002);
    pub const IXOTH: Mode = Mode(0o001);
    pub const ISUID: Mode = Mode(0o4000);
    pub const ISGID: Mode = Mode(0o2000);
    pub const ISVTX: Mode = Mode(0o1000);

    /// No flags.
    pub const fn empty() -> Mode { Mode(0) }
    /// The raw bits.
    pub const fn bits(self) -> u32 { self.0 }
    /// Flags from raw bits, keeping unknown bits.
    pub const fn from_bits_retain(bits: u32) -> Mode { Mode(bits) }
    /// True when every bit of `other` is set in `self`.
    pub const fn contains(self, other: Mode) -> bool { self.0 & other.0 == other.0 }
    /// True when no bit is set.
    pub const fn is_empty(self) -> bool { self.0 == 0 }
}

impl core::ops::BitOr for Mode {
    type Output = Mode;
    fn bitor(self, other: Mode) -> Mode { Mode(self.0 | other.0) }
}

impl core::ops::BitOrAssign for Mode {
    fn bitor_assign(&mut self, other: Mode) { self.0 |= other.0; }
}

impl core::ops::BitAnd for Mode {
    type Output = Mode;
    fn bitand(self, other: Mode) -> Mode { Mode(self.0 & other.0) }
}

/// `AtFlags` flags.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct AtFlags(i32);

impl AtFlags {
    pub const SYMLINK_NOFOLLOW: AtFlags = AtFlags(0x100);
    pub const EACCESS: AtFlags = AtFlags(0x200);
    pub const REMOVEDIR: AtFlags = AtFlags(0x200);
    pub const SYMLINK_FOLLOW: AtFlags = AtFlags(0x400);
    pub const NO_AUTOMOUNT: AtFlags = AtFlags(0x800);
    pub const EMPTY_PATH: AtFlags = AtFlags(0x1000);
    pub const STATX_FORCE_SYNC: AtFlags = AtFlags(0x2000);
    pub const STATX_DONT_SYNC: AtFlags = AtFlags(0x4000);
    pub const STATX_SYNC_AS_STAT: AtFlags = AtFlags(0);

    /// No flags.
    pub const fn empty() -> AtFlags { AtFlags(0) }
    /// The raw bits.
    pub const fn bits(self) -> i32 { self.0 }
    /// Flags from raw bits, keeping unknown bits.
    pub const fn from_bits_retain(bits: i32) -> AtFlags { AtFlags(bits) }
    /// True when every bit of `other` is set in `self`.
    pub const fn contains(self, other: AtFlags) -> bool { self.0 & other.0 == other.0 }
    /// True when no bit is set.
    pub const fn is_empty(self) -> bool { self.0 == 0 }
}

impl core::ops::BitOr for AtFlags {
    type Output = AtFlags;
    fn bitor(self, other: AtFlags) -> AtFlags { AtFlags(self.0 | other.0) }
}

impl core::ops::BitOrAssign for AtFlags {
    fn bitor_assign(&mut self, other: AtFlags) { self.0 |= other.0; }
}

impl core::ops::BitAnd for AtFlags {
    type Output = AtFlags;
    fn bitand(self, other: AtFlags) -> AtFlags { AtFlags(self.0 & other.0) }
}

/// `Access` flags.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Access(u32);

impl Access {
    pub const EXISTS: Access = Access(0);
    pub const EXEC_OK: Access = Access(1);
    pub const WRITE_OK: Access = Access(2);
    pub const READ_OK: Access = Access(4);

    /// No flags.
    pub const fn empty() -> Access { Access(0) }
    /// The raw bits.
    pub const fn bits(self) -> u32 { self.0 }
    /// Flags from raw bits, keeping unknown bits.
    pub const fn from_bits_retain(bits: u32) -> Access { Access(bits) }
    /// True when every bit of `other` is set in `self`.
    pub const fn contains(self, other: Access) -> bool { self.0 & other.0 == other.0 }
    /// True when no bit is set.
    pub const fn is_empty(self) -> bool { self.0 == 0 }
}

impl core::ops::BitOr for Access {
    type Output = Access;
    fn bitor(self, other: Access) -> Access { Access(self.0 | other.0) }
}

impl core::ops::BitOrAssign for Access {
    fn bitor_assign(&mut self, other: Access) { self.0 |= other.0; }
}

impl core::ops::BitAnd for Access {
    type Output = Access;
    fn bitand(self, other: Access) -> Access { Access(self.0 & other.0) }
}

/// `StatxFlags` flags.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct StatxFlags(u32);

impl StatxFlags {
    pub const TYPE: StatxFlags = StatxFlags(0x001);
    pub const MODE: StatxFlags = StatxFlags(0x002);
    pub const NLINK: StatxFlags = StatxFlags(0x004);
    pub const UID: StatxFlags = StatxFlags(0x008);
    pub const GID: StatxFlags = StatxFlags(0x010);
    pub const ATIME: StatxFlags = StatxFlags(0x020);
    pub const MTIME: StatxFlags = StatxFlags(0x040);
    pub const CTIME: StatxFlags = StatxFlags(0x080);
    pub const INO: StatxFlags = StatxFlags(0x100);
    pub const SIZE: StatxFlags = StatxFlags(0x200);
    pub const BLOCKS: StatxFlags = StatxFlags(0x400);
    pub const BASIC_STATS: StatxFlags = StatxFlags(0x7ff);
    pub const BTIME: StatxFlags = StatxFlags(0x800);
    pub const MNT_ID: StatxFlags = StatxFlags(0x1000);
    pub const DIOALIGN: StatxFlags = StatxFlags(0x2000);
    pub const ALL: StatxFlags = StatxFlags(0x3fff);

    /// No flags.
    pub const fn empty() -> StatxFlags { StatxFlags(0) }
    /// The raw bits.
    pub const fn bits(self) -> u32 { self.0 }
    /// Flags from raw bits, keeping unknown bits.
    pub const fn from_bits_retain(bits: u32) -> StatxFlags { StatxFlags(bits) }
    /// True when every bit of `other` is set in `self`.
    pub const fn contains(self, other: StatxFlags) -> bool { self.0 & other.0 == other.0 }
    /// True when no bit is set.
    pub const fn is_empty(self) -> bool { self.0 == 0 }
}

impl core::ops::BitOr for StatxFlags {
    type Output = StatxFlags;
    fn bitor(self, other: StatxFlags) -> StatxFlags { StatxFlags(self.0 | other.0) }
}

impl core::ops::BitOrAssign for StatxFlags {
    fn bitor_assign(&mut self, other: StatxFlags) { self.0 |= other.0; }
}

impl core::ops::BitAnd for StatxFlags {
    type Output = StatxFlags;
    fn bitand(self, other: StatxFlags) -> StatxFlags { StatxFlags(self.0 & other.0) }
}


impl Mode {
    /// The permission bits of a raw mode.
    pub const fn from_raw_mode(mode: u32) -> Mode {
        Mode(mode & 0o7777)
    }

    /// The raw permission bits.
    pub const fn as_raw_mode(self) -> u32 {
        self.0
    }
}

/// A file type, from the mode bits or a directory entry.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum FileType {
    /// A regular file.
    RegularFile,
    /// A directory.
    Directory,
    /// A symbolic link.
    Symlink,
    /// A FIFO (named pipe).
    Fifo,
    /// A socket.
    Socket,
    /// A character device.
    CharacterDevice,
    /// A block device.
    BlockDevice,
    /// Unknown (the file system gave no type).
    Unknown,
}

impl FileType {
    /// The file type of a raw `st_mode`.
    pub const fn from_raw_mode(mode: u32) -> FileType {
        match mode & 0o170000 {
            0o100000 => FileType::RegularFile,
            0o040000 => FileType::Directory,
            0o120000 => FileType::Symlink,
            0o010000 => FileType::Fifo,
            0o140000 => FileType::Socket,
            0o020000 => FileType::CharacterDevice,
            0o060000 => FileType::BlockDevice,
            _ => FileType::Unknown,
        }
    }

    /// The `S_IF*` raw mode bits of this type (0 for Unknown).
    pub const fn as_raw_mode(self) -> u32 {
        match self {
            FileType::RegularFile => 0o100000,
            FileType::Directory => 0o040000,
            FileType::Symlink => 0o120000,
            FileType::Fifo => 0o010000,
            FileType::Socket => 0o140000,
            FileType::CharacterDevice => 0o020000,
            FileType::BlockDevice => 0o060000,
            FileType::Unknown => 0,
        }
    }
}

/// The result of `stat` and kin (Linux fields).
#[derive(Copy, Clone, Debug, Default)]
pub struct Stat {
    pub st_dev: u64,
    pub st_ino: u64,
    pub st_nlink: u64,
    pub st_mode: u32,
    pub st_uid: u32,
    pub st_gid: u32,
    pub st_rdev: u64,
    pub st_size: i64,
    pub st_blksize: i64,
    pub st_blocks: i64,
    pub st_atime: i64,
    pub st_atime_nsec: i64,
    pub st_mtime: i64,
    pub st_mtime_nsec: i64,
    pub st_ctime: i64,
    pub st_ctime_nsec: i64,
}

/// Decodes one sysx stat record.
fn stat_of(rec: &[u8]) -> Stat {
    Stat {
        st_dev: rec_u64(rec, 0),
        st_ino: rec_u64(rec, 1),
        st_nlink: rec_u64(rec, 2),
        st_mode: rec_u64(rec, 3) as u32,
        st_uid: rec_u64(rec, 4) as u32,
        st_gid: rec_u64(rec, 5) as u32,
        st_rdev: rec_u64(rec, 6),
        st_size: rec_i64(rec, 7),
        st_blksize: rec_i64(rec, 8),
        st_blocks: rec_i64(rec, 9),
        st_atime: rec_i64(rec, 10),
        st_atime_nsec: rec_i64(rec, 11),
        st_mtime: rec_i64(rec, 12),
        st_mtime_nsec: rec_i64(rec, 13),
        st_ctime: rec_i64(rec, 14),
        st_ctime_nsec: rec_i64(rec, 15),
    }
}

/// A timestamp within `Statx`.
#[derive(Copy, Clone, Debug, Default)]
pub struct StatxTimestamp {
    pub tv_sec: i64,
    pub tv_nsec: u32,
}

/// The result of `statx`.
#[derive(Copy, Clone, Debug, Default)]
pub struct Statx {
    pub stx_mask: u32,
    pub stx_blksize: u32,
    pub stx_attributes: u64,
    pub stx_nlink: u32,
    pub stx_uid: u32,
    pub stx_gid: u32,
    pub stx_mode: u16,
    pub stx_ino: u64,
    pub stx_size: u64,
    pub stx_blocks: u64,
    pub stx_attributes_mask: u64,
    pub stx_atime: StatxTimestamp,
    pub stx_mtime: StatxTimestamp,
    pub stx_ctime: StatxTimestamp,
    pub stx_btime: StatxTimestamp,
    pub stx_rdev_major: u32,
    pub stx_rdev_minor: u32,
    pub stx_dev_major: u32,
    pub stx_dev_minor: u32,
}

/// Decodes one sysx statx record.
fn statx_of(rec: &[u8]) -> Statx {
    let ts = |sec: usize, nsec: usize| StatxTimestamp { tv_sec: rec_i64(rec, sec), tv_nsec: rec_u64(rec, nsec) as u32 };
    Statx {
        stx_mask: rec_u64(rec, 0) as u32,
        stx_blksize: rec_u64(rec, 1) as u32,
        stx_attributes: rec_u64(rec, 2),
        stx_nlink: rec_u64(rec, 3) as u32,
        stx_uid: rec_u64(rec, 4) as u32,
        stx_gid: rec_u64(rec, 5) as u32,
        stx_mode: rec_u64(rec, 6) as u16,
        stx_ino: rec_u64(rec, 7),
        stx_size: rec_u64(rec, 8),
        stx_blocks: rec_u64(rec, 9),
        stx_attributes_mask: rec_u64(rec, 10),
        stx_atime: ts(11, 12),
        stx_mtime: ts(13, 14),
        stx_ctime: ts(15, 16),
        stx_btime: ts(17, 18),
        stx_rdev_major: rec_u64(rec, 19) as u32,
        stx_rdev_minor: rec_u64(rec, 20) as u32,
        stx_dev_major: rec_u64(rec, 21) as u32,
        stx_dev_minor: rec_u64(rec, 22) as u32,
    }
}

/// A time for `utimensat`: seconds and nanoseconds since the epoch.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Timespec {
    pub tv_sec: i64,
    pub tv_nsec: i64,
}

/// `UTIME_NOW` for a `Timespec` nanosecond field.
pub const UTIME_NOW: i64 = (1 << 30) - 1;
/// `UTIME_OMIT` for a `Timespec` nanosecond field.
pub const UTIME_OMIT: i64 = (1 << 30) - 2;

/// The two times of `utimensat`.
#[derive(Copy, Clone, Debug, Default)]
pub struct Timestamps {
    pub last_access: Timespec,
    pub last_modification: Timespec,
}

/// `open(path, oflags, mode)`.
pub fn open<P: Arg>(path: P, flags: OFlags, mode: Mode) -> Result<OwnedFd> {
    openat(CWD, path, flags, mode)
}

/// `openat(dirfd, path, oflags, mode)`.
pub fn openat<Fd: AsFd, P: Arg>(dirfd: Fd, path: P, flags: OFlags, mode: Mode) -> Result<OwnedFd> {
    let bytes = path_bytes(&path)?;
    let fd = core::intrinsics::sys_x_openat(dirfd.as_fd().as_raw_fd(), &bytes, flags.bits() as i32, mode.as_raw_mode());
    if fd < 0 {
        Err(Errno::from_raw_os_error(-fd))
    } else {
        Ok(OwnedFd::from_raw(fd))
    }
}

/// `fstat(fd)`.
pub fn fstat<Fd: AsFd>(fd: Fd) -> Result<Stat> {
    let mut rec: Vec<u8> = Vec::new();
    let e = core::intrinsics::sys_x_fstat(fd.as_fd().as_raw_fd(), &mut rec);
    if e != 0 {
        return Err(Errno::from_raw_os_error(e));
    }
    Ok(stat_of(&rec))
}

/// `fstatat(dirfd, path, flags)`.
pub fn statat<Fd: AsFd, P: Arg>(dirfd: Fd, path: P, flags: AtFlags) -> Result<Stat> {
    let bytes = path_bytes(&path)?;
    let mut rec: Vec<u8> = Vec::new();
    let e = core::intrinsics::sys_x_statat(dirfd.as_fd().as_raw_fd(), &bytes, flags.bits(), &mut rec);
    if e != 0 {
        return Err(Errno::from_raw_os_error(e));
    }
    Ok(stat_of(&rec))
}

/// `statx(dirfd, path, flags, mask)`.
pub fn statx<Fd: AsFd, P: Arg>(dirfd: Fd, path: P, flags: AtFlags, mask: StatxFlags) -> Result<Statx> {
    let bytes = path_bytes(&path)?;
    let mut rec: Vec<u8> = Vec::new();
    let e = core::intrinsics::sys_x_statx(dirfd.as_fd().as_raw_fd(), &bytes, flags.bits(), mask.bits(), &mut rec);
    if e != 0 {
        return Err(Errno::from_raw_os_error(e));
    }
    Ok(statx_of(&rec))
}

/// `faccessat(dirfd, path, access, flags)`.
pub fn accessat<Fd: AsFd, P: Arg>(dirfd: Fd, path: P, access: Access, flags: AtFlags) -> Result<()> {
    let bytes = path_bytes(&path)?;
    let e = core::intrinsics::sys_x_accessat(dirfd.as_fd().as_raw_fd(), &bytes, access.bits() as i32, flags.bits());
    if e != 0 {
        return Err(Errno::from_raw_os_error(e));
    }
    Ok(())
}

/// `utimensat(dirfd, path, times, flags)`.
pub fn utimensat<Fd: AsFd, P: Arg>(dirfd: Fd, path: P, times: &Timestamps, flags: AtFlags) -> Result<()> {
    let bytes = path_bytes(&path)?;
    let e = core::intrinsics::sys_x_utimensat(
        dirfd.as_fd().as_raw_fd(),
        &bytes,
        times.last_access.tv_sec,
        times.last_access.tv_nsec,
        times.last_modification.tv_sec,
        times.last_modification.tv_nsec,
        flags.bits(),
    );
    if e != 0 {
        return Err(Errno::from_raw_os_error(e));
    }
    Ok(())
}

/// `mknodat(dirfd, path, kind, mode, dev)`.
pub fn mknodat<Fd: AsFd, P: Arg>(dirfd: Fd, path: P, kind: FileType, mode: Mode, dev: u64) -> Result<()> {
    let bytes = path_bytes(&path)?;
    let e = core::intrinsics::sys_x_mknodat(dirfd.as_fd().as_raw_fd(), &bytes, kind.as_raw_mode() | mode.as_raw_mode(), dev);
    if e != 0 {
        return Err(Errno::from_raw_os_error(e));
    }
    Ok(())
}

/// `fcntl(fd, F_GETFL)`.
pub fn fcntl_getfl<Fd: AsFd>(fd: Fd) -> Result<OFlags> {
    let r = core::intrinsics::sys_x_fcntl_getfl(fd.as_fd().as_raw_fd());
    if r < 0 {
        Err(Errno::from_raw_os_error(-r))
    } else {
        Ok(OFlags::from_bits_retain(r as u32))
    }
}

/// `fcntl(fd, F_SETFL, flags)`.
pub fn fcntl_setfl<Fd: AsFd>(fd: Fd, flags: OFlags) -> Result<()> {
    let e = core::intrinsics::sys_x_fcntl_setfl(fd.as_fd().as_raw_fd(), flags.bits() as i32);
    if e != 0 {
        return Err(Errno::from_raw_os_error(e));
    }
    Ok(())
}
