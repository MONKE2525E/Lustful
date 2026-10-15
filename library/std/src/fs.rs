// `std::fs` (W-SHIM): whole-file reads and writes, directories,
// metadata, and directory listings, as std does them on Linux.
//
// Each function makes the same syscalls as std (open flags and modes
// included), so results and `io::Error` values match: OS errors carry
// errno, a path with a NUL byte is std's InvalidInput error, invalid
// UTF-8 in `read_to_string` is std's InvalidData error. `File` and
// `OpenOptions` are not here yet.

use crate::ffi::OsString;
use crate::io;
use crate::path::{Path, PathBuf};
use core::fmt;

/// The `io::Result` of a runtime status: 0 is Ok, -1 a path with a NUL
/// byte, -2 a zero-length write, anything else an errno.
pub(crate) fn status(code: i32) -> io::Result<()> {
    match code {
        0 => Ok(()),
        -1 => Err(io::Error::simple_message(io::ErrorKind::InvalidInput, "file name contained an unexpected NUL byte")),
        -2 => Err(io::Error::simple_message(io::ErrorKind::WriteZero, "failed to write whole buffer")),
        code => Err(io::Error::from_raw_os_error(code)),
    }
}

fn bytes_of(path: &Path) -> &[u8] {
    path.as_os_str().as_encoded_bytes()
}

/// The whole contents of a file.
pub fn read<P: AsRef<Path>>(path: P) -> io::Result<Vec<u8>> {
    let mut buf: Vec<u8> = Vec::new();
    match status(core::intrinsics::sys_read_file(bytes_of(path.as_ref()), &mut buf)) {
        Ok(()) => Ok(buf),
        Err(e) => Err(e),
    }
}

/// The whole contents of a file as a `String`.
pub fn read_to_string<P: AsRef<Path>>(path: P) -> io::Result<String> {
    let buf = match read(path) {
        Ok(buf) => buf,
        Err(e) => return Err(e),
    };
    if core::intrinsics::sys_utf8_valid_up_to(&buf) == buf.len() {
        Ok(core::intrinsics::sys_string_from_utf8_unchecked(buf))
    } else {
        Err(io::Error::simple_message(io::ErrorKind::InvalidData, "stream did not contain valid UTF-8"))
    }
}

/// Creates or truncates a file and writes all of `contents` to it.
pub fn write<P: AsRef<Path>, C: AsRef<[u8]>>(path: P, contents: C) -> io::Result<()> {
    let data: &[u8] = contents.as_ref();
    status(core::intrinsics::sys_write_file(bytes_of(path.as_ref()), data))
}

/// The `mode: 0o000666` field of the `OpenOptions` Debug form.
struct CreateMode;

impl fmt::Debug for CreateMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("0o000666")
    }
}

/// Options for opening a file: access, creation, and truncation, as
/// std validates and applies them on Linux.
#[derive(Clone)]
pub struct OpenOptions {
    read: bool,
    write: bool,
    append: bool,
    truncate: bool,
    create: bool,
    create_new: bool,
}

impl OpenOptions {
    /// A blank set of options, ready to configure.
    pub fn new() -> OpenOptions {
        OpenOptions { read: false, write: false, append: false, truncate: false, create: false, create_new: false }
    }

    /// Read access.
    pub fn read(&mut self, read: bool) -> &mut OpenOptions {
        self.read = read;
        self
    }

    /// Write access.
    pub fn write(&mut self, write: bool) -> &mut OpenOptions {
        self.write = write;
        self
    }

    /// Append access: writes go to the end of the file.
    pub fn append(&mut self, append: bool) -> &mut OpenOptions {
        self.append = append;
        self
    }

    /// Truncate the file to empty on open.
    pub fn truncate(&mut self, truncate: bool) -> &mut OpenOptions {
        self.truncate = truncate;
        self
    }

    /// Create the file when it does not exist.
    pub fn create(&mut self, create: bool) -> &mut OpenOptions {
        self.create = create;
        self
    }

    /// Create the file, failing when it already exists.
    pub fn create_new(&mut self, create_new: bool) -> &mut OpenOptions {
        self.create_new = create_new;
        self
    }

    /// Opens the file with these options.
    pub fn open<P: AsRef<Path>>(&self, path: P) -> io::Result<File> {
        let path: &Path = path.as_ref();
        let bytes = bytes_of(path);
        if bytes.contains(&0) {
            return match status(-1) {
                Ok(()) => unreachable!(),
                Err(e) => Err(e),
            };
        }
        // std's checks: truncate needs plain write access, except
        // that create_new drops the truncate flag entirely; creating
        // needs write or append access.
        if (self.truncate && !self.create_new && (self.append || !self.write)) || ((self.create || self.create_new) && !self.write && !self.append) {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "creating or truncating a file requires write or append access"));
        }
        if !self.read && !self.write && !self.append {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "must specify at least one of read, write, or append access"));
        }
        // std's access_mode: append dominates write.
        let access: i32 = if self.append {
            if self.read { 2 } else { 1 }
        } else if self.read && self.write {
            2
        } else if self.write {
            1
        } else {
            0
        };
        let mut flags = access;
        if self.create || self.create_new {
            flags |= 4;
        }
        if self.truncate {
            flags |= 8;
        }
        if self.append {
            flags |= 16;
        }
        if self.create_new {
            flags |= 32;
        }
        let fd = core::intrinsics::sys_fd_open(bytes, flags);
        if fd < 0 {
            Err(io::Error::from_raw_os_error(-fd))
        } else {
            Ok(File { fd, read: access != 1, write: access != 0 })
        }
    }
}

/// The inner struct of the `OpenOptions` Debug form.
struct OpenOptionsInner<'a>(&'a OpenOptions);

impl fmt::Debug for OpenOptionsInner<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OpenOptions")
            .field("read", &self.0.read)
            .field("write", &self.0.write)
            .field("append", &self.0.append)
            .field("truncate", &self.0.truncate)
            .field("create", &self.0.create)
            .field("create_new", &self.0.create_new)
            .field("custom_flags", &0)
            .field("mode", &CreateMode)
            .finish()
    }
}

impl fmt::Debug for OpenOptions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("OpenOptions").field(&OpenOptionsInner(self)).finish()
    }
}

/// An open file. Dropping it closes the descriptor.
pub struct File {
    fd: i32,
    read: bool,
    write: bool,
}

impl File {
    /// Opens a file for reading.
    pub fn open<P: AsRef<Path>>(path: P) -> io::Result<File> {
        OpenOptions::new().read(true).open(path)
    }

    /// Creates a file for writing, truncating it when it exists.
    pub fn create<P: AsRef<Path>>(path: P) -> io::Result<File> {
        OpenOptions::new().write(true).create(true).truncate(true).open(path)
    }

    /// Creates a file for writing, failing when it already exists.
    pub fn create_new<P: AsRef<Path>>(path: P) -> io::Result<File> {
        OpenOptions::new().write(true).create_new(true).open(path)
    }

    /// A blank `OpenOptions`, as a starting point.
    pub fn options() -> OpenOptions {
        OpenOptions::new()
    }

    /// A new handle to the same open file (they share the position).
    pub fn try_clone(&self) -> io::Result<File> {
        let fd = core::intrinsics::sys_fd_dup(self.fd);
        if fd < 0 {
            Err(io::Error::from_raw_os_error(-fd))
        } else {
            Ok(File { fd, read: self.read, write: self.write })
        }
    }

    /// Flushes the file's data and metadata to storage.
    pub fn sync_all(&self) -> io::Result<()> {
        status(core::intrinsics::sys_fd_sync(self.fd))
    }

    /// Flushes the file's data to storage.
    pub fn sync_data(&self) -> io::Result<()> {
        status(core::intrinsics::sys_fd_sync_data(self.fd))
    }

    /// Sets the file's length (extending with zeros, or truncating).
    pub fn set_len(&self, size: u64) -> io::Result<()> {
        status(core::intrinsics::sys_fd_truncate(self.fd, size))
    }

    /// The raw descriptor (for `std::os::fd` in os.rs).
    pub(crate) fn __raw_fd(&self) -> i32 {
        self.fd
    }

    /// A `File` that owns `fd` (for `std::os::fd` in os.rs). The
    /// descriptor's own mode governs reads and writes, as in std.
    pub(crate) fn __from_raw_fd(fd: i32) -> File {
        File { fd, read: true, write: true }
    }

    /// The raw descriptor, without closing it (os.rs).
    pub(crate) fn __into_raw_fd(self) -> i32 {
        let fd = self.fd;
        core::mem::forget(self);
        fd
    }

    /// The file's metadata.
    pub fn metadata(&self) -> io::Result<Metadata> {
        let mut raw: Vec<u8> = Vec::new();
        if let Err(e) = status(core::intrinsics::sys_fd_stat(self.fd, &mut raw)) {
            return Err(e);
        }
        Ok(metadata_from_raw(&raw))
    }
}

impl Drop for File {
    fn drop(&mut self) {
        if self.fd >= 0 {
            let _ = core::intrinsics::sys_fd_close(self.fd);
        }
    }
}

impl fmt::Debug for File {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let link = format!("/proc/self/fd/{}", self.fd);
        let mut raw: Vec<u8> = Vec::new();
        let _ = core::intrinsics::sys_readlink(core::intrinsics::sys_str_as_bytes(&link), &mut raw);
        f.debug_struct("File")
            .field("fd", &self.fd)
            .field("path", &PathBuf::from_os_string(OsString::__from_vec(raw)))
            .field("read", &self.read)
            .field("write", &self.write)
            .finish()
    }
}

/// Reserves std's `File::read_to_end` size hint: the metadata
/// length past the current position.
fn file_hint_reserve(file: &File, buf: &mut Vec<u8>) {
    if let Ok(m) = file.metadata() {
        if let Ok(pos) = io::seek_fd(file.fd, io::SeekFrom::Current(0)) {
            let left = m.len().saturating_sub(pos) as usize;
            if left > 0 {
                buf.reserve(left);
            }
        }
    }
}

impl io::Read for File {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        io::read_fd(self.fd, buf)
    }

    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
        file_hint_reserve(self, buf);
        io::read_to_end_default(self, buf)
    }
}

impl io::Read for &File {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        io::read_fd(self.fd, buf)
    }

    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
        file_hint_reserve(self, buf);
        io::read_to_end_default(self, buf)
    }
}

impl io::Write for File {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        io::write_fd(self.fd, buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl io::Write for &File {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        io::write_fd(self.fd, buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl io::Seek for File {
    fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        io::seek_fd(self.fd, pos)
    }
}

impl io::Seek for &File {
    fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        io::seek_fd(self.fd, pos)
    }
}

impl From<File> for crate::process::Stdio {
    fn from(mut file: File) -> crate::process::Stdio {
        let fd = file.fd;
        file.fd = -1;
        crate::process::Stdio::from_fd(fd)
    }
}

/// Creates one directory (mode 0777 before the umask).
pub fn create_dir<P: AsRef<Path>>(path: P) -> io::Result<()> {
    status(core::intrinsics::sys_path_op(bytes_of(path.as_ref()), 0))
}

/// Creates a directory and every missing parent, as std's
/// `DirBuilder::create_dir_all`: an existing directory is fine.
pub fn create_dir_all<P: AsRef<Path>>(path: P) -> io::Result<()> {
    create_dir_all_inner(path.as_ref())
}

fn create_dir_all_inner(path: &Path) -> io::Result<()> {
    if bytes_of(path).is_empty() {
        return Ok(());
    }
    match create_dir(path) {
        Ok(()) => return Ok(()),
        Err(e) => {
            if e.kind() != io::ErrorKind::NotFound {
                return if path.is_dir() { Ok(()) } else { Err(e) };
            }
        }
    }
    match path.parent() {
        Some(p) => {
            if let Err(e) = create_dir_all_inner(p) {
                return Err(e);
            }
        }
        None => return Err(io::Error::simple_message(io::ErrorKind::__Uncategorized, "failed to create whole tree")),
    }
    match create_dir(path) {
        Ok(()) => Ok(()),
        Err(e) => {
            if path.is_dir() {
                Ok(())
            } else {
                Err(e)
            }
        }
    }
}

/// Removes a file (or a symlink).
pub fn remove_file<P: AsRef<Path>>(path: P) -> io::Result<()> {
    status(core::intrinsics::sys_path_op(bytes_of(path.as_ref()), 1))
}

/// Removes an empty directory.
pub fn remove_dir<P: AsRef<Path>>(path: P) -> io::Result<()> {
    status(core::intrinsics::sys_path_op(bytes_of(path.as_ref()), 2))
}

/// Removes a directory and everything in it (a symlink is removed,
/// not followed).
pub fn remove_dir_all<P: AsRef<Path>>(path: P) -> io::Result<()> {
    status(core::intrinsics::sys_remove_dir_all(bytes_of(path.as_ref())))
}

/// Renames a file or directory, replacing `to` when it exists.
pub fn rename<P: AsRef<Path>, Q: AsRef<Path>>(from: P, to: Q) -> io::Result<()> {
    status(core::intrinsics::sys_rename(bytes_of(from.as_ref()), bytes_of(to.as_ref())))
}

/// The absolute path with every symlink resolved.
pub fn canonicalize<P: AsRef<Path>>(path: P) -> io::Result<PathBuf> {
    let mut buf: Vec<u8> = Vec::new();
    match status(core::intrinsics::sys_realpath(bytes_of(path.as_ref()), &mut buf)) {
        Ok(()) => Ok(PathBuf::from_os_string(OsString::__from_vec(buf))),
        Err(e) => Err(e),
    }
}

/// True when the path exists (following symlinks); errors other than
/// NotFound are returned.
pub fn exists<P: AsRef<Path>>(path: P) -> io::Result<bool> {
    match metadata(path) {
        Ok(_) => Ok(true),
        Err(e) => {
            if e.kind() == io::ErrorKind::NotFound {
                Ok(false)
            } else {
                Err(e)
            }
        }
    }
}

/// The type bits of a mode (`S_IFMT`) and the ones std names.
const S_IFMT: u64 = 0o170000;
const S_IFDIR: u64 = 0o040000;
const S_IFREG: u64 = 0o100000;
const S_IFLNK: u64 = 0o120000;

/// The type of a file: directory, regular file, symlink, or other.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct FileType {
    mode: u64,
}

impl FileType {
    /// True for a directory.
    pub fn is_dir(&self) -> bool {
        self.mode & S_IFMT == S_IFDIR
    }

    /// True for a regular file.
    pub fn is_file(&self) -> bool {
        self.mode & S_IFMT == S_IFREG
    }

    /// True for a symbolic link.
    pub fn is_symlink(&self) -> bool {
        self.mode & S_IFMT == S_IFLNK
    }
}

impl fmt::Debug for FileType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FileType")
            .field("is_file", &self.is_file())
            .field("is_dir", &self.is_dir())
            .field("is_symlink", &self.is_symlink())
            .finish_non_exhaustive()
    }
}

/// The permission bits of a file.
#[derive(Clone, PartialEq, Eq)]
pub struct Permissions {
    mode: u64,
}

impl Permissions {
    /// True when no write bit is set.
    pub fn readonly(&self) -> bool {
        self.mode & 0o222 == 0
    }
}

impl fmt::Debug for Permissions {
    /// As std: `Permissions(FilePermissions { mode: 0o100644 (-rw-r--r--) })`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let m = self.mode;
        let kind = match m & S_IFMT {
            S_IFDIR => 'd',
            S_IFLNK => 'l',
            0o010000 => 'p',
            0o140000 => 's',
            0o020000 => 'c',
            0o060000 => 'b',
            _ => '-',
        };
        let mut text = String::new();
        text.push(kind);
        let bit = |b: u64, c: char| if m & b != 0 { c } else { '-' };
        let exec = |x: u64, special: u64, set: char, unset: char| {
            if m & special != 0 {
                if m & x != 0 { set } else { unset }
            } else if m & x != 0 {
                'x'
            } else {
                '-'
            }
        };
        text.push(bit(0o400, 'r'));
        text.push(bit(0o200, 'w'));
        text.push(exec(0o100, 0o4000, 's', 'S'));
        text.push(bit(0o040, 'r'));
        text.push(bit(0o020, 'w'));
        text.push(exec(0o010, 0o2000, 's', 'S'));
        text.push(bit(0o004, 'r'));
        text.push(bit(0o002, 'w'));
        text.push(exec(0o001, 0o1000, 't', 'T'));
        let mode = PermModeText(format!("{:#08o} ({})", m, text));
        f.debug_tuple("Permissions").field(&FilePerm { mode }).finish()
    }
}

/// Raw text that `Debug`-formats as itself (the mode value of
/// `Permissions` debug output carries its own `0o… (…)` text).
struct PermModeText(String);

impl fmt::Debug for PermModeText {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// The inner value of `Permissions` debug output, built with
/// `debug_struct` so the alternate (`{:#?}`) form expands as std's does.
struct FilePerm {
    mode: PermModeText,
}

impl fmt::Debug for FilePerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FilePermissions").field("mode", &self.mode).finish()
    }
}

/// Metadata of a file: its type, length, and permissions. The
/// Unix identity and ownership fields ride along for
/// `std::os::unix::fs::MetadataExt` (std/src/os.rs).
#[derive(Clone)]
pub struct Metadata {
    pub(crate) mode: u64,
    len: u64,
    pub(crate) mtime: i64,
    pub(crate) mtime_nsec: i64,
    pub(crate) uid: u32,
    pub(crate) gid: u32,
    pub(crate) nlink: u64,
    pub(crate) ino: u64,
    pub(crate) dev: u64,
    pub(crate) atime: i64,
    pub(crate) atime_nsec: i64,
    pub(crate) ctime: i64,
    pub(crate) ctime_nsec: i64,
    pub(crate) blocks: u64,
    pub(crate) blksize: u64,
    pub(crate) rdev: u64,
}

impl Metadata {
    /// The file type.
    pub fn file_type(&self) -> FileType {
        FileType { mode: self.mode }
    }

    /// True for a directory.
    pub fn is_dir(&self) -> bool {
        self.file_type().is_dir()
    }

    /// True for a regular file.
    pub fn is_file(&self) -> bool {
        self.file_type().is_file()
    }

    /// True for a symbolic link (only `symlink_metadata` sees one).
    pub fn is_symlink(&self) -> bool {
        self.file_type().is_symlink()
    }

    /// The size in bytes.
    pub fn len(&self) -> u64 {
        self.len
    }

    /// The permissions.
    pub fn permissions(&self) -> Permissions {
        Permissions { mode: self.mode }
    }
}

/// The metadata from the runtime's 8-byte stat fields (sys.c
/// `lust_sys_stat`): mode, size, mtime, uid, gid, nlink, ino,
/// dev, atime, ctime, blocks, blksize, rdev.
fn metadata_from_raw(raw: &[u8]) -> Metadata {
    let field = |i: usize| {
        let mut v: u64 = 0;
        for k in 0..8 {
            v |= (raw[i * 8 + k] as u64) << (8 * k);
        }
        v
    };
    Metadata {
        mode: field(0),
        len: field(1),
        mtime: field(2) as i64,
        mtime_nsec: field(3) as i64,
        uid: field(4) as u32,
        gid: field(5) as u32,
        nlink: field(6),
        ino: field(7),
        dev: field(8),
        atime: field(9) as i64,
        atime_nsec: field(10) as i64,
        ctime: field(11) as i64,
        ctime_nsec: field(12) as i64,
        blocks: field(13),
        blksize: field(14),
        rdev: field(15),
    }
}

/// stat (follow) or lstat of a path.
fn stat(path: &Path, follow: bool) -> io::Result<Metadata> {
    let mut raw: Vec<u8> = Vec::new();
    if let Err(e) = status(core::intrinsics::sys_stat(bytes_of(path), follow, &mut raw)) {
        return Err(e);
    }
    Ok(metadata_from_raw(&raw))
}

/// The metadata of a path, following symlinks.
pub fn metadata<P: AsRef<Path>>(path: P) -> io::Result<Metadata> {
    stat(path.as_ref(), true)
}

/// The metadata of a path itself (a symlink is not followed).
pub fn symlink_metadata<P: AsRef<Path>>(path: P) -> io::Result<Metadata> {
    stat(path.as_ref(), false)
}

/// The entries of a directory, in the order the OS lists them.
pub struct ReadDir {
    root: PathBuf,
    names: Vec<Vec<u8>>,
    next: usize,
}

impl fmt::Debug for ReadDir {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ReadDir").field(&self.root).finish()
    }
}

impl Iterator for ReadDir {
    type Item = io::Result<DirEntry>;

    fn next(&mut self) -> Option<io::Result<DirEntry>> {
        if self.next < self.names.len() {
            self.next += 1;
            let name = OsString::__from_vec(self.names[self.next - 1].clone());
            Some(Ok(DirEntry { path: self.root.join(&name), name }))
        } else {
            None
        }
    }
}

/// One entry of a directory listing.
pub struct DirEntry {
    path: PathBuf,
    name: OsString,
}

impl DirEntry {
    /// The directory path joined with the entry's name.
    pub fn path(&self) -> PathBuf {
        self.path.clone()
    }

    /// The entry's name.
    pub fn file_name(&self) -> OsString {
        self.name.clone()
    }

    /// The entry's metadata (a symlink is not followed).
    pub fn metadata(&self) -> io::Result<Metadata> {
        stat(&self.path, false)
    }

    /// The entry's file type (a symlink is not followed).
    pub fn file_type(&self) -> io::Result<FileType> {
        match stat(&self.path, false) {
            Ok(m) => Ok(m.file_type()),
            Err(e) => Err(e),
        }
    }
}

impl fmt::Debug for DirEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("DirEntry").field(&self.path).finish()
    }
}

/// The entries of a directory.
pub fn read_dir<P: AsRef<Path>>(path: P) -> io::Result<ReadDir> {
    let path: &Path = path.as_ref();
    let mut raw: Vec<u8> = Vec::new();
    if let Err(e) = status(core::intrinsics::sys_read_dir(bytes_of(path), &mut raw)) {
        return Err(e);
    }
    let mut names: Vec<Vec<u8>> = Vec::new();
    let mut start = 0;
    for i in 0..raw.len() {
        if raw[i] == 0 {
            names.push(raw[start..i].to_vec());
            start = i + 1;
        }
    }
    Ok(ReadDir { root: path.to_path_buf(), names, next: 0 })
}
