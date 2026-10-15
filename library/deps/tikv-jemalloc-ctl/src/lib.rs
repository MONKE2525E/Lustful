// Lust adapter for tikv-jemalloc-ctl 0.7.0 (docs/ARCH.md section
// 3.6): the `Name` / `AsName` / `Access` surface over a one-arena
// model of the lust runtime allocator, plus `Error`, `version`,
// and `epoch`. This is the form ts-rust uses (`thread.arena` and
// `opt.narenas` by name in program.rs and jemalloc_layout.rs).
//
// Honest limits (see README.md): lust has one allocator arena, so
// `opt.narenas` reads 1 and every thread's `thread.arena` reads
// 0. Real jemalloc answers depend on its build, its
// `MALLOC_CONF`, and the CPU count, so a program that prints
// those values can print a different number under lust; programs
// that only move threads between arenas they read (the ts-rust
// use) behave the same. Keys with allocator-accounting values
// (`stats.*` and kin) and the typed key modules other than
// `version` and `epoch` are not here: the by-name form answers
// `ENOENT`, and the typed forms do not exist, so such code
// rejects or errors, never silently answers with a fake count.
// The `stats` and `profiling` features are not implemented.

use core::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

const EPERM: i32 = 1;
const ENOENT: i32 = 2;
const EAGAIN: i32 = 11;
const EFAULT: i32 = 14;
const EINVAL: i32 = 22;

/// Errors of the mallctl family: a non-zero errno code, as upstream.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Error(i32);

/// Result type, as upstream.
pub type Result<T> = core::result::Result<T, Error>;

/// The error text upstream prints for `code`.
fn description(code: i32) -> Option<&'static str> {
    match code {
        EINVAL => Some(
            "`newp` is not `NULL`, and `newlen` is too large or too small. Alternatively, `*oldlenp` is too large or too small; in this case as much data as possible are read despite the error.",
        ),
        ENOENT => Some("`name` or `mib` specifies an unknown/invalid value."),
        EPERM => Some("Attempt to read or write `void` value, or attempt to write read-only value."),
        EAGAIN => Some("A memory allocation failure occurred."),
        EFAULT => Some("An interface with side effects failed in some way not directly related to `mallctl*()` read/write processing."),
        _ => None,
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match description(self.0) {
            Some(m) => write!(f, "{m}"),
            None => write!(f, "Unknown error code: \"{}\".", self.0),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Self as fmt::Debug>::fmt(self, f)
    }
}

#[cfg(feature = "use_std")]
impl std::error::Error for Error {}

/// A name in the mallctl namespace: an unsized wrapper over the
/// null-terminated bytes, as upstream.
#[repr(transparent)]
#[derive(PartialEq, Eq)]
pub struct Name([u8]);

/// Converts a null-terminated byte-string into a [`Name`].
pub trait AsName {
    /// Converts a null-terminated byte-string into a [`Name`].
    fn name(&self) -> &Name;
}

impl AsName for [u8] {
    fn name(&self) -> &Name {
        assert!(!self.is_empty(), "cannot create Name from empty byte-string");
        assert_eq!(
            *self.last().unwrap(),
            b'\0',
            "cannot create Name from non-null-terminated byte-string \"{}\"",
            core::str::from_utf8(self).unwrap()
        );
        self
    }
}

impl AsName for str {
    fn name(&self) -> &Name {
        self.as_bytes().name()
    }
}

/// True when `v` starts with `pre` (byte slices have no
/// `starts_with` in the lust subset yet).
fn starts_with(v: &[u8], pre: &[u8]) -> bool {
    v.len() >= pre.len() && &v[..pre.len()] == pre
}

/// True when `v` ends with `suf`.
fn ends_with(v: &[u8], suf: &[u8]) -> bool {
    v.len() >= suf.len() && &v[v.len() - suf.len()..] == suf
}

impl Name {
    /// The key bytes without the null terminator.
    fn key(&self) -> &[u8] {
        &self.0[..self.0.len() - 1]
    }

    /// True when this key names a string value, as upstream's list.
    pub fn value_type_str(&self) -> bool {
        let name = self.key();
        if name.is_empty() {
            return false;
        }
        match name {
            b"version"
            | b"config.malloc_conf"
            | b"opt.metadata_thp"
            | b"opt.dss"
            | b"opt.percpu_arena"
            | b"opt.stats_print_opts"
            | b"opt.junk"
            | b"opt.thp"
            | b"opt.prof_prefix"
            | b"thread.prof.name"
            | b"prof.dump" => true,
            v if starts_with(v, b"arena.") && ends_with(v, b".dss") => true,
            v if starts_with(v, b"stats.arenas.") && ends_with(v, b".dss") => true,
            _ => false,
        }
    }

    /// The name as a null-terminated byte-string.
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", core::str::from_utf8(&self.0).unwrap())
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", core::str::from_utf8(&self.0).unwrap())
    }
}

/// The epoch counter. Real jemalloc starts at 1 and each advance
/// adds one; stats reads do not exist here, so the epoch only
/// counts its own advances, as upstream's tests observe it.
static EPOCH: AtomicU64 = AtomicU64::new(1);

std::thread_local! {
    /// This thread's tcache switch (`thread.tcache.enabled`,
    /// initially on, as upstream). Lust's allocator has no
    /// thread cache to switch; the value is kept so reads after
    /// writes agree, and nothing else observes it.
    static TCACHE_ENABLED: core::cell::Cell<bool> = const { core::cell::Cell::new(true) };
}

/// The jemalloc version string of tikv-jemalloc-sys 0.7.1, with
/// its trailing null, as `version` reads it upstream.
const VERSION: &[u8] = b"5.3.1-0-g81034ce1f1373e37dc865038e1bc8eeecf559ce8\0";

/// Advances the epoch and returns its new value.
fn advance_epoch() -> u64 {
    EPOCH.fetch_add(1, Ordering::SeqCst) + 1
}

/// Reads a 4-byte key (`thread.arena`, `opt.narenas`).
fn read_u32(key: &[u8]) -> Result<u32> {
    match key {
        b"thread.arena" => Ok(0),
        b"opt.narenas" => Ok(1),
        b"epoch" | b"version" | b"thread.tcache.enabled" => Err(Error(EINVAL)),
        _ => Err(Error(ENOENT)),
    }
}

/// Writes a 4-byte key.
fn write_u32(key: &[u8], value: u32) -> Result<()> {
    match key {
        // One arena: 0 is the only valid index, as a one-arena
        // jemalloc also answers EFAULT for any other index.
        b"thread.arena" => {
            if value == 0 {
                Ok(())
            } else {
                Err(Error(EFAULT))
            }
        }
        b"opt.narenas" => Err(Error(EPERM)),
        b"epoch" | b"version" | b"thread.tcache.enabled" => Err(Error(EINVAL)),
        _ => Err(Error(ENOENT)),
    }
}

/// Reads an 8-byte key (`epoch`).
fn read_u64(key: &[u8]) -> Result<u64> {
    match key {
        b"epoch" => Ok(EPOCH.load(Ordering::SeqCst)),
        b"thread.arena" | b"opt.narenas" | b"version" | b"thread.tcache.enabled" => Err(Error(EINVAL)),
        _ => Err(Error(ENOENT)),
    }
}

/// Writes an 8-byte key. A write to `epoch` advances it and
/// ignores the value, as upstream.
fn write_u64(key: &[u8], _value: u64) -> Result<()> {
    match key {
        b"epoch" => {
            advance_epoch();
            Ok(())
        }
        b"version" => Err(Error(EPERM)),
        b"thread.arena" | b"opt.narenas" | b"thread.tcache.enabled" => Err(Error(EINVAL)),
        _ => Err(Error(ENOENT)),
    }
}

/// Reads the one bool key (`thread.tcache.enabled`).
fn read_bool(key: &[u8]) -> Result<bool> {
    match key {
        b"thread.tcache.enabled" => Ok(TCACHE_ENABLED.with(|c| c.get())),
        b"thread.arena" | b"opt.narenas" | b"epoch" | b"version" => Err(Error(EINVAL)),
        _ => Err(Error(ENOENT)),
    }
}

/// Writes the one bool key.
fn write_bool(key: &[u8], value: bool) -> Result<()> {
    match key {
        b"thread.tcache.enabled" => {
            TCACHE_ENABLED.with(|c| c.set(value));
            Ok(())
        }
        b"thread.arena" | b"opt.narenas" | b"epoch" | b"version" => Err(Error(EINVAL)),
        _ => Err(Error(ENOENT)),
    }
}

/// Reads a string key. The caller asserted `value_type_str`.
fn read_str_key(key: &[u8]) -> Result<&'static [u8]> {
    match key {
        b"version" => Ok(VERSION),
        _ => Err(Error(ENOENT)),
    }
}

/// Writes a string key. The caller asserted `value_type_str`.
fn write_str_key(key: &[u8], value: &'static [u8]) -> Result<()> {
    assert!(!value.is_empty(), "value cannot be empty");
    assert_eq!(*value.last().unwrap(), b'\0');
    match key {
        b"version" => Err(Error(EPERM)),
        _ => Err(Error(ENOENT)),
    }
}

/// Safe read access to the mallctl namespace.
pub trait Access<T> {
    /// Read the key at `self`.
    fn read(&self) -> Result<T>;
    /// Write `value` at the key `self`.
    fn write(&self, value: T) -> Result<()>;
    /// Write `value` at the key `self` returning its previous value.
    fn update(&self, value: T) -> Result<T>;
}

impl Access<u32> for Name {
    fn read(&self) -> Result<u32> {
        read_u32(self.key())
    }
    fn write(&self, value: u32) -> Result<()> {
        write_u32(self.key(), value)
    }
    fn update(&self, value: u32) -> Result<u32> {
        let old = self.read()?;
        self.write(value)?;
        Ok(old)
    }
}

impl Access<u64> for Name {
    fn read(&self) -> Result<u64> {
        read_u64(self.key())
    }
    fn write(&self, value: u64) -> Result<()> {
        write_u64(self.key(), value)
    }
    fn update(&self, value: u64) -> Result<u64> {
        // `epoch` is the one key whose update returns the new
        // value, as upstream's docs state.
        if matches!(self.key(), b"epoch") {
            return Ok(advance_epoch());
        }
        let old = self.read()?;
        self.write(value)?;
        Ok(old)
    }
}

impl Access<usize> for Name {
    fn read(&self) -> Result<usize> {
        read_u64(self.key()).map(|v| v as usize)
    }
    fn write(&self, value: usize) -> Result<()> {
        write_u64(self.key(), value as u64)
    }
    fn update(&self, value: usize) -> Result<usize> {
        Access::<u64>::update(self, value as u64).map(|v| v as usize)
    }
}

impl Access<isize> for Name {
    fn read(&self) -> Result<isize> {
        read_u64(self.key()).map(|v| v as isize)
    }
    fn write(&self, value: isize) -> Result<()> {
        write_u64(self.key(), value as u64)
    }
    fn update(&self, value: isize) -> Result<isize> {
        Access::<u64>::update(self, value as u64).map(|v| v as isize)
    }
}

impl Access<bool> for Name {
    fn read(&self) -> Result<bool> {
        read_bool(self.key())
    }
    fn write(&self, value: bool) -> Result<()> {
        write_bool(self.key(), value)
    }
    fn update(&self, value: bool) -> Result<bool> {
        let old = self.read()?;
        self.write(value)?;
        Ok(old)
    }
}

impl Access<&'static [u8]> for Name {
    fn read(&self) -> Result<&'static [u8]> {
        assert!(self.value_type_str(), "the name \"{:?}\" does not refer to a byte string", self);
        read_str_key(self.key())
    }
    fn write(&self, value: &'static [u8]) -> Result<()> {
        assert!(self.value_type_str(), "the name \"{:?}\" does not refer to a byte string", self);
        write_str_key(self.key(), value)
    }
    fn update(&self, value: &'static [u8]) -> Result<&'static [u8]> {
        assert!(self.value_type_str(), "the name \"{:?}\" does not refer to a byte string", self);
        let old = read_str_key(self.key())?;
        write_str_key(self.key(), value)?;
        Ok(old)
    }
}

impl Access<&'static str> for Name {
    fn read(&self) -> Result<&'static str> {
        assert!(self.value_type_str(), "the name \"{:?}\" does not refer to a byte string", self);
        let s = read_str_key(self.key())?;
        Ok(core::str::from_utf8(s).unwrap())
    }
    fn write(&self, value: &'static str) -> Result<()> {
        assert!(self.value_type_str(), "the name \"{:?}\" does not refer to a byte string", self);
        write_str_key(self.key(), value.as_bytes())
    }
    fn update(&self, value: &'static str) -> Result<&'static str> {
        assert!(self.value_type_str(), "the name \"{:?}\" does not refer to a byte string", self);
        let old = read_str_key(self.key())?;
        write_str_key(self.key(), value.as_bytes())?;
        Ok(core::str::from_utf8(old).unwrap())
    }
}

/// The `epoch` key: many statistics are cached and refresh when
/// the epoch advances. Here it only counts, as upstream's own
/// tests observe it.
pub mod epoch {
    use super::{Access, AsName, Result};

    /// Reads the epoch.
    pub fn read() -> Result<u64> {
        Access::<u64>::read(b"epoch\0".name())
    }

    /// Advances the epoch, ignoring `value`, as upstream.
    pub fn write(value: u64) -> Result<()> {
        Access::<u64>::write(b"epoch\0".name(), value)
    }

    /// Advances the epoch and returns its new value.
    pub fn update(value: u64) -> Result<u64> {
        Access::<u64>::update(b"epoch\0".name(), value)
    }

    /// Advances the epoch returning its latest value.
    pub fn advance() -> Result<u64> {
        update(1)
    }
}

/// The `version` key: the jemalloc version string.
pub mod version {
    use super::{Access, AsName, Result};

    /// Reads the version string (with its trailing null, as
    /// upstream returns it).
    pub fn read() -> Result<&'static str> {
        b"version\0".name().read()
    }
}
