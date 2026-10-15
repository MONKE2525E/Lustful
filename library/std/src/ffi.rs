// `std::ffi` (W-SHIM): `OsStr` and `OsString` as on Unix, raw bytes
// with no encoding promise.
//
// `OsStr` is an unsized newtype over `[u8]` (the compiler lays it out
// as its field; shipped source may turn `&[u8]` into `&OsStr`).
// `OsString` reaches the `OsStr` methods through `Deref`, as in std.
// `to_string_lossy` is missing: std returns `Cow<str>`, which lust does
// not have yet (W-STD-B).

use core::cmp::Ordering;
use core::fmt;
use core::ops::Deref;

/// Borrowed platform string: a byte slice on Unix.
pub struct OsStr {
    inner: [u8],
}

/// Owned platform string: a byte vector on Unix.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct OsString {
    inner: Vec<u8>,
}

/// The `OsStr` view of raw bytes (the bytes become the string as is).
pub(crate) fn os_str_from_bytes(bytes: &[u8]) -> &OsStr {
    bytes
}

/// The text of valid UTF-8 bytes, None for any other bytes.
pub(crate) fn bytes_to_str(bytes: &[u8]) -> Option<&str> {
    if core::intrinsics::sys_utf8_valid_up_to(bytes) == bytes.len() { Some(core::intrinsics::sys_bytes_as_str(bytes)) } else { None }
}

/// The bytes as text, each invalid sequence replaced by U+FFFD.
pub(crate) fn bytes_to_string_lossy(bytes: &[u8]) -> String {
    let mut out = String::new();
    core::intrinsics::sys_utf8_lossy(bytes, &mut out);
    out
}

/// `Debug` of platform string bytes, as std's `Utf8Chunks` debug form:
/// valid text escaped as `str` Debug escapes it, invalid bytes as
/// `\xNN`, all in double quotes.
pub(crate) fn debug_bytes(bytes: &[u8], f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if let Some(s) = bytes_to_str(bytes) {
        return write!(f, "{:?}", s);
    }
    f.write_str("\"")?;
    let mut rest = bytes;
    while !rest.is_empty() {
        let valid = core::intrinsics::sys_utf8_valid_up_to(rest);
        let text = core::intrinsics::sys_bytes_as_str(&rest[..valid]);
        let quoted = format!("{:?}", text);
        f.write_str(&quoted[1..quoted.len() - 1])?;
        if valid == rest.len() {
            break;
        }
        let bad = invalid_len(&rest[valid..]);
        for k in 0..bad {
            write!(f, "\\x{:02X}", rest[valid + k])?;
        }
        rest = &rest[valid + bad..];
    }
    f.write_str("\"")
}

/// The length of the maximal invalid UTF-8 subpart at the start of
/// `bytes` (which does not start with a valid sequence): 1 to 3.
pub(crate) fn invalid_len(bytes: &[u8]) -> usize {
    let b = bytes[0];
    let (need, lo, hi) = if b >= 0xC2 && b <= 0xDF {
        (2, 0x80, 0xBF)
    } else if b == 0xE0 {
        (3, 0xA0, 0xBF)
    } else if b == 0xED {
        (3, 0x80, 0x9F)
    } else if b >= 0xE1 && b <= 0xEF {
        (3, 0x80, 0xBF)
    } else if b == 0xF0 {
        (4, 0x90, 0xBF)
    } else if b == 0xF4 {
        (4, 0x80, 0x8F)
    } else if b >= 0xF1 && b <= 0xF3 {
        (4, 0x80, 0xBF)
    } else {
        return 1;
    };
    let mut k = 1;
    while k < need && k < bytes.len() {
        let c = bytes[k];
        let (l, h) = if k == 1 { (lo, hi) } else { (0x80, 0xBF) };
        if c < l || c > h {
            return k;
        }
        k += 1;
    }
    k
}

impl OsStr {
    /// Coerces into an `OsStr` slice.
    pub fn new<S: AsRef<OsStr> + ?Sized>(s: &S) -> &OsStr {
        s.as_ref()
    }

    /// The string as `&str` if it is valid Unicode.
    pub fn to_str(&self) -> Option<&str> {
        bytes_to_str(&self.inner)
    }

    /// An owned copy.
    pub fn to_os_string(&self) -> OsString {
        OsString { inner: self.inner.to_vec() }
    }

    /// True for the empty string.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// The length in bytes.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// The underlying bytes.
    pub fn as_encoded_bytes(&self) -> &[u8] {
        &self.inner
    }

    /// ASCII case-insensitive equality.
    pub fn eq_ignore_ascii_case<S: AsRef<OsStr>>(&self, other: S) -> bool {
        let a = &self.inner;
        let b = &other.as_ref().inner;
        if a.len() != b.len() {
            return false;
        }
        for i in 0..a.len() {
            if ascii_lower(a[i]) != ascii_lower(b[i]) {
                return false;
            }
        }
        true
    }

    /// A copy with ASCII letters lowercased.
    pub fn to_ascii_lowercase(&self) -> OsString {
        let mut v = self.inner.to_vec();
        for i in 0..v.len() {
            v[i] = ascii_lower(v[i]);
        }
        OsString { inner: v }
    }

    /// A copy with ASCII letters uppercased.
    pub fn to_ascii_uppercase(&self) -> OsString {
        let mut v = self.inner.to_vec();
        for i in 0..v.len() {
            let b = v[i];
            if b >= b'a' && b <= b'z' {
                v[i] = b - 32;
            }
        }
        OsString { inner: v }
    }
}

fn ascii_lower(b: u8) -> u8 {
    if b >= b'A' && b <= b'Z' { b + 32 } else { b }
}

impl OsString {
    /// An empty `OsString`.
    pub fn new() -> OsString {
        OsString { inner: Vec::new() }
    }

    /// An empty `OsString` with room for `capacity` bytes.
    pub fn with_capacity(capacity: usize) -> OsString {
        OsString { inner: Vec::with_capacity(capacity) }
    }

    /// The `OsString` of the bytes, as given.
    pub(crate) fn from_vec(inner: Vec<u8>) -> OsString {
        OsString { inner }
    }

    /// The string as a `String` if it is valid Unicode, else itself.
    pub fn into_string(self) -> Result<String, OsString> {
        if core::intrinsics::sys_utf8_valid_up_to(&self.inner) == self.inner.len() {
            Ok(core::intrinsics::sys_string_from_utf8_unchecked(self.inner))
        } else {
            Err(self)
        }
    }

    /// The bytes.
    pub fn into_encoded_bytes(self) -> Vec<u8> {
        self.inner
    }

    /// Appends a platform string.
    pub fn push<T: AsRef<OsStr>>(&mut self, s: T) {
        let s: &OsStr = s.as_ref();
        self.inner.extend_from_slice(&s.inner);
    }

    /// The borrowed `OsStr`.
    pub fn as_os_str(&self) -> &OsStr {
        os_str_from_bytes(&self.inner)
    }

    /// Removes the contents, keeping the buffer.
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// The buffer capacity in bytes.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Shortens the string to `len` bytes.
    pub(crate) fn truncate(&mut self, len: usize) {
        self.inner.truncate(len);
    }
}

impl ToOwned for OsStr {
    type Owned = OsString;

    fn to_owned(&self) -> OsString {
        self.to_os_string()
    }

    fn clone_into(&self, target: &mut OsString) {
        target.clear();
        target.push(self);
    }
}

impl fmt::Debug for OsStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        debug_bytes(&self.inner, f)
    }
}

impl fmt::Debug for OsString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        debug_bytes(&self.inner, f)
    }
}

impl AsRef<OsStr> for OsStr {
    fn as_ref(&self) -> &OsStr {
        self
    }
}

impl AsRef<OsStr> for OsString {
    fn as_ref(&self) -> &OsStr {
        os_str_from_bytes(&self.inner)
    }
}

impl AsRef<OsStr> for str {
    fn as_ref(&self) -> &OsStr {
        os_str_from_bytes(core::intrinsics::sys_str_as_bytes(self))
    }
}

impl AsRef<OsStr> for String {
    fn as_ref(&self) -> &OsStr {
        os_str_from_bytes(self.as_bytes())
    }
}

impl From<String> for OsString {
    fn from(s: String) -> OsString {
        OsString { inner: s.into_bytes() }
    }
}

impl From<&str> for OsString {
    fn from(s: &str) -> OsString {
        OsString { inner: core::intrinsics::sys_str_as_bytes(s).to_vec() }
    }
}

impl PartialEq for OsStr {
    fn eq(&self, other: &OsStr) -> bool {
        self.inner == other.inner
    }
}

impl Eq for OsStr {}

impl PartialEq<str> for OsStr {
    fn eq(&self, other: &str) -> bool {
        &self.inner == core::intrinsics::sys_str_as_bytes(other)
    }
}

impl PartialEq<OsStr> for str {
    fn eq(&self, other: &OsStr) -> bool {
        core::intrinsics::sys_str_as_bytes(self) == &other.inner
    }
}

impl PartialEq<str> for OsString {
    fn eq(&self, other: &str) -> bool {
        self.inner.as_slice() == core::intrinsics::sys_str_as_bytes(other)
    }
}

impl PartialEq<&str> for OsString {
    fn eq(&self, other: &&str) -> bool {
        self.inner.as_slice() == core::intrinsics::sys_str_as_bytes(*other)
    }
}

impl PartialEq<OsString> for str {
    fn eq(&self, other: &OsString) -> bool {
        core::intrinsics::sys_str_as_bytes(self) == other.inner.as_slice()
    }
}

impl PartialEq<OsString> for &str {
    fn eq(&self, other: &OsString) -> bool {
        core::intrinsics::sys_str_as_bytes(*self) == other.inner.as_slice()
    }
}

impl PartialEq<OsStr> for OsString {
    fn eq(&self, other: &OsStr) -> bool {
        self.inner.as_slice() == &other.inner
    }
}

impl PartialEq<OsString> for OsStr {
    fn eq(&self, other: &OsString) -> bool {
        &self.inner == other.inner.as_slice()
    }
}

impl PartialOrd for OsStr {
    fn partial_cmp(&self, other: &OsStr) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OsStr {
    fn cmp(&self, other: &OsStr) -> Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl Deref for OsString {
    type Target = OsStr;
    fn deref(&self) -> &OsStr {
        os_str_from_bytes(&self.inner)
    }
}
