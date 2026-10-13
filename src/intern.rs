// String interning. Identifiers become `Sym` (a u32) during lexing, so later stages compare integers.
// The interner is sharded by hash, so many threads can lex and parse at once.
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::sync::Mutex;

/// FxHash (from rustc). Much faster than SipHash for short keys; no DoS resistance needed here.
#[derive(Default, Clone, Copy)]
pub struct FxHasher(u64);

impl Hasher for FxHasher {
    fn write(&mut self, bytes: &[u8]) {
        let (words, rest) = bytes.as_chunks::<8>();
        for w in words {
            self.add(u64::from_le_bytes(*w));
        }
        for &b in rest {
            self.add(b as u64);
        }
    }
    fn write_u8(&mut self, i: u8) {
        self.add(i as u64);
    }
    fn write_u32(&mut self, i: u32) {
        self.add(i as u64);
    }
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

impl FxHasher {
    fn add(&mut self, w: u64) {
        self.0 = (self.0.rotate_left(5) ^ w).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
}

pub type FxMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Sym(pub u32);

const SHARD_BITS: u32 = 6;
const SHARDS: usize = 1 << SHARD_BITS;

#[derive(Default)]
struct Shard {
    map: FxMap<Box<str>, u32>,
    strs: Vec<Box<str>>,
}

/// A `Sym` packs `(index in shard << SHARD_BITS) | shard`.
pub struct Interner {
    shards: Vec<Mutex<Shard>>,
}

impl Default for Interner {
    fn default() -> Interner {
        Interner { shards: (0..SHARDS).map(|_| Mutex::default()).collect() }
    }
}

impl Interner {
    pub fn intern(&self, s: &str) -> Sym {
        let mut h = FxHasher::default();
        s.hash(&mut h);
        let shard = (h.finish() >> 58) as usize & (SHARDS - 1);
        let mut sh = self.shards[shard].lock().unwrap();
        if let Some(&i) = sh.map.get(s) {
            return Sym((i << SHARD_BITS) | shard as u32);
        }
        let i = sh.strs.len() as u32;
        sh.strs.push(s.into());
        sh.map.insert(s.into(), i);
        Sym((i << SHARD_BITS) | shard as u32)
    }

    pub fn get(&self, sym: Sym) -> &str {
        let sh = self.shards[(sym.0 as usize) & (SHARDS - 1)].lock().unwrap();
        let s: *const str = &*sh.strs[(sym.0 >> SHARD_BITS) as usize];
        // SAFETY: strings are boxed and never removed or mutated, so the heap data stays valid
        // after the lock guard drops, for as long as the interner lives.
        unsafe { &*s }
    }
}

macro_rules! known_syms {
    ($($name:ident),* $(,)?) => {
        /// Symbols the compiler looks up by name. Interned before lexing, so they always exist.
        #[allow(non_snake_case)]
        pub struct Known {
            $(pub $name: Sym,)*
            /// `self` and `Self` are keywords, so they cannot be macro field names.
            pub self_value: Sym,
            pub self_type: Sym,
        }
        impl Known {
            pub fn new(i: &Interner) -> Known {
                Known {
                    $($name: i.intern(stringify!($name)),)*
                    self_value: i.intern("self"),
                    self_type: i.intern("Self"),
                }
            }
        }
    };
}

known_syms!(
    std,
    core,
    intrinsics,
    env,
    args,
    String,
    Vec,
    str,
    main,
    new,
    from,
    with_capacity,
    count,
    len,
    is_empty,
    push,
    push_str,
    as_str,
    to_string,
    to_owned,
    clone,
    wrapping_add,
    wrapping_sub,
    wrapping_mul,
    wrapping_div,
    wrapping_rem,
    wrapping_neg,
    wrapping_pow,
    wrapping_shl,
    wrapping_shr,
    wrapping_abs,
    checked_add,
    checked_sub,
    checked_mul,
    checked_div,
    checked_rem,
    checked_neg,
    checked_abs,
    checked_pow,
    checked_shl,
    checked_shr,
    saturating_add,
    saturating_sub,
    saturating_mul,
    saturating_div,
    saturating_neg,
    saturating_abs,
    saturating_pow,
    overflowing_add,
    overflowing_sub,
    overflowing_mul,
    overflowing_div,
    overflowing_rem,
    overflowing_neg,
    overflowing_abs,
    overflowing_pow,
    overflowing_shl,
    overflowing_shr,
    count_ones,
    count_zeros,
    leading_zeros,
    trailing_zeros,
    leading_ones,
    trailing_ones,
    rotate_left,
    rotate_right,
    swap_bytes,
    reverse_bits,
    div_euclid,
    rem_euclid,
    signum,
    is_positive,
    is_negative,
    is_power_of_two,
    sqrt,
    powi,
    powf,
    exp,
    ln,
    log,
    log2,
    log10,
    mul_add,
    floor,
    ceil,
    round,
    trunc,
    fract,
    recip,
    is_nan,
    is_infinite,
    is_finite,
    is_sign_positive,
    is_sign_negative,
    to_bits,
    from_bits,
    copysign,
    len_utf8,
    len_utf16,
    is_ascii,
    is_ascii_punctuation,
    is_ascii_graphic,
    is_ascii_hexdigit,
    is_ascii_control,
    is_digit,
    abs,
    min,
    max,
    pow,
    bool,
    char,
    i8,
    i16,
    i32,
    i64,
    isize,
    u8,
    u16,
    u32,
    u64,
    usize,
    i128,
    u128,
    f32,
    f64,
    println,
    print,
    eprintln,
    eprint,
    format,
    panic,
    vec,
    assert,
    assert_eq,
    assert_ne,
    todo,
    unreachable,
    derive,
    test,
    allow,
    warn,
    deny,
    Option,
    Some,
    None,
    is_some,
    is_none,
    unwrap,
    expect,
    unwrap_or,
    pop,
    get,
    first,
    last,
    contains,
    swap,
    clear,
    insert,
    remove,
    truncate,
    starts_with,
    ends_with,
    trim,
    to_uppercase,
    to_lowercase,
    chars,
    next,
    is_ascii_digit,
    is_ascii_alphabetic,
    is_ascii_alphanumeric,
    is_ascii_whitespace,
    is_ascii_uppercase,
    is_ascii_lowercase,
    to_ascii_uppercase,
    to_ascii_lowercase,
    to_digit,
    Result,
    Ok,
    Err,
    is_ok,
    is_err,
);

impl Known {
    /// The integer type a name refers to, if any.
    pub fn int_ty(&self, s: Sym) -> Option<crate::ty::IntTy> {
        use crate::ty::IntTy::*;
        let table = [
            (self.i8, I8),
            (self.i16, I16),
            (self.i32, I32),
            (self.i64, I64),
            (self.isize, Isize),
            (self.u8, U8),
            (self.u16, U16),
            (self.u32, U32),
            (self.u64, U64),
            (self.usize, Usize),
            (self.i128, I128),
            (self.u128, U128),
        ];
        table.iter().find(|(k, _)| *k == s).map(|&(_, t)| t)
    }
}
