// Semantic types. Types are interned to a `Ty` (u32). Signature types live in a global table that is
// frozen after collection. Each function body adds its own types in a local overlay, so bodies can
// be checked in parallel with no locks.
use crate::intern::FxMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Ty(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AdtId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IntTy {
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
}

impl IntTy {
    pub const ALL: [IntTy; 10] =
        [IntTy::I8, IntTy::I16, IntTy::I32, IntTy::I64, IntTy::Isize, IntTy::U8, IntTy::U16, IntTy::U32, IntTy::U64, IntTy::Usize];
    pub fn signed(self) -> bool {
        matches!(self, IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::Isize)
    }
    pub fn bits(self) -> u32 {
        match self {
            IntTy::I8 | IntTy::U8 => 8,
            IntTy::I16 | IntTy::U16 => 16,
            IntTy::I32 | IntTy::U32 => 32,
            _ => 64,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            IntTy::I8 => "i8",
            IntTy::I16 => "i16",
            IntTy::I32 => "i32",
            IntTy::I64 => "i64",
            IntTy::Isize => "isize",
            IntTy::U8 => "u8",
            IntTy::U16 => "u16",
            IntTy::U32 => "u32",
            IntTy::U64 => "u64",
            IntTy::Usize => "usize",
        }
    }
    /// Largest value, as u64. Used for literal range checks.
    pub fn max(self) -> u64 {
        if self.signed() {
            (1u64 << (self.bits() - 1)) - 1
        } else if self.bits() == 64 {
            u64::MAX
        } else {
            (1u64 << self.bits()) - 1
        }
    }
    pub fn from_suffix(s: crate::lexer::IntSuffix) -> IntTy {
        use crate::lexer::IntSuffix as S;
        match s {
            S::I8 => IntTy::I8,
            S::I16 => IntTy::I16,
            S::I32 => IntTy::I32,
            S::I64 => IntTy::I64,
            S::Isize => IntTy::Isize,
            S::U8 => IntTy::U8,
            S::U16 => IntTy::U16,
            S::U32 => IntTy::U32,
            S::U64 => IntTy::U64,
            S::Usize => IntTy::Usize,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TyKind {
    /// Placeholder after an error. Unifies with anything, so one mistake gives one error.
    Error,
    Unit,
    Bool,
    Char,
    Str,
    String,
    Never,
    Int(IntTy),
    Vec(Ty),
    Option(Ty),
    Ref(bool, Ty),
    Adt(AdtId),
    /// `std::env::Args`.
    Args,
    /// `str::Chars`, the iterator from `s.chars()`. It borrows the string.
    Chars,
    /// An inference variable. `int` is true for integer literals with no type yet.
    Var(u32, bool),
}

pub const ERROR: Ty = Ty(0);
pub const UNIT: Ty = Ty(1);
pub const BOOL: Ty = Ty(2);
pub const CHAR: Ty = Ty(3);
pub const STR: Ty = Ty(4);
pub const STRING: Ty = Ty(5);
pub const NEVER: Ty = Ty(6);
pub const ARGS: Ty = Ty(7);
pub const REF_STR: Ty = Ty(8);
const FIRST_INT: u32 = 9;

pub fn int(t: IntTy) -> Ty {
    Ty(FIRST_INT + IntTy::ALL.iter().position(|&x| x == t).unwrap() as u32)
}
pub const I32: Ty = Ty(FIRST_INT + 2);
pub const USIZE: Ty = Ty(FIRST_INT + 9);

pub trait TyIntern {
    fn intern(&mut self, k: TyKind) -> Ty;
    fn kind(&self, t: Ty) -> TyKind;
}

#[derive(Default)]
pub struct GlobalTys {
    kinds: Vec<TyKind>,
    map: FxMap<TyKind, Ty>,
}

impl GlobalTys {
    pub fn new() -> GlobalTys {
        let mut g = GlobalTys::default();
        for k in [TyKind::Error, TyKind::Unit, TyKind::Bool, TyKind::Char, TyKind::Str, TyKind::String, TyKind::Never, TyKind::Args] {
            g.intern(k);
        }
        g.intern(TyKind::Ref(false, STR));
        for t in IntTy::ALL {
            g.intern(TyKind::Int(t));
        }
        g
    }
    pub fn len(&self) -> u32 {
        self.kinds.len() as u32
    }
    pub fn get(&self, k: TyKind) -> Option<Ty> {
        self.map.get(&k).copied()
    }
}

impl TyIntern for GlobalTys {
    fn intern(&mut self, k: TyKind) -> Ty {
        if let Some(&t) = self.map.get(&k) {
            return t;
        }
        let t = Ty(self.kinds.len() as u32);
        self.kinds.push(k);
        self.map.insert(k, t);
        t
    }
    fn kind(&self, t: Ty) -> TyKind {
        self.kinds[t.0 as usize]
    }
}

/// A function's view of the type table: the frozen global table plus local additions.
pub struct Tys<'g> {
    pub global: &'g GlobalTys,
    local: Vec<TyKind>,
    map: FxMap<TyKind, Ty>,
}

impl<'g> Tys<'g> {
    pub fn new(global: &'g GlobalTys) -> Tys<'g> {
        Tys { global, local: Vec::new(), map: FxMap::default() }
    }
}

impl TyIntern for Tys<'_> {
    fn intern(&mut self, k: TyKind) -> Ty {
        if let Some(&t) = self.global.map.get(&k) {
            return t;
        }
        if let Some(&t) = self.map.get(&k) {
            return t;
        }
        let t = Ty(self.global.len() + self.local.len() as u32);
        self.local.push(k);
        self.map.insert(k, t);
        t
    }
    fn kind(&self, t: Ty) -> TyKind {
        let g = self.global.len();
        if t.0 < g { self.global.kinds[t.0 as usize] } else { self.local[(t.0 - g) as usize] }
    }
}
