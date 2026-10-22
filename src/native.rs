//! The supported native ABI. Foreign declarations never enter the Rust body
//! arena: their symbols and signatures have a separate identity and contract.
use crate::def::DefId;
use crate::diag::{Diag, Span};
use crate::intern::FxMap;
use crate::ty::{self, IntTy, Mut, Ty, TyIntern, TyKind};
use std::hash::{Hash, Hasher};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct NativeFnId(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum NativeInt {
    I32,
    U32,
    I64,
    U64,
    Isize,
    Usize,
}

impl NativeInt {
    pub(crate) fn rust_ty(self) -> Ty {
        ty::int(self.int_ty())
    }

    pub(crate) fn int_ty(self) -> IntTy {
        match self {
            Self::I32 => IntTy::I32,
            Self::U32 => IntTy::U32,
            Self::I64 => IntTy::I64,
            Self::U64 => IntTy::U64,
            Self::Isize => IntTy::Isize,
            Self::Usize => IntTy::Usize,
        }
    }

    fn from_ty(ty: Ty, tys: &impl TyIntern) -> Option<Self> {
        Some(match tys.kind(ty) {
            TyKind::Int(IntTy::I32) => Self::I32,
            TyKind::Int(IntTy::U32) => Self::U32,
            TyKind::Int(IntTy::I64) => Self::I64,
            TyKind::Int(IntTy::U64) => Self::U64,
            TyKind::Int(IntTy::Isize) => Self::Isize,
            TyKind::Int(IntTy::Usize) => Self::Usize,
            _ => return None,
        })
    }
}

/// Pointee admission is independent of by-value integer admission.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum NativePointee {
    I8,
    U8,
    I32,
    U32,
    I64,
    U64,
    Isize,
    Usize,
}

impl NativePointee {
    pub(crate) fn int_ty(self) -> IntTy {
        match self {
            Self::I8 => IntTy::I8,
            Self::U8 => IntTy::U8,
            Self::I32 => IntTy::I32,
            Self::U32 => IntTy::U32,
            Self::I64 => IntTy::I64,
            Self::U64 => IntTy::U64,
            Self::Isize => IntTy::Isize,
            Self::Usize => IntTy::Usize,
        }
    }

    fn from_ty(ty: Ty, tys: &impl TyIntern) -> Option<Self> {
        Some(match tys.kind(ty) {
            TyKind::Int(IntTy::I8) => Self::I8,
            TyKind::Int(IntTy::U8) => Self::U8,
            TyKind::Int(IntTy::I32) => Self::I32,
            TyKind::Int(IntTy::U32) => Self::U32,
            TyKind::Int(IntTy::I64) => Self::I64,
            TyKind::Int(IntTy::U64) => Self::U64,
            TyKind::Int(IntTy::Isize) => Self::Isize,
            TyKind::Int(IntTy::Usize) => Self::Usize,
            _ => return None,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum NativeValue {
    Int(NativeInt),
    Ptr { mutability: Mut, pointee: NativePointee },
}

impl NativeValue {
    pub(crate) fn rust_ty(self, tys: &mut impl TyIntern) -> Ty {
        match self {
            Self::Int(int) => int.rust_ty(),
            Self::Ptr { mutability, pointee } => tys.intern(TyKind::RawPtr(mutability, ty::int(pointee.int_ty()))),
        }
    }

    fn from_ty(ty: Ty, tys: &impl TyIntern) -> Option<Self> {
        match tys.kind(ty) {
            TyKind::RawPtr(mutability, inner) => Some(Self::Ptr { mutability, pointee: NativePointee::from_ty(inner, tys)? }),
            _ => NativeInt::from_ty(ty, tys).map(Self::Int),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum NativeReturn {
    Void,
    Value(NativeValue),
}

impl NativeReturn {
    pub(crate) fn rust_ty(self, tys: &mut impl TyIntern) -> Ty {
        match self {
            Self::Void => ty::UNIT,
            Self::Value(value) => value.rust_ty(tys),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NativeSig {
    params: Vec<NativeValue>,
    ret: NativeReturn,
}

impl Hash for NativeSig {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Both graph signature reads and cached native-call IR hash this.
        // Invalidate the old scalar-only schema without storing Ty arena ids.
        "native-abi-v2".hash(state);
        self.params.hash(state);
        self.ret.hash(state);
    }
}

impl NativeSig {
    pub(crate) fn params(&self) -> &[NativeValue] {
        &self.params
    }
    pub(crate) fn ret(&self) -> NativeReturn {
        self.ret
    }
}

/// Constructed from the requested target and backend, never the host alone.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct NativeTarget(());

impl NativeTarget {
    pub(crate) fn select(triple: &str, c_backend: bool, span: Span) -> Result<Self, Diag> {
        if triple == "x86_64-unknown-linux-gnu" && !c_backend {
            Ok(Self(()))
        } else {
            Err(reject(span, "native imports currently require Linux x86_64 GNU with TinyCC"))
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct NativeFn {
    def: DefId,
    symbol: String,
    sig: NativeSig,
}

impl NativeFn {
    pub(crate) fn def(&self) -> DefId {
        self.def
    }
    pub(crate) fn symbol(&self) -> &str {
        &self.symbol
    }
    pub(crate) fn sig(&self) -> &NativeSig {
        &self.sig
    }
}

#[derive(Default)]
pub(crate) struct NativeImports {
    entries: Vec<NativeFn>,
    by_def: FxMap<DefId, NativeFnId>,
    by_symbol: FxMap<String, NativeFnId>,
}

impl NativeImports {
    pub(crate) fn register(
        &mut self,
        def: DefId,
        symbol: &str,
        params: &[Ty],
        ret: Ty,
        tys: &impl TyIntern,
        _target: NativeTarget,
        span: Span,
    ) -> Result<NativeFnId, Diag> {
        if !valid_symbol(symbol) {
            return Err(reject(span, "native symbol is not an available C identifier"));
        }
        let params = params
            .iter()
            .map(|&t| NativeValue::from_ty(t, tys))
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| reject(span, "native parameters must be supported integers or thin pointers to i8, u8, i32, u32, i64, u64, isize or usize"))?;
        let ret = if ret == ty::UNIT {
            NativeReturn::Void
        } else {
            NativeReturn::Value(NativeValue::from_ty(ret, tys).ok_or_else(|| reject(span, "native returns must be a supported integer, primitive thin pointer or ()"))?)
        };
        let sig = NativeSig { params, ret };
        if let Some(id) = self.by_def.get(&def).copied() {
            let previous = self.get(id);
            return if previous.symbol == symbol && previous.sig == sig {
                Ok(id)
            } else {
                Err(reject(span, "one native definition has conflicting declarations"))
            };
        }
        if let Some(id) = self.by_symbol.get(symbol) {
            if self.get(*id).sig != sig {
                return Err(reject(span, "native symbol has conflicting signatures"));
            }
        }
        let id = NativeFnId(self.entries.len().try_into().expect("native import arena overflow"));
        self.entries.push(NativeFn { def, symbol: symbol.to_owned(), sig });
        self.by_def.insert(def, id);
        self.by_symbol.entry(symbol.to_owned()).or_insert(id);
        Ok(id)
    }

    pub(crate) fn get(&self, id: NativeFnId) -> &NativeFn {
        &self.entries[id.0 as usize]
    }
    pub(crate) fn by_def(&self, def: DefId) -> Option<NativeFnId> {
        self.by_def.get(&def).copied()
    }
}

fn reject(span: Span, message: &str) -> Diag {
    Diag::new("L0810", span, message, "Use supported scalar values or primitive thin pointers; other foreign interfaces are not implemented.")
}

fn valid_symbol(symbol: &str) -> bool {
    // Leading underscores belong to the C implementation; lust_* is private
    // to our runtime. Main is supplied by the executable entry point.
    let mut bytes = symbol.bytes();
    bytes.next().is_some_and(|b| b.is_ascii_alphabetic())
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
        && !symbol.starts_with("lust_")
        && !generated_symbol(symbol)
        && !matches!(
            symbol,
            "main"
                | "auto"
                | "break"
                | "case"
                | "char"
                | "const"
                | "continue"
                | "default"
                | "do"
                | "double"
                | "else"
                | "enum"
                | "extern"
                | "float"
                | "for"
                | "goto"
                | "if"
                | "inline"
                | "int"
                | "long"
                | "register"
                | "restrict"
                | "return"
                | "short"
                | "signed"
                | "sizeof"
                | "static"
                | "struct"
                | "switch"
                | "typedef"
                | "union"
                | "unsigned"
                | "void"
                | "volatile"
                | "while"
                | "alignas"
                | "alignof"
                | "bool"
                | "true"
                | "false"
                | "nullptr"
                | "static_assert"
                | "thread_local"
                | "typeof"
                | "typeof_unqual"
                | "constexpr"
        )
}

fn generated_symbol(symbol: &str) -> bool {
    // Generated type names start with a capital. Generated bodies and
    // glue occupy these prefixes in cold, base-library and overlay units.
    symbol.as_bytes()[0].is_ascii_uppercase()
        || ["f_", "tramp", "stramp", "disc_", "default_", "drop_", "clone_", "cmp_", "eq_", "hash_", "fmt_", "vt", "pk"]
            .iter()
            .any(|p| symbol.starts_with(p))
        || symbol.strip_prefix('f').is_some_and(|tail| !tail.is_empty() && tail.bytes().all(|b| b.is_ascii_digit()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::def::{CrateId, DefPathHash};
    use crate::diag::FileId;
    use crate::ty::GlobalTys;

    fn span() -> Span {
        Span::new(FileId(0), 0, 1)
    }
    fn def(n: u64) -> DefId {
        DefId { krate: CrateId(0), hash: DefPathHash(n) }
    }
    fn target() -> NativeTarget {
        NativeTarget::select("x86_64-unknown-linux-gnu", false, span()).unwrap()
    }

    #[test]
    fn declarations_keep_rust_identity_and_validate_one_external_signature() {
        let tys = GlobalTys::new();
        let mut imports = NativeImports::default();
        let first = imports.register(def(1), "abs", &[ty::I32], ty::I32, &tys, target(), span()).unwrap();
        assert_eq!(imports.by_def(def(1)), Some(first));
        assert_eq!(imports.get(first).def(), def(1));
        assert_eq!(imports.get(first).symbol(), "abs");
        assert_eq!(imports.get(first).sig().params(), &[NativeValue::Int(NativeInt::I32)]);
        assert_eq!(imports.get(first).sig().ret().rust_ty(&mut GlobalTys::new()), ty::I32);
        assert_eq!(imports.register(def(1), "abs", &[ty::I32], ty::I32, &tys, target(), span()).unwrap(), first);
        let alias = imports.register(def(2), "abs", &[ty::I32], ty::I32, &tys, target(), span()).unwrap();
        assert_ne!(alias, first);
        assert_eq!(imports.get(alias).def(), def(2));
        assert!(imports.register(def(3), "abs", &[ty::USIZE], ty::I32, &tys, target(), span()).is_err());
        assert!(imports.register(def(1), "other", &[ty::I32], ty::I32, &tys, target(), span()).is_err());
        assert_eq!(imports.by_def(def(3)), None);
    }

    #[test]
    fn abi_preserves_all_six_integer_kinds_and_void() {
        let tys = GlobalTys::new();
        let mut imports = NativeImports::default();
        let kinds = [NativeInt::I32, NativeInt::U32, NativeInt::I64, NativeInt::U64, NativeInt::Isize, NativeInt::Usize];
        let params: Vec<_> = kinds.iter().map(|k| k.rust_ty()).collect();
        let id = imports.register(def(1), "scalar_call", &params, ty::UNIT, &tys, target(), span()).unwrap();
        assert_eq!(imports.get(id).sig().params(), &kinds.map(NativeValue::Int));
        assert_eq!(imports.get(id).sig().ret(), NativeReturn::Void);
        for (i, kind) in kinds.into_iter().enumerate() {
            let id = imports.register(def(i as u64 + 2), &format!("scalar_{i}"), &[], kind.rust_ty(), &tys, target(), span()).unwrap();
            assert_eq!(imports.get(id).sig().ret().rust_ty(&mut GlobalTys::new()), kind.rust_ty());
        }
    }

    #[test]
    fn unimplemented_abi_types_never_register() {
        let tys = GlobalTys::new();
        for unsupported in [ty::UNIT, ty::BOOL, ty::CHAR, ty::STRING, ty::int(IntTy::I8), ty::int(IntTy::U8), ty::int(IntTy::U128)] {
            let mut imports = NativeImports::default();
            assert!(imports.register(def(1), "native_call", &[unsupported], ty::UNIT, &tys, target(), span()).is_err());
            assert_eq!(imports.by_def(def(1)), None);
            if unsupported != ty::UNIT {
                assert!(imports.register(def(1), "native_call", &[], unsupported, &tys, target(), span()).is_err());
            }
        }
    }

    #[test]
    fn primitive_pointers_round_trip_without_type_arena_identity() {
        let pointees = [NativePointee::I8, NativePointee::U8, NativePointee::I32, NativePointee::U32,
            NativePointee::I64, NativePointee::U64, NativePointee::Isize, NativePointee::Usize];
        let mut source = GlobalTys::new();
        let mut destination = GlobalTys::new();
        destination.intern(TyKind::RawPtr(Mut::Mut, ty::BOOL));
        let mut hashes = std::collections::HashSet::new();
        for (n, pointee) in pointees.into_iter().enumerate() {
            for (m, mutability) in [Mut::Shared, Mut::Mut].into_iter().enumerate() {
                let value = NativeValue::Ptr { mutability, pointee };
                let rust_ty = value.rust_ty(&mut source);
                let mut imports = NativeImports::default();
                let id = imports.register(def(1), "native_pointer", &[rust_ty], rust_ty, &source, target(), span()).unwrap();
                let sig = imports.get(id).sig();
                assert_eq!(sig.params(), &[value]);
                assert_eq!(sig.ret(), NativeReturn::Value(value));
                let restored = sig.ret().rust_ty(&mut destination);
                assert_eq!(destination.kind(restored), TyKind::RawPtr(mutability, ty::int(pointee.int_ty())));
                let mut h = crate::intern::FxHasher::default();
                sig.hash(&mut h);
                assert!(hashes.insert(h.finish()), "pointee and mutability must affect signature hashes: {n}/{m}");
            }
        }
        // A native ABI schema bump reaches both graph and IR hash consumers,
        // including unchanged scalar signatures from pre-pointer caches.
        let sig = NativeSig { params: vec![NativeValue::Int(NativeInt::I32)], ret: NativeReturn::Void };
        let mut current = crate::intern::FxHasher::default();
        sig.hash(&mut current);
        let mut old = crate::intern::FxHasher::default();
        vec![NativeInt::I32].hash(&mut old);
        NativeReturn::Void.hash(&mut old);
        assert_ne!(current.finish(), old.finish());
    }

    #[test]
    fn pointer_conflicts_are_exact_and_failed_registration_is_atomic() {
        let mut tys = GlobalTys::new();
        let shared = tys.intern(TyKind::RawPtr(Mut::Shared, ty::I32));
        let mutable = tys.intern(TyKind::RawPtr(Mut::Mut, ty::I32));
        let unsigned = tys.intern(TyKind::RawPtr(Mut::Shared, ty::int(ty::IntTy::U32)));
        let mut imports = NativeImports::default();
        let original = imports.register(def(1), "native_pointer", &[shared], shared, &tys, target(), span()).unwrap();
        for (params, ret) in [([mutable], shared), ([unsigned], shared), ([shared], mutable), ([shared], unsigned)] {
            assert!(imports.register(def(2), "native_pointer", &params, ret, &tys, target(), span()).is_err());
            assert!(imports.register(def(1), "native_pointer", &params, ret, &tys, target(), span()).is_err());
            assert_eq!(imports.by_def(def(2)), None);
            assert_eq!(imports.by_def(def(1)), Some(original));
        }
        let alias = imports.register(def(2), "native_pointer", &[shared], shared, &tys, target(), span()).unwrap();
        assert_ne!(original, alias);
        // A rejected return must not reserve either the definition or symbol.
        assert!(imports.register(def(3), "native_later", &[mutable], ty::BOOL, &tys, target(), span()).is_err());
        assert!(imports.register(def(3), "native_later", &[shared], shared, &tys, target(), span()).is_ok());
    }

    #[test]
    fn pointer_admission_is_closed_and_does_not_admit_narrow_values() {
        let mut tys = GlobalTys::new();
        let pointer = tys.intern(TyKind::RawPtr(Mut::Shared, ty::int(ty::IntTy::U8)));
        let reference = tys.intern(TyKind::Ref(ty::Region::Static, Mut::Shared, ty::int(ty::IntTy::U8)));
        let slice = tys.intern(TyKind::Slice(ty::int(ty::IntTy::U8)));
        let parameter = tys.intern(TyKind::Param(ty::ParamId(0)));
        let length = tys.intern_const(ty::ConstKind::Int(2));
        let array = tys.intern(TyKind::Array(ty::int(ty::IntTy::U8), length));
        let tuple_elements = tys.intern_tys(&[ty::int(ty::IntTy::U8), ty::int(ty::IntTy::U8)]);
        let tuple = tys.intern(TyKind::Tuple(tuple_elements));
        let record = tys.intern(TyKind::Adt(def(99), ty::EMPTY_ARGS));
        let signature = tys.intern_sig(ty::Binder::plain(ty::FnSig::plain(ty::EMPTY_TYS, ty::UNIT)));
        let function = tys.intern(TyKind::FnPtr(signature));
        let mut denied = vec![ty::UNIT, ty::BOOL, ty::CHAR, ty::STRING, pointer, reference, slice, parameter, array, tuple, record, function];
        denied.push(tys.intern(TyKind::Str));
        denied.push(tys.intern(TyKind::Float(ty::FloatTy::F32)));
        denied.push(tys.intern(TyKind::Float(ty::FloatTy::F64)));
        for int in IntTy::ALL {
            if NativePointee::from_ty(ty::int(int), &tys).is_none() {
                denied.push(ty::int(int));
            }
        }
        for inner in denied {
            for mutability in [Mut::Shared, Mut::Mut] {
                let pointer = tys.intern(TyKind::RawPtr(mutability, inner));
                let mut imports = NativeImports::default();
                assert!(imports.register(def(1), "native_pointer", &[ty::I32, pointer], ty::UNIT, &tys, target(), span()).is_err());
                assert!(imports.register(def(1), "native_pointer", &[], pointer, &tys, target(), span()).is_err());
                assert_eq!(imports.by_def(def(1)), None);
            }
        }
        for int in [IntTy::I8, IntTy::U8, IntTy::I16, IntTy::U16, IntTy::I128, IntTy::U128] {
            let mut imports = NativeImports::default();
            assert!(imports.register(def(1), "native_narrow", &[ty::int(int)], ty::UNIT, &tys, target(), span()).is_err());
            assert!(imports.register(def(1), "native_narrow", &[], ty::int(int), &tys, target(), span()).is_err());
        }
    }

    #[test]
    fn unsafe_symbol_spellings_and_runtime_collisions_are_rejected() {
        for symbol in ["", "a();evil", "a b", "9foo", "é", "_private", "lust_fns", "main", "int", "bool", "typedef", "nullptr"] {
            assert!(!valid_symbol(symbol), "{symbol}");
        }
        for symbol in ["abs", "getpid", "srand", "native_v2"] {
            assert!(valid_symbol(symbol));
        }
    }

    #[test]
    fn admission_uses_requested_target_and_backend() {
        assert!(NativeTarget::select("x86_64-unknown-linux-gnu", false, span()).is_ok());
        for triple in ["", "aarch64-unknown-linux-gnu", "x86_64-unknown-linux-musl", "x86_64-pc-windows-msvc"] {
            assert!(NativeTarget::select(triple, false, span()).is_err());
        }
        assert!(NativeTarget::select("x86_64-unknown-linux-gnu", true, span()).is_err());
    }
}

#[cfg(test)]
mod abi_tests {
    use crate::{cgen, check, def, diag, intern, lexer, lower, parser, tcc};
    use std::sync::Arc;

    #[test]
    fn native_abi_calls_c_peers_with_stack_arguments_and_full_width_values() {
        let src = r#"
type Byte = u8;
type Bytes = *mut Byte;
unsafe extern "C" {
    fn native_fill(value: Bytes, len: usize);
    fn native_sum(value: *const Byte, len: usize) -> u64;
    fn native_mix(a: i32, b: *const u8, c: i64, d: u64, e: isize, f: usize, g: *const u8, h: *mut u8) -> *const u8;
    fn native_write_i32(value: *mut i32);
    fn native_read_i32(value: *const i32) -> i32;
    fn native_write_i64(value: *mut i64);
    fn native_read_i64(value: *const i64) -> i64;
    fn native_i8c(value: *const i8) -> *const i8;
    fn native_i8m(value: *mut i8) -> *mut i8;
    fn native_u8c(value: *const u8) -> *const u8;
    fn native_u8m(value: *mut u8) -> *mut u8;
    fn native_i32c(value: *const i32) -> *const i32;
    fn native_i32m(value: *mut i32) -> *mut i32;
    fn native_u32c(value: *const u32) -> *const u32;
    fn native_u32m(value: *mut u32) -> *mut u32;
    fn native_i64c(value: *const i64) -> *const i64;
    fn native_i64m(value: *mut i64) -> *mut i64;
    fn native_u64c(value: *const u64) -> *const u64;
    fn native_u64m(value: *mut u64) -> *mut u64;
    fn native_isizec(value: *const isize) -> *const isize;
    fn native_isizem(value: *mut isize) -> *mut isize;
    fn native_usizec(value: *const usize) -> *const usize;
    fn native_usizem(value: *mut usize) -> *mut usize;
    fn native_eight(a: i32, b: u32, c: i64, d: u64, e: isize, f: usize, g: i32, h: u64) -> u64;
    fn native_unsigned() -> u32;
    fn native_set(value: u64);
    fn native_get() -> u64;
    fn native_step(value: i32) -> i32;
    fn native_order(a: i32, b: i32, c: i32, d: i32, e: i32, f: i32, g: i32, h: i32) -> i32;
    fn l0() -> i32;
}
fn main() {
    unsafe {
        assert_eq!(native_eight(-17, 0xfedcba98, -4294967297, 0xfedcba9876543210,
            -2147483649, usize::MAX - 5, -99, 0x876543210fedcba9), 0xfedcba9876543210);
        assert_eq!(native_unsigned(), 0xfedcba98);
        native_set(0xffffffffffabcdef);
        assert_eq!(native_get(), 0xffffffffffabcdef);
        assert_eq!(native_order(native_step(1), native_step(2), native_step(3), native_step(4),
            native_step(5), native_step(6), native_step(7), native_step(8)), 1);
        assert_eq!(l0(), 42);
        let mut guarded = [0xa5u8; 10];
        let ptr = &mut guarded[1] as *mut u8;
        native_fill(ptr, 8);
        assert_eq!(guarded[0], 0xa5);
        assert_eq!(guarded[9], 0xa5);
        for i in 0..8 { assert_eq!(guarded[i + 1], (i as u8) + 17); }
        assert_eq!(native_sum(ptr, 8), 164);
        native_fill(ptr, 0);
        assert_eq!(native_sum(ptr, 0), 0);
        assert_eq!(native_sum(ptr, 8), 164);
        native_fill(ptr, 8);
        assert_eq!(guarded[1], 17);
        assert_eq!(guarded[8], 24);
        // A prior effectful call is evaluated once before the C peer reads it.
        assert!(native_mix(native_step(9), ptr, -4294967297, 0xfedcba9876543210,
            -2147483649, usize::MAX - 5, ptr, ptr) == ptr as *const u8);
        assert_eq!(native_step(10), 10);
        let mut signed32 = [0i32; 1];
        native_write_i32(signed32.as_mut_ptr());
        assert_eq!(signed32[0], -1234567);
        assert_eq!(native_read_i32(signed32.as_ptr()), -1234567);
        let mut signed64 = [0i64; 1];
        native_write_i64(signed64.as_mut_ptr());
        assert_eq!(signed64[0], -4294967297);
        assert_eq!(native_read_i64(signed64.as_ptr()), -4294967297);
        let mut value_i8: i8 = -7;
        assert!(native_i8c(&value_i8) == &value_i8 as *const i8);
        let ptr_i8 = &mut value_i8 as *mut i8;
        assert!(native_i8m(ptr_i8) == ptr_i8);
        assert!(native_i8c(ptr_i8) == ptr_i8 as *const i8);
        assert!(native_i8c(0usize as *const i8).is_null());
        assert!(native_i8m(0usize as *mut i8).is_null());
        let mut value_u8: u8 = 249;
        assert!(native_u8c(&value_u8) == &value_u8 as *const u8);
        let ptr_u8 = &mut value_u8 as *mut u8;
        assert!(native_u8m(ptr_u8) == ptr_u8);
        assert!(native_u8c(ptr_u8) == ptr_u8 as *const u8);
        assert!(native_u8c(0usize as *const u8).is_null());
        assert!(native_u8m(0usize as *mut u8).is_null());
        let mut value_i32: i32 = -1234567;
        assert!(native_i32c(&value_i32) == &value_i32 as *const i32);
        let ptr_i32 = &mut value_i32 as *mut i32;
        assert!(native_i32m(ptr_i32) == ptr_i32);
        assert!(native_i32c(ptr_i32) == ptr_i32 as *const i32);
        assert!(native_i32c(0usize as *const i32).is_null());
        assert!(native_i32m(0usize as *mut i32).is_null());
        let mut value_u32: u32 = 0xfedcba98;
        assert!(native_u32c(&value_u32) == &value_u32 as *const u32);
        let ptr_u32 = &mut value_u32 as *mut u32;
        assert!(native_u32m(ptr_u32) == ptr_u32);
        assert!(native_u32c(ptr_u32) == ptr_u32 as *const u32);
        assert!(native_u32c(0usize as *const u32).is_null());
        assert!(native_u32m(0usize as *mut u32).is_null());
        let mut value_i64: i64 = -4294967297;
        assert!(native_i64c(&value_i64) == &value_i64 as *const i64);
        let ptr_i64 = &mut value_i64 as *mut i64;
        assert!(native_i64m(ptr_i64) == ptr_i64);
        assert!(native_i64c(ptr_i64) == ptr_i64 as *const i64);
        assert!(native_i64c(0usize as *const i64).is_null());
        assert!(native_i64m(0usize as *mut i64).is_null());
        let mut value_u64: u64 = 0xfedcba9876543210;
        assert!(native_u64c(&value_u64) == &value_u64 as *const u64);
        let ptr_u64 = &mut value_u64 as *mut u64;
        assert!(native_u64m(ptr_u64) == ptr_u64);
        assert!(native_u64c(ptr_u64) == ptr_u64 as *const u64);
        assert!(native_u64c(0usize as *const u64).is_null());
        assert!(native_u64m(0usize as *mut u64).is_null());
        let mut value_isize: isize = -2147483649;
        assert!(native_isizec(&value_isize) == &value_isize as *const isize);
        let ptr_isize = &mut value_isize as *mut isize;
        assert!(native_isizem(ptr_isize) == ptr_isize);
        assert!(native_isizec(ptr_isize) == ptr_isize as *const isize);
        assert!(native_isizec(0usize as *const isize).is_null());
        assert!(native_isizem(0usize as *mut isize).is_null());
        let mut value_usize: usize = usize::MAX - 5;
        assert!(native_usizec(&value_usize) == &value_usize as *const usize);
        let ptr_usize = &mut value_usize as *mut usize;
        assert!(native_usizem(ptr_usize) == ptr_usize);
        assert!(native_usizec(ptr_usize) == ptr_usize as *const usize);
        assert!(native_usizec(0usize as *const usize).is_null());
        assert!(native_usizem(0usize as *mut usize).is_null());
    }
    println!("native ABI peer: ok");
}
"#;
        let peer = r#"
#include <stdint.h>
#include <stddef.h>
uint64_t native_eight(int32_t a, uint32_t b, int64_t c, uint64_t d, intptr_t e, uintptr_t f, int32_t g, uint64_t h) {
    return a == -17 && b == UINT32_C(0xfedcba98) && c == -INT64_C(4294967297)
        && d == UINT64_C(0xfedcba9876543210) && e == -INT64_C(2147483649)
        && f == UINTPTR_MAX - 5 && g == -99 && h == UINT64_C(0x876543210fedcba9) ? d : 0;
}
uint32_t native_unsigned(void) { return UINT32_C(0xfedcba98); }
static uint64_t stored;
void native_set(uint64_t value) { stored = value; }
uint64_t native_get(void) { return stored; }
static int sequence;
int32_t native_step(int32_t value) { return ++sequence == value ? value : -1; }
int32_t native_order(int32_t a, int32_t b, int32_t c, int32_t d, int32_t e, int32_t f, int32_t g, int32_t h) {
    return a == 1 && b == 2 && c == 3 && d == 4 && e == 5 && f == 6 && g == 7 && h == 8;
}
int32_t l0(void) { return 42; }
void native_fill(uint8_t* value, uintptr_t len) {
    for (uintptr_t i = 0; i < len; ++i) value[i] = (uint8_t)(i + 17);
}
uint64_t native_sum(const uint8_t* value, uintptr_t len) {
    uint64_t sum = 0;
    for (uintptr_t i = 0; i < len; ++i) sum += value[i];
    return sum;
}
const uint8_t* native_mix(int32_t a, const uint8_t* b, int64_t c, uint64_t d,
    intptr_t e, uintptr_t f, const uint8_t* g, uint8_t* h) {
    return a == 9 && b == g && g == h && b[0] == 17 && h[7] == 24
        && c == -INT64_C(4294967297) && d == UINT64_C(0xfedcba9876543210)
        && e == -INT64_C(2147483649) && f == UINTPTR_MAX - 5 ? g : NULL;
}
void native_write_i32(int32_t* value) { *value = -1234567; }
int32_t native_read_i32(const int32_t* value) { return *value; }
void native_write_i64(int64_t* value) { *value = -INT64_C(4294967297); }
int64_t native_read_i64(const int64_t* value) { return *value; }
#define NATIVE_ID(name, type) \
    const type* native_##name##c(const type* value) { return value; } \
    type* native_##name##m(type* value) { return value; }
NATIVE_ID(i8, int8_t)
NATIVE_ID(u8, uint8_t)
NATIVE_ID(i32, int32_t)
NATIVE_ID(u32, uint32_t)
NATIVE_ID(i64, int64_t)
NATIVE_ID(u64, uint64_t)
NATIVE_ID(isize, intptr_t)
NATIVE_ID(usize, uintptr_t)
"#;
        let dir = std::env::temp_dir().join(format!("lust-native-abi-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let source = dir.join("peer.rs");
        let c_source = dir.join("peer.c");
        std::fs::write(&source, src).unwrap();
        std::fs::write(&c_source, peer).unwrap();
        let interner = Arc::new(intern::Interner::default());
        let known = Arc::new(intern::Known::new(&interner));
        let lexed = lexer::lex(src, diag::FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = def::CrateIds { local: def::LOCAL_CRATE, stable: def::synthetic_crate_hash("native-peer.rs", false) };
        let program = check::collect::collect(Arc::new(ast), interner, known, ids).unwrap();
        let mut map = diag::SourceMap::default();
        map.add_file("native-peer.rs", src);
        let n = program.fns.len();
        assert_eq!(n, 1, "foreign declarations have no Lust bodies or slots");
        let slots = vec![0];
        let main = program.main.unwrap();
        let (checked, errors) = check::check_fn(&program, main);
        assert!(errors.is_empty(), "{errors:?}");
        let body = lower::lower(&program, main, checked);
        let output = cgen::gen_fn(&program, &body, &map, 1, &slots);
        assert!(output.error.is_none(), "{:?}", output.error);
        for (name, ctype) in [("i8", "int8_t"), ("u8", "uint8_t"), ("i32", "int32_t"), ("u32", "uint32_t"),
            ("i64", "int64_t"), ("u64", "uint64_t"), ("isize", "intptr_t"), ("usize", "uintptr_t")] {
            for (suffix, qualifier) in [("c", "const "), ("m", "")] {
                let symbol = format!("native_{name}{suffix}");
                let decl = output.externs.iter().find(|e| e.contains(&format!("__asm__(\"{symbol}\")"))).unwrap();
                assert!(decl.starts_with(&format!("extern {qualifier}{ctype}* ")), "{decl}");
                assert!(decl.contains(&format!("({qualifier}{ctype}*)")), "{decl}");
            }
        }
        assert!(output.code_text().contains("((int8_t*)("), "const results convert to the internal pointer representation");
        let mut glue = cgen::GlueSet::default();
        glue.add(&program, &slots, output.glue.iter());
        let texts = [
            cgen::main_unit(0, &[], None),
            cgen::glue_unit(&program, &glue),
            cgen::runtime_unit(),
            cgen::table_unit(n, &[5]),
            cgen::loc_unit(&cgen::SlotFiles { paths: &["native-peer.rs"], of_slot: &[] }, &[1]),
            cgen::fn_unit(&program, &[output], &[0], &glue, "lust_register_u5", Some(0)),
        ];
        let units: Vec<_> = texts.into_iter().enumerate().map(|(i, text)| (dir.join(format!("u{i}.o")), text)).collect();
        tcc::compile_units(&units, false).unwrap();
        let expected = b"native ABI peer: ok\n";
        for (name, compiler) in [("system", std::path::PathBuf::from("cc")), ("tcc", tcc::tcc_paths().1)] {
            let object = dir.join(format!("{name}-peer.o"));
            let result = std::process::Command::new(compiler).args(["-c", "-o"]).arg(&object).arg(&c_source).output().unwrap();
            assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
            let mut objects: Vec<_> = units.iter().map(|(object, _)| object.clone()).collect();
            objects.push(object.clone());
            let executable = dir.join(format!("lust-{name}"));
            tcc::link(&objects, &executable, false).unwrap();
            let run = std::process::Command::new(executable).output().unwrap();
            assert!(run.status.success(), "{}", String::from_utf8_lossy(&run.stderr));
            assert_eq!(run.stdout, expected);
            // rustc is only the independent test oracle, never a Lust build step.
            let oracle = dir.join(format!("oracle-{name}"));
            let result = std::process::Command::new("rustc")
                .args(["--edition=2024", "-o"])
                .arg(&oracle)
                .arg(&source)
                .arg("-C")
                .arg(format!("link-arg={}", object.display()))
                .output()
                .unwrap();
            assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
            let run = std::process::Command::new(oracle).output().unwrap();
            assert!(run.status.success(), "{}", String::from_utf8_lossy(&run.stderr));
            assert_eq!(run.stdout, expected);
        }
        // Opt in: instrument these exact generated units and the C peer, not libc fixtures.
        if std::env::var_os("LUST_NATIVE_ABI_SANITIZE").as_deref() == Some(std::ffi::OsStr::new("1")) {
            let compiler = std::env::var_os("LUST_NATIVE_ABI_SANITIZE_CC").unwrap_or_else(|| "gcc".into());
            let mut sources = Vec::new();
            for (i, (_, text)) in units.iter().enumerate() {
                let path = dir.join(format!("san-u{i}.c"));
                std::fs::write(&path, text).unwrap();
                sources.push(path);
            }
            sources.push(c_source.clone());
            let executable = dir.join("lust-sanitized");
            // The system driver compiles AND links every unit with sanitizer support.
            // Keep the emitted C's aliasing/wrapping rules; use frames for diagnostics.
            let result = std::process::Command::new(&compiler)
                .args([
                    "-O1", "-g", "-std=gnu11", "-fsigned-char", "-fno-strict-aliasing", "-fwrapv",
                    "-fno-omit-frame-pointer", "-Werror=incompatible-pointer-types",
                    "-fsanitize=address,undefined", "-fno-sanitize-recover=undefined",
                ])
                .arg("-o")
                .arg(&executable)
                .args(&sources)
                .args(["-pthread", "-lm"])
                .output()
                .expect("cannot run native ABI sanitizer compiler");
            assert!(result.status.success(), "sanitizer compile/link ({}): {}", result.status,
                String::from_utf8_lossy(&result.stderr));
            let run = std::process::Command::new(&executable)
                .env("ASAN_OPTIONS", "detect_leaks=1:halt_on_error=1:allocator_may_return_null=1")
                .env("UBSAN_OPTIONS", "halt_on_error=1:print_stacktrace=1")
                .output()
                .expect("cannot run sanitized native ABI peer");
            assert!(run.status.success(), "sanitizer run ({}): {}", run.status, String::from_utf8_lossy(&run.stderr));
            assert_eq!(run.stdout, expected);
            assert!(run.stderr.is_empty(), "sanitizer stderr: {}", String::from_utf8_lossy(&run.stderr));
        }
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
