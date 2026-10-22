//! The supported native ABI. Foreign declarations never enter the Rust body
//! arena: their symbols and signatures have a separate identity and contract.
use crate::def::DefId;
use crate::diag::{Diag, Span};
use crate::intern::FxMap;
use crate::ty::{self, IntTy, Ty, TyIntern, TyKind};

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum NativeReturn {
    Void,
    Int(NativeInt),
}

impl NativeReturn {
    pub(crate) fn rust_ty(self) -> Ty {
        match self {
            Self::Void => ty::UNIT,
            Self::Int(int) => int.rust_ty(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct NativeSig {
    params: Vec<NativeInt>,
    ret: NativeReturn,
}

impl NativeSig {
    pub(crate) fn params(&self) -> &[NativeInt] {
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
            .map(|&t| NativeInt::from_ty(t, tys))
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| reject(span, "native parameters must be i32, u32, i64, u64, isize or usize"))?;
        let ret = if ret == ty::UNIT {
            NativeReturn::Void
        } else {
            NativeReturn::Int(NativeInt::from_ty(ret, tys).ok_or_else(|| reject(span, "native returns must be a supported integer or ()"))?)
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
    Diag::new("L0810", span, message, "Use the supported scalar native ABI; other foreign interfaces are not implemented.")
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
        assert_eq!(imports.get(first).sig().params(), &[NativeInt::I32]);
        assert_eq!(imports.get(first).sig().ret().rust_ty(), ty::I32);
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
        assert_eq!(imports.get(id).sig().params(), &kinds);
        assert_eq!(imports.get(id).sig().ret(), NativeReturn::Void);
        for (i, kind) in kinds.into_iter().enumerate() {
            let id = imports.register(def(i as u64 + 2), &format!("scalar_{i}"), &[], kind.rust_ty(), &tys, target(), span()).unwrap();
            assert_eq!(imports.get(id).sig().ret().rust_ty(), kind.rust_ty());
        }
    }

    #[test]
    fn unimplemented_abi_types_never_register() {
        let mut tys = GlobalTys::new();
        let pointer = tys.intern(TyKind::RawPtr(ty::Mut::Shared, ty::I32));
        for unsupported in [ty::UNIT, ty::BOOL, ty::CHAR, ty::STRING, ty::int(IntTy::I8), ty::int(IntTy::U128), pointer] {
            let mut imports = NativeImports::default();
            assert!(imports.register(def(1), "native_call", &[unsupported], ty::UNIT, &tys, target(), span()).is_err());
            assert_eq!(imports.by_def(def(1)), None);
            if unsupported != ty::UNIT {
                assert!(imports.register(def(1), "native_call", &[], unsupported, &tys, target(), span()).is_err());
            }
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
unsafe extern "C" {
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
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
