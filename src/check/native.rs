use super::collect::Program;
use super::generics;
use crate::ast::{ForeignItem, ItemKind};
use crate::def::{self, DefId};
use crate::diag::Diag;
use crate::driver::graph::Namespace;
use crate::native::NativeTarget;
use crate::resolve::imports::ns_index;
use crate::ty::{
    self,
    defs::{DefData, DefKind, SigData, Vis},
};

/// Runs after aliases resolve, before any function bodies are checked.
/// The driver separately admits the requested target/backend before
/// collection; direct collect callers use the host's TinyCC target.
pub(super) fn collect_declarations(p: &mut Program, errs: &mut Vec<Diag>) {
    let ast = p.ast.clone();
    for item in &ast.items {
        let ItemKind::ExternBlock(block) = &item.kind else { continue };
        let target = match NativeTarget::select(crate::protocol::host_triple(), false, block.span) {
            Ok(target) => target,
            Err(diag) => {
                errs.push(diag);
                continue;
            }
        };
        for item in &block.items {
            let ForeignItem::Fn(f) = item else { continue };
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            let scope = generics::Scope::default();
            let signature = (|| {
                let mut params = Vec::with_capacity(f.params.len());
                for param in &f.params {
                    params.push(generics::resolve_scoped(&ast, &p.interner, &p.known, &cx, &mut p.tys, param.ty, &scope)?);
                }
                let ret = match f.ret {
                    Some(t) => generics::resolve_scoped(&ast, &p.interner, &p.known, &cx, &mut p.tys, t, &scope)?,
                    None => ty::UNIT,
                };
                Ok::<_, Diag>((params, ret))
            })();
            let (params, ret) = match signature {
                Ok(sig) => sig,
                Err(diag) => {
                    errs.push(diag);
                    continue;
                }
            };
            let def = p.resolved.as_ref().and_then(|t| t.flat[ns_index(Namespace::Value)].get(&f.name)).copied().unwrap_or_else(|| DefId {
                krate: p.krate,
                hash: def::item_hash(p.stable_crate, &[], def::DefKind::ForeignFn, p.interner.get(f.name), 0),
            });
            let symbol = p.resolved.as_ref().and_then(|t| t.native_symbols.get(&def)).copied().unwrap_or(f.name);
            match p.native.register(def, p.interner.get(symbol), &params, ret, &p.tys, target, f.name_span) {
                Ok(id) => {
                    p.native_names.insert(f.name, id);
                    let mut data = DefData::skeleton(DefKind::ForeignFn, None, f.name, Vis::Priv, f.name_span);
                    data.sig = SigData::Fn { params, ret };
                    p.defs.insert(def, data);
                }
                Err(diag) => errs.push(diag),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::FileId;
    use crate::intern::{Interner, Known};
    use crate::{check, lexer, parser};
    use crate::ty::{Mut, TyIntern, TyKind};
    use std::sync::Arc;

    fn collect(src: &str, walk: bool) -> Result<Program, Vec<Diag>> {
        let interner = Arc::new(Interner::default());
        let known = Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = def::CrateIds { local: def::LOCAL_CRATE, stable: def::synthetic_crate_hash("native-pointers.rs", false) };
        check::collect::collect_mode(Arc::new(ast), interner, known, ids, walk)
    }

    fn errors(src: &str, walk: bool) -> Vec<Diag> {
        match collect(src, walk) {
            Err(errors) => errors,
            Ok(p) => {
                let mut errors = Vec::new();
                for i in 0..p.fns.len() {
                    errors.extend(check::check_fn(&p, def::LocalDefId(i as u32)).1);
                }
                errors
            }
        }
    }

    #[test]
    fn aliases_keep_semantic_pointer_signatures_and_normal_coercions() {
        let src = r#"
type Byte = u8;
type Buffer = *mut Byte;
unsafe extern "C" {
    fn native_read(value: *const Byte) -> *const Byte;
    fn native_write(value: Buffer) -> Buffer;
}
fn main() {
    let mut byte = 0u8;
    unsafe {
        let p: Buffer = native_write(&mut byte);
        let q: *const Byte = native_read(p);
        let r: *const Byte = native_read(&byte);
        assert!(q == r);
    }
}
"#;
        for walk in [false, true] {
            let p = collect(src, walk).unwrap_or_else(|errors| panic!("{errors:?}"));
            assert_eq!(p.fns.len(), 1, "native declarations have no Lust bodies");
            let (checked, diagnostics) = check::check_fn(&p, p.main.unwrap());
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
            for name in ["native_read", "native_write"] {
                let id = p.native_names[&p.interner.intern(name)];
                let native = p.native.get(id);
                let mut reads = crate::driver::graph::Reads::new();
                let sig = p.sig_of(&mut reads, native.def());
                // DefData remains the source semantic signature, including aliases.
                let crate::driver::graph::SigOf::Other(data) = sig else { panic!("native DefData missing") };
                let SigData::Fn { params, ret } = &data.sig else { panic!("native signature missing") };
                let mutable = name == "native_write";
                let expected = TyKind::RawPtr(if mutable { Mut::Mut } else { Mut::Shared }, ty::int(ty::IntTy::U8));
                assert_eq!(params.len(), 1);
                assert_eq!(p.tys.kind(params[0]), expected);
                assert_eq!(p.tys.kind(*ret), expected);
                assert!(reads.recorded(&crate::driver::graph::ReadKey::Sig(native.def())).is_some());
                assert!(checked.reads.recorded(&crate::driver::graph::ReadKey::Sig(native.def())).is_some(),
                    "the caller must depend on the foreign signature: {name}");
            }
            assert!(errors(src, walk).is_empty());
        }
    }

    #[test]
    fn native_pointer_calls_keep_unsafe_arity_and_type_checks() {
        let declarations = r#"unsafe extern "C" {
    fn native_read(value: *const u8) -> *const u8;
    fn native_write(value: *mut u8) -> *mut u8;
}"#;
        for (body, expected) in [
            ("let x = 1u8; native_read(&x);", "L0404"),
            ("unsafe { native_read(); }", "L0105"),
            ("unsafe { native_read(0usize); }", "L0110"),
            ("let x = 1i32; unsafe { native_read(&x as *const i32); }", "L0110"),
            ("let x = 1u8; let p = &x as *const u8; unsafe { native_write(p); }", "L0110"),
            ("let x = 1u8; let p: *mut u8 = unsafe { native_read(&x) };", "L0110"),
        ] {
            let src = format!("{declarations}\nfn main() {{ {body} }}");
            for walk in [false, true] {
                let errors = errors(&src, walk);
                assert!(errors.iter().any(|e| e.code == expected), "{body}: {errors:?}");
            }
        }
    }

    #[test]
    fn unsupported_pointer_layouts_and_narrow_values_reject_during_collection() {
        for value in ["*const *const u8", "*mut Record", "*const [u8; 2]", "*const [u8]",
            "*const str", "*const ()", "*const bool", "*const char", "*const f32", "*mut i16",
            "*const u16", "*const i128", "*const u128", "*const &'static u8", "*const (u8, u8)",
            "i8", "u8"] {
            for return_value in [false, true] {
                let signature = if return_value { format!("fn native_bad() -> {value};") }
                    else { format!("fn native_bad(value: {value});") };
                let src = format!("struct Record {{ value: u8 }}\nunsafe extern \"C\" {{ {signature} }}\nfn main() {{}}");
                for walk in [false, true] {
                    match collect(&src, walk) {
                        Err(errors) => assert!(errors.iter().any(|e| e.code == "L0810"), "{value}: {errors:?}"),
                        Ok(_) => panic!("unsupported ABI admitted: {value}"),
                    }
                }
            }
        }
    }

    #[test]
    fn native_signature_reads_track_pointer_constness_pointee_and_returns() {
        let fingerprint = |param: &str, ret: &str| {
            let src = format!("unsafe extern \"C\" {{ fn native_pointer(p: {param}) -> {ret}; }}\nfn main() {{}}");
            let p = collect(&src, false).unwrap_or_else(|errors| panic!("{errors:?}"));
            let id = p.native_names[&p.interner.intern("native_pointer")];
            let def = p.native.get(id).def();
            let mut reads = crate::driver::graph::Reads::new();
            let _ = p.sig_of(&mut reads, def);
            reads.recorded(&crate::driver::graph::ReadKey::Sig(def)).unwrap().fingerprint
        };
        let base = fingerprint("*const u8", "*const u8");
        assert_eq!(base, fingerprint("*const u8", "*const u8"));
        for (param, ret) in [
            ("*mut u8", "*const u8"), ("*const i8", "*const u8"),
            ("*const i32", "*const u8"), ("*const u8", "*mut u8"),
            ("*const u8", "*const i8"), ("*const u8", "*const u32"),
        ] {
            assert_ne!(base, fingerprint(param, ret), "{param} -> {ret}");
        }
    }
}
