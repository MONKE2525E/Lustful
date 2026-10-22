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
