// Vtable materialization (docs/ARCH.md section 2.8; W-MONO).
//
// Mono builds one vtable per (concrete type, principal trait ref) that
// a checked body unsizes to: for each vtable method of the trait (the
// layout is `check::object::DynInfo`), the impl method selection picks
// for the concrete type, or the trait's default body instantiated at
// it, and one vtable per supertrait for the super slots. Instances
// these entries need are handed back to the materialize loop, which
// checks them like any other instance. Codegen reads the result
// (`GenTables::vtables`) to emit the vtable statics.
use crate::check::collect::Program;
use crate::check::generics::{instance_at, select_impl_global};
use crate::check::object::{self, VtableData};
use crate::def::LocalDefId;
use crate::ty::*;

/// Builds, ahead of any body check, the vtables of every non-generic
/// local impl of a trait that some `dyn` type in the source names as
/// its principal (or a supertrait of one). The body checks mono runs
/// at collect cannot see const and static items yet (the resolver
/// tables arrive after collect), so a coercion in such a body would
/// not ask for its vtable; this keeps the common case independent of
/// that. Generic and blanket impls still get their vtables from the
/// requests of checked bodies.
pub fn eager_vtables(p: &mut Program, made: &mut Vec<LocalDefId>) {
    let mut wanted: Vec<crate::def::DefId> = Vec::new();
    for t in &p.ast.tys {
        let crate::ast::TyExpr::Dyn { bounds, .. } = t else { continue };
        for b in bounds {
            if let crate::ast::TraitBound::Trait { trait_ref, .. } = b
                && let Some(seg) = trait_ref.path.last()
                && let Some(&def) = p.gx.trait_names.get(&seg.name)
                && !wanted.contains(&def)
            {
                wanted.push(def);
            }
        }
    }
    // Supertraits, for upcasts and supertrait calls.
    let mut i = 0;
    while i < wanted.len() {
        if let Some(info) = p.gx.dyn_infos.get(&wanted[i]) {
            for s in info.supers.clone() {
                if !wanted.contains(&s.def) {
                    wanted.push(s.def);
                }
            }
        }
        i += 1;
    }
    let mut pairs: Vec<(Ty, TraitRef)> = Vec::new();
    for (_, rec) in p.gx.index.all_impls() {
        if !rec.local || rec.synthetic != crate::traits::index::Synthetic::None || !rec.generics.params.is_empty() {
            continue;
        }
        if !wanted.contains(&rec.trait_def)
            || p.gx.dyn_infos.get(&rec.trait_def).is_none_or(|i| i.violation.is_some() || i.unsupported.is_some())
        {
            continue;
        }
        let self_ty = rec.self_ty(&p.tys);
        if p.tys.flags(self_ty).contains_param() || !crate::check::collect::is_sized_ty(&p.tys, self_ty) {
            continue;
        }
        pairs.push((self_ty, rec.trait_ref));
    }
    for (self_ty, tr) in pairs {
        let principal = TraitRef { bindings: EMPTY_BINDINGS, ..object::with_self(&mut p.tys, tr, DYN_SELF) };
        ensure_vtable(p, self_ty, principal, made);
    }
}

/// The vtable for `self_ty` (a concrete, sized type in the global
/// store) behind the existential `principal`, built on first use.
/// New fn instances go to `made`. None when no impl applies, which a
/// checked body never asks for.
pub fn ensure_vtable(p: &mut Program, self_ty: Ty, principal: TraitRef, made: &mut Vec<LocalDefId>) -> Option<u32> {
    if let Some(&id) = p.gx.vtable_by_key.get(&(self_ty, principal)) {
        return Some(id);
    }
    let info = p.gx.dyn_infos.get(&principal.def)?.clone();
    let tr = object::with_self(&mut p.tys, principal, self_ty);
    let (impl_id, impl_args) = select_impl_global(p, tr)?;
    let items = p.gx.index.get(impl_id).items.clone();
    let trait_args: Vec<GenericArg> = p.tys.args(tr.args).to_vec();
    let mut methods: Vec<LocalDefId> = Vec::with_capacity(info.methods.len());
    for m in &info.methods {
        let written = items.iter().copied().find_map(|d| p.local_def(d.hash).filter(|&l| p.fn_info(l).name == m.name));
        let f = match written {
            Some(l) => instance_at(p, l, &impl_args, made),
            // The trait's default body, instantiated at the full trait ref.
            None => {
                let default = p.local_def(m.def.hash)?;
                instance_at(p, default, &trait_args, made)
            }
        };
        methods.push(f);
    }
    let id = p.gx.vtables.len() as u32;
    p.gx.vtables.push(VtableData { self_ty, principal, methods, supers: Vec::new() });
    p.gx.vtable_by_key.insert((self_ty, principal), id);
    let pargs: Vec<GenericArg> = p.tys.args(principal.args).to_vec();
    let supers: Vec<TraitRef> = info.supers.iter().map(|s| crate::traits::index::subst_trait_ref_pub(&mut p.tys, *s, &pargs)).collect();
    let mut super_ids: Vec<u32> = Vec::with_capacity(supers.len());
    for s in supers {
        super_ids.push(ensure_vtable(p, self_ty, s, made)?);
    }
    p.gx.vtables[id as usize].supers = super_ids;
    Some(id)
}
