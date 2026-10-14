// Std iterator types named by path in a written type
// (`std::slice::Iter<'a, T>`, `std::vec::IntoIter<T>`,
// `std::iter::Map<I, fn(A) -> B>`, `std::str::Chars<'a>`). They are the
// builtin iterator Adts of `ty::iter`, so a value from `.iter()` and a
// written type agree. The type args lust adds after std's own (`Map`'s
// item `B`, `Copied`'s `T`) come from the written args: a `Map` or
// `FilterMap` function type must be a fn pointer, and an adapter's inner
// type must be a builtin iterator; other forms reject with L0641.
// In a region signature (`RegionMode::Keep`) the borrowing iterators
// (`slice::Iter`, `slice::IterMut`, `Chars`) carry their lifetime as the
// first arg, as user Adts do (the borrow checker reads one region slot
// for them, see `borrowck::regions::adt_regions`).
use crate::ast::{self, Ast, GenericArgs, PathSeg};
use crate::check::generics::{ResolveCx, Scope};
use crate::diag::{Diag, Span, not_yet};
use crate::intern::{Interner, Known};
use crate::ty::iter::{IterKind, item_ty, mk_iter};
use crate::ty::*;

/// The builtin iterator a std path names, or `Chars` (as None inside
/// Some). Paths use the std facade (`std::iter::Map`) or the crate that
/// defines the type (`core::slice::Iter`, `alloc::vec::IntoIter`).
pub fn iter_by_path(path: &[&str]) -> Option<Option<IterKind>> {
    let [krate, module, name] = path else { return None };
    if matches!((*krate, *module, *name), ("std" | "core", "str", "Chars")) {
        return Some(None);
    }
    IterKind::ALL.into_iter().find_map(|k| {
        let (kmod, kname) = k.path();
        let facade = if kmod.get(1) == Some(&"iter") { "iter" } else { kmod.get(1).copied().unwrap_or("") };
        (kname == *name && facade == *module && (*krate == "std" || *krate == kmod[0])).then_some(Some(k))
    })
}

/// Resolves a std iterator type path (`iter_by_path` matched it) with the
/// written args of its last segment.
#[allow(clippy::too_many_arguments)]
pub fn resolve_iter_path(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    kind: Option<IterKind>,
    seg: &PathSeg,
    span: Span,
) -> Result<Ty, Diag> {
    let shown = crate::intern::source_name(interner.get(seg.name)).to_string();
    let (mut ty_args, mut lts): (Vec<Ty>, Vec<ast::Lifetime>) = (Vec::new(), Vec::new());
    match &seg.args {
        GenericArgs::None => {}
        GenericArgs::Angle(args) => {
            for a in args {
                match a {
                    ast::GenericArg::Type(t) => {
                        ty_args.push(crate::check::generics::resolve_scoped(ast, interner, known, cx, tys, *t, scope)?)
                    }
                    ast::GenericArg::Lifetime(lt) => lts.push(*lt),
                    _ => {
                        return Err(Diag::new(
                            "L0110",
                            span,
                            format!("`{shown}` takes only type and lifetime arguments"),
                            "Remove the other arguments.",
                        ));
                    }
                }
            }
        }
        GenericArgs::Parenthesized { .. } => {
            return Err(Diag::new("L0110", span, "parenthesized arguments are only for Fn traits", "Use angle arguments."));
        }
    }
    let borrows = matches!(kind, None | Some(IterKind::SliceIter | IterKind::SliceIterMut | IterKind::VecDrain | IterKind::StringDrain));
    let n_lts = usize::from(borrows);
    if lts.len() > n_lts {
        return Err(Diag::new(
            "L0110",
            span,
            format!("`{shown}` takes {n_lts} lifetime argument(s), but {} were given", lts.len()),
            "Match the number of lifetime parameters in the definition.",
        ));
    }
    let want = kind.map_or(0, IterKind::shown_args);
    if ty_args.len() != want {
        return Err(Diag::new(
            "L0110",
            span,
            format!("`{shown}` takes {want} generic argument(s), but {} were given", ty_args.len()),
            "Match the number of parameters in the definition.",
        ));
    }
    // In a region signature the written args keep their regions; the
    // checks and the derived item args read their erased forms.
    let keep = matches!(scope.regions, crate::check::generics::RegionMode::Keep { .. });
    let mut erased_args: Vec<Ty> = Vec::with_capacity(ty_args.len());
    if keep {
        let erased_scope = scope.erased();
        if let GenericArgs::Angle(args) = &seg.args {
            for a in args {
                if let ast::GenericArg::Type(t) = a {
                    erased_args.push(crate::check::generics::resolve_scoped(ast, interner, known, cx, tys, *t, &erased_scope)?);
                }
            }
        }
    } else {
        erased_args.clone_from(&ty_args);
    }
    let unsupported = |what: &str| not_yet("L0641", span, &format!("`{shown}` {what}"));
    let (erased, extra) = match kind {
        None => (CHARS, Vec::new()),
        Some(k) => {
            // Adapters wrap a builtin iterator (their item and fields need it).
            if !matches!(
                k,
                IterKind::SliceIter
                    | IterKind::SliceIterMut
                    | IterKind::VecIntoIter
                    | IterKind::Range
                    | IterKind::RangeInclusive
                    | IterKind::VecDrain
                    | IterKind::StringDrain
                    | IterKind::RangeFrom
                    | IterKind::RangeTo
                    | IterKind::RangeFull
                    | IterKind::RangeToInclusive
            ) && !crate::ty::iter::is_iter(tys, erased_args[0])
            {
                return Err(unsupported("over a type that is not a std iterator lust knows"));
            }
            if (k.is_range() && k != IterKind::RangeFull) && !matches!(tys.kind(erased_args[0]), TyKind::Int(_)) {
                return Err(unsupported("over a type that is not an integer"));
            }
            if k == IterKind::Zip && !crate::ty::iter::is_iter(tys, erased_args[1]) {
                return Err(unsupported("over a type that is not a std iterator lust knows"));
            }
            let mut extra: Vec<Ty> = Vec::new();
            match k {
                IterKind::Map | IterKind::FilterMap => {
                    let TyKind::FnPtr(sig) = tys.kind(erased_args[1]) else {
                        return Err(unsupported("with a function type that is not a fn pointer"));
                    };
                    let s = tys.sig(sig).value;
                    let item = item_ty(tys, erased_args[0]);
                    if tys.tys_of(s.inputs).len() != 1 || item.is_none_or(|it| tys.tys_of(s.inputs)[0] != it) {
                        return Err(unsupported("with a fn pointer that does not take the inner item"));
                    }
                    let out = if k == IterKind::Map {
                        s.output
                    } else {
                        match tys.option_elem(s.output) {
                            Some(b) => b,
                            None => return Err(unsupported("with a fn pointer that does not return an `Option`")),
                        }
                    };
                    extra.push(out);
                }
                IterKind::Copied | IterKind::Cloned => {
                    let inner = item_ty(tys, erased_args[0]).and_then(|it| match tys.kind(it) {
                        TyKind::Ref(_, Mut::Shared, t) => Some(t),
                        _ => None,
                    });
                    match inner {
                        Some(t) => extra.push(t),
                        None => return Err(unsupported("over an iterator whose items are not shared references")),
                    }
                }
                _ => {}
            }
            let mut all = erased_args.clone();
            all.extend(extra.iter().copied());
            (mk_iter(tys, k, &all), extra)
        }
    };
    if !keep {
        return Ok(erased);
    }
    // The region signature form: the lifetime first (borrowing iterators
    // only), then the written args with their regions, then the derived ones.
    let (def, _) = tys.adt_parts(erased).expect("a builtin iterator is an Adt");
    let mut all: Vec<GenericArg> = Vec::new();
    if borrows {
        all.push(GenericArg::Lifetime(crate::check::generics::scope_region(interner, scope, lts.first().copied(), span)?));
    }
    all.extend(ty_args.iter().map(|&t| GenericArg::Ty(t)));
    all.extend(extra.iter().map(|&t| GenericArg::Ty(t)));
    Ok(tys.mk_adt(def, &all))
}
