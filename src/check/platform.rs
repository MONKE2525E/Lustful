// Checks for the std platform crate's generic code (W-SHIM; the crate
// is library/std/src/platform.rs, loaded by the resolver).
//
// `io::Write::write_fmt` in lust formats the whole `write!` text first
// and writes it with one `write_all`. For std's own writers that is the
// output std gives, but std calls a writer's `write` once per format
// piece, so a user writer that counts or logs its `write` calls would
// see a different sequence. Materialize asks `user_write_fmt_instance`
// about every new instance; the default `write_fmt` for a user writer
// type rejects with L0641 instead of running with different behavior.
use crate::check::collect::Program;
use crate::def::LocalDefId;
use crate::diag::{Diag, Span};
use crate::ty::lang::ShippedCrate;
use crate::ty::{Ty, TyIntern, TyKind};

/// L0641 when `inst` is the default `io::Write::write_fmt` body of the
/// platform crate instantiated for a writer that std does not define.
/// The `&mut W` forwarding impl is not the default: its inner writer
/// gets its own instance, which this check sees.
pub fn user_write_fmt_instance(p: &Program, inst: LocalDefId) -> Option<Diag> {
    let f = p.fn_info(inst);
    if !is_platform_write_fmt(p, inst) {
        return None;
    }
    let TyKind::Ref(_, _, writer) = p.tys.kind(*f.params.first()?) else { return None };
    if matches!(p.tys.kind(writer), TyKind::Ref(..)) {
        return None;
    }
    user_writer_diag(p, &p.tys, writer, f.def.name_span)
}

/// The same rule at a `write!` call `lust check` sees, for a receiver
/// whose type is already concrete (`f` is the method the call picked,
/// `writer` the receiver with references peeled). Generic and `dyn`
/// receivers are left to `user_write_fmt_instance` in a build.
pub fn user_write_fmt_call(p: &Program, tys: &impl TyIntern, f: LocalDefId, writer: Ty, span: Span) -> Option<Diag> {
    if !is_platform_write_fmt(p, f) {
        return None;
    }
    user_writer_diag(p, tys, writer, span)
}

/// True for a `write_fmt` fn of the platform crate (the trait default,
/// the `&mut W` forwarder, or one of their instances).
fn is_platform_write_fmt(p: &Program, f: LocalDefId) -> bool {
    let info = p.fn_info(f);
    p.name(info.name) == "write_fmt" && p.shipped_crate_at(info.def.name_span) == Some(ShippedCrate::Std)
}

/// L0641 unless `writer` is a std writer: `Vec<u8>` or a type the
/// platform crate defines. Params and other non-Adt types say nothing.
fn user_writer_diag(p: &Program, tys: &impl TyIntern, writer: Ty, fallback: Span) -> Option<Diag> {
    if tys.vec_elem(writer).is_some() {
        return None;
    }
    let a = tys.local_adt(writer)?;
    if p.shipped_crate_at(p.adt(a).span) == Some(ShippedCrate::Std) {
        return None;
    }
    let span = if p.adt(a).span == Span::default() { fallback } else { p.adt(a).span };
    Some(Diag::new(
        "L0641",
        span,
        "`write!` into a user-defined `std::io::Write` type is not supported yet",
        "Format into a `String` with `format!`, then call `write_all` with its bytes.",
    ))
}
