// `#[track_caller]` and `std::panic::Location` (W-CHECK-G3).
//
// A fn with `#[track_caller]` takes one hidden trailing C parameter, the
// caller's packed panic location (`lust_loc`, cgen.rs `fn_sig`). Every
// direct call passes the location of the call, or, inside another
// `#[track_caller]` fn, the location that fn received; every panic
// location inside the fn's own body (`panic!`, `unwrap`, an index or an
// overflow check, `Location::caller()`) is the received one, as rustc
// reports them. A closure in such a fn reports its own locations.
//
// Only direct calls pass the location, so the fn may not become a value
// (a fn pointer, a `dyn Fn`, a generic `F: Fn` argument) and may not be a
// trait method (dyn calls); both are rejects (L0702), not guesses.
//
// `Location` is a synthetic std Adt (`generics::location_def`) of `file:
// &str, line: u32, column: u32` with core's Debug, Clone, Copy, PartialEq,
// and Eq; `Location::caller()` builds one from the packed location at run
// time (cgen `B::LocationCaller`), and `file`, `line`, `column`, and its
// Display read the fields.
use super::*;

/// True when `f` has `#[track_caller]`: its own attribute, or its
/// template's for an instance. A closure body fn never has it.
pub fn is_track_caller(p: &Program, f: LocalDefId) -> bool {
    // A closure body fn or a trait method stub borrows another fn's def.
    if p.gx.closure_fns.contains_key(&f) || matches!(p.gx.fn_class.get(f.0 as usize), Some(generics::FnClass::Stub)) {
        return false;
    }
    let info = p.fn_info(f);
    info.def.attrs.iter().any(|a| a.path.len() == 1 && p.name(a.path[0].name) == "track_caller")
}

/// The rejects for `#[track_caller]` uses lust does not support, and
/// rustc's own errors: on `main` (rustc E0648-style), on a trait method or
/// a trait impl method (L0702: dyn calls cannot pass the location).
pub fn check_attrs(p: &Program, errs: &mut Vec<Diag>) {
    for i in 0..p.fns.len() {
        let f = LocalDefId(i as u32);
        if !matches!(p.gx.fn_class.get(i), Some(generics::FnClass::Plain | generics::FnClass::Template)) || !is_track_caller(p, f) {
            continue;
        }
        // A trait method declaration (a default body) is a dyn entry too.
        if p.gx.trait_methods.contains_key(&p.def_id(f)) {
            errs.push(generics::dyn_not_yet(p.fn_info(f).def.name_span, "`#[track_caller]` on a trait method"));
            continue;
        }
        let def = p.fn_info(f).def;
        if p.name(def.name) == "main" && p.fn_info(f).owner.is_none() && def.self_param.is_none() && p.fn_names.get(&def.name) == Some(&f) {
            errs.push(Diag::new("L0110", def.name_span, "`main` function is not allowed to be `#[track_caller]`", "Remove the attribute."));
            continue;
        }
        if crate::borrowck::impl_trait_method(p, f).is_some() {
            errs.push(generics::dyn_not_yet(def.name_span, "`#[track_caller]` on a trait impl method"));
        }
    }
}

impl<'p, 'a> Ctx<'p, 'a> {
    /// Rejects a `#[track_caller]` fn used as a value (L0702): its calls
    /// would not pass the caller's location.
    pub(super) fn reject_track_caller_value(&mut self, f: LocalDefId, span: Span) {
        if is_track_caller(self.p, f) {
            self.errs.push(generics::dyn_not_yet(span, "a `#[track_caller]` fn as a value"));
        }
    }

    /// The methods of `std::panic::Location`: `file`, `line`, `column`.
    /// None when `base` is not `Location` or the name is not one of them.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn location_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        derefs: u8,
        name: Sym,
        span: Span,
        args: &[ExprId],
    ) -> Option<Ty> {
        use Builtin as B;
        if self.tys.adt_parts(base).map(|(d, _)| d) != Some(generics::location_def()) {
            return None;
        }
        let (b, ret) = match self.name(name) {
            "file" => (B::LocationFile, self.tys.mk_ref(false, STR)),
            "line" => (B::LocationLine, int(IntTy::U32)),
            "column" => (B::LocationColumn, int(IntTy::U32)),
            _ => return None,
        };
        self.check_packed_borrow(recv, span);
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref: Autoref::Ref });
        self.check_args(&[], args, span);
        Some(ret)
    }
}
