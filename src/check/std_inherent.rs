// Rule zero against std items lust does not model (L0643).
//
// rustc's method probe walks the receiver's autoderef steps, and at each
// step probes by value, then `&`, then `&mut`. In one probe an inherent
// item beats a trait item, and two trait items are ambiguous (E0034).
// lust models only part of std, so a user trait's item could win in lust
// where std has an item of the same name that wins or ties in rustc
// (`v.spare_capacity_mut()` with a user trait method of that name: rustc
// calls Vec's). The other way, lust's builtin dispatch could answer where
// rustc picks the user trait first (`v.len()` with a by-value `fn
// len(self)` in a user trait for `Vec<u8>`: rustc's by-value probe finds
// the trait before Vec's `&self` len).
//
// `std_inherent.txt` (scripts/gen-std-inherent.py, from the rustdoc of std
// 1.99) lists what std gives each std type: its stable inherent items and
// the items of the std traits it implements, each with its receiver form.
// When an in-scope trait from outside std may apply to a std receiver
// step, `std_shadow_method` places both sides on rustc's probe order and
// says who wins; `std_shadow_path` does the same for `Type::item`, where
// every inherent item wins over every trait item.
use super::*;
use crate::ast::{ExprId, SelfKind};
use crate::def::DefId;
use crate::intern::FxMap;
use crate::traits::solve::Selection;
use std::sync::OnceLock;

/// Generated table: `<std type name> <letter><item> ...` per line (see the
/// generator for the letters).
static TABLE: &str = include_str!("std_inherent.txt");

/// Std type name to item name to receiver letters.
type Table = FxMap<&'static str, FxMap<&'static str, Vec<u8>>>;

fn table() -> &'static Table {
    static T: OnceLock<Table> = OnceLock::new();
    T.get_or_init(|| {
        let mut t = Table::default();
        for line in TABLE.lines() {
            let mut words = line.split(' ');
            let Some(ty) = words.next() else { continue };
            let items = t.entry(ty).or_default();
            for w in words {
                if let Some((&letter, name)) = w.as_bytes().split_first() {
                    items.entry(&w[1..1 + name.len()]).or_default().push(letter);
                }
            }
        }
        t
    })
}

/// The receiver letters std gives item `item` on the std type named `ty`.
fn std_letters(ty: &str, item: &str) -> &'static [u8] {
    table().get(ty).and_then(|m| m.get(item)).map_or(&[], |v| &v[..])
}

/// What the method probe order says about a call whose receiver chain
/// has a std type and a user trait candidate (see `std_shadow_method`).
pub(super) enum StdShadow {
    /// No user trait item may apply, or std has no item of the name.
    None,
    /// rustc picks the user trait's method: std's item comes later.
    UserFirst,
    /// rustc picks std's inherent item: a user trait may not be picked.
    StdFirst,
    /// A std trait's item comes first or ties, or the user's receiver
    /// cannot be placed: only the trait probe may answer, and only with a
    /// std trait (it reports a tie it sees itself).
    Tie,
    /// The order cannot be told: report L0643.
    Reject,
}

impl Ctx<'_, '_> {
    /// True when trait `d` is from outside std: the user's crates and the
    /// dependency adapters. Lang traits and std source traits are std.
    pub(super) fn is_user_trait(&self, d: DefId) -> bool {
        d.krate != crate::ty::BUILTIN_CRATE && !self.p.gx.index.trait_record(d).is_some_and(|r| self.std_span(r.span))
    }

    /// True for a span in std's own source (core, alloc, std): its calls
    /// were written against real std and its traits are std's.
    fn std_span(&self, span: Span) -> bool {
        use crate::ty::lang::ShippedCrate as K;
        self.p.std_source_span(span) || matches!(self.p.shipped_crate_at(span), Some(K::Core | K::Alloc | K::Std))
    }

    /// The table names of a std type: `u8`, `str`, `slice`, `Vec`, `Iter`
    /// (one name; an integer of unknown type gives both signs). Empty for
    /// every type that is not std's.
    fn std_type_names(&self, t: Ty) -> Vec<String> {
        let one = |s: &str| vec![s.to_string()];
        match self.tys.kind(t) {
            TyKind::Int(i) => one(i.name()),
            TyKind::Float(f) => one(f.name()),
            TyKind::Bool => one("bool"),
            TyKind::Char => one("char"),
            TyKind::Str => one("str"),
            TyKind::Slice(_) => one("slice"),
            TyKind::Array(..) => one("array"),
            // A reference or pointer step counts only over a std type:
            // std's impls for `&T` (`Iterator for &mut I`, `Display for
            // &T`) forward to `T`'s own, which a user type answers itself.
            TyKind::RawPtr(_, inner) if !self.std_type_names(inner).is_empty() => one("pointer"),
            TyKind::Ref(_, _, inner) if !self.std_type_names(inner).is_empty() => one("reference"),
            TyKind::FnPtr(_) => one("fn"),
            TyKind::Infer(v) if v.is_int() => vec!["i32".into(), "u32".into()],
            TyKind::Infer(v) if v.is_float() => vec!["f64".into(), "f32".into()],
            TyKind::Adt(..) => {
                let std = self.tys.builtin_of(t).is_some()
                    || self.tys.local_adt(t).is_some_and(|a| self.p.is_std_adt(a) || generics::is_std_adt(&self.tys, a));
                if !std {
                    return Vec::new();
                }
                // The printed path's last segment: `std::slice::Iter<u8>` is `Iter`.
                let shown = self.tn(t);
                let head = shown.split('<').next().unwrap_or("");
                one(head.rsplit("::").next().unwrap_or(head))
            }
            _ => Vec::new(),
        }
    }

    /// The receiver letters std gives `item` at type `t` (the union over
    /// its table names). Inference variables have no inherent candidates
    /// in rustc, so only their trait letters count.
    fn std_letters_at(&self, t: Ty, item: &str) -> Vec<u8> {
        let infer = matches!(self.tys.kind(t), TyKind::Infer(_));
        let mut out: Vec<u8> = Vec::new();
        for n in self.std_type_names(t) {
            out.extend(std_letters(&n, item).iter().filter(|l| !infer || l.is_ascii_uppercase()));
        }
        out
    }

    /// rustc's autoderef steps for a method probe from receiver type `rt`:
    /// references, `Box`, `Rc`, `Arc`, and guards, `Vec<T>` to `[T]`,
    /// `String` to `str`, then an array's unsizing to a slice.
    fn std_probe_steps(&mut self, rt: Ty) -> Vec<Ty> {
        let mut steps = Vec::new();
        let mut cur = self.resolve(rt);
        for _ in 0..16 {
            steps.push(cur);
            let next = match self.tys.kind(cur) {
                TyKind::Ref(_, _, inner) => Some(inner),
                _ => match self.tys.builtin_of(cur) {
                    Some(BuiltinTy::Vec) => self.tys.adt_first_ty_arg(cur).map(|el| self.tys.intern(TyKind::Slice(el))),
                    Some(BuiltinTy::String) => Some(self.tys.intern(TyKind::Str)),
                    _ => self.tys.smart_elem(cur),
                },
            };
            match next {
                Some(n) => cur = self.resolve(n),
                None => break,
            }
        }
        if let Some(&last) = steps.last()
            && let TyKind::Array(el, _) = self.tys.kind(last)
        {
            steps.push(self.tys.intern(TyKind::Slice(el)));
        }
        steps
    }

    /// True when trait `d` may hold with Self = `self_ty`: selection finds
    /// an impl or cannot rule one out (nested bounds are not proven, so
    /// this says yes more often than rustc). Nothing is kept.
    fn trait_may_apply(&mut self, d: DefId, self_ty: Ty) -> bool {
        let Some(n) = self.p.gx.index.trait_record(d).map(|r| r.generics.params.len()) else { return false };
        let snap = self.snapshot_vars();
        let obl_len = self.obl_len();
        let mut args = vec![GenericArg::Ty(self_ty)];
        for _ in 1..n {
            args.push(GenericArg::Ty(self.new_var(false)));
        }
        let args = self.tys.intern_args(&args);
        let sel = self.select_obligation(TraitRef { def: d, args, bindings: EMPTY_BINDINGS });
        self.rollback_vars(snap);
        self.obl_truncate(obl_len);
        !matches!(sel, Selection::NoImpl)
    }

    /// The in-scope traits from outside std that declare a method or
    /// associated fn `name`, each with the receiver form of that item.
    fn user_traits_with(&mut self, name: Sym) -> Vec<(DefId, Option<SelfKind>)> {
        let p = self.p;
        let Some(ds) = p.gx.traits_by_method.get(&name) else { return Vec::new() };
        let mut out = Vec::new();
        for &d in ds {
            if !self.is_user_trait(d) || !method::trait_in_scope_pub(self, d) {
                continue;
            }
            let Some(m) = p.gx.index.trait_record(d).and_then(|r| r.method_by_name(name)) else { continue };
            out.push((d, p.gx.trait_methods.get(&m).and_then(|t| t.self_kind)));
        }
        out
    }

    /// The first probe (3 per autoderef step: by value, `&`, `&mut`) whose
    /// receiver type is `recv`, if any step reaches it. References compare
    /// by mutability and pointee, not by region.
    fn probe_of_receiver(&self, steps: &[Ty], recv: Ty) -> Option<usize> {
        let same = |a: Ty, b: Ty| match (self.tys.kind(a), self.tys.kind(b)) {
            (TyKind::Ref(_, m1, x), TyKind::Ref(_, m2, y)) => m1 == m2 && x == y,
            _ => a == b,
        };
        let autoref = |s: Ty, m: Mut| matches!(self.tys.kind(recv), TyKind::Ref(_, rm, inner) if rm == m && inner == s);
        for (i, &s) in steps.iter().enumerate() {
            if same(s, recv) {
                return Some(3 * i);
            }
            if autoref(s, Mut::Shared) {
                return Some(3 * i + 1);
            }
            if autoref(s, Mut::Mut) {
                return Some(3 * i + 2);
            }
        }
        None
    }

    /// The earliest probe at which std's item of receiver letter `l` on
    /// step `j` can match (a `&self` item of `T` already matches at the
    /// by-value probe of a `&T` step before it). Typed receivers
    /// (`self: Box<Self>`) count from the first probe. None for an item
    /// without `self`, which is no method.
    fn std_probe(&self, steps: &[Ty], j: usize, l: u8) -> Option<usize> {
        let after_ref = j > 0 && matches!(self.tys.kind(steps[j - 1]), TyKind::Ref(..));
        match l.to_ascii_lowercase() {
            b'v' => Some(3 * j),
            b'r' if after_ref => Some(3 * (j - 1)),
            b'r' => Some(3 * j + 1),
            b'm' if after_ref => Some(3 * (j - 1)),
            b'm' => Some(3 * j + 2),
            b't' => Some(0),
            _ => None,
        }
    }

    /// Rule zero for `recv.name(..)` with receiver type `rt` (see the
    /// module comment): who wins in rustc's probe order. Instances skip
    /// it: the template check of the same body decided (rustc resolves a
    /// generic body's calls once).
    pub(super) fn std_shadow_method(&mut self, e: ExprId, rt: Ty, name: Sym, span: Span) -> StdShadow {
        if self.p.gx.instances.contains_key(&self.fid) || self.std_span(span) {
            return StdShadow::None;
        }
        let users = self.user_traits_with(name);
        if users.is_empty() {
            return StdShadow::None;
        }
        let mut steps = self.std_probe_steps(rt);
        // Through a user `Deref`, rustc's step is the target place itself.
        if self.user_deref_call == Some(e) && steps.len() > 1 && matches!(self.tys.kind(steps[0]), TyKind::Ref(..)) {
            steps.remove(0);
        }
        let item = self.name(name).to_string();
        // std's earliest inherent and trait probes.
        let (mut std_inh, mut std_tr): (Option<usize>, Option<usize>) = (None, None);
        for j in 0..steps.len() {
            for l in self.std_letters_at(steps[j], &item) {
                let Some(at) = self.std_probe(&steps, j, l) else { continue };
                let slot = if l.is_ascii_uppercase() { &mut std_tr } else { &mut std_inh };
                if slot.is_none_or(|s| at < s) {
                    *slot = Some(at);
                }
            }
        }
        if std_inh.is_none() && std_tr.is_none() {
            return StdShadow::None;
        }
        // The user side's earliest probe. A candidate's receiver is
        // `form(Self)`, and a probe takes it only when that is a step, `&`
        // a step, or `&mut` a step, so Self is a step or a reference to one.
        // A typed receiver (`self: Rc<Self>`) is not placed: `unplaced`.
        let mut user: Option<usize> = None;
        let mut unplaced = false;
        for &(d, kind) in &users {
            if kind.is_none() {
                continue; // An associated fn is no method candidate.
            }
            for j in 0..steps.len() {
                let s = steps[j];
                for self_ty in [s, self.tys.mk_ref(false, s), self.tys.mk_ref(true, s)] {
                    if !self.trait_may_apply(d, self_ty) {
                        continue;
                    }
                    let recv = match kind {
                        Some(SelfKind::Value) => self_ty,
                        Some(SelfKind::Ref) => self.tys.mk_ref(false, self_ty),
                        Some(SelfKind::RefMut) => self.tys.mk_ref(true, self_ty),
                        _ => {
                            unplaced = true;
                            continue;
                        }
                    };
                    if let Some(at) = self.probe_of_receiver(&steps, recv) {
                        user = Some(user.map_or(at, |u| u.min(at)));
                    }
                }
            }
        }
        if unplaced {
            return if std_inh.is_some() { StdShadow::Reject } else { StdShadow::Tie };
        }
        let Some(user) = user else { return StdShadow::None };
        // In one probe an inherent item wins; a std trait's item first or
        // at the user's probe is the trait probe's to decide.
        match (std_inh, std_tr) {
            (Some(i), t) if i <= user && t.is_none_or(|t| i <= t) => StdShadow::StdFirst,
            (_, Some(t)) if t <= user => StdShadow::Tie,
            _ => StdShadow::UserFirst,
        }
    }

    /// `std_shadow_method` at a method call `e` (receiver type `rt`, `base`
    /// after autoderef), acted on before the builtin dispatch: Some when
    /// the call is answered here (the user trait's pick, or L0643).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn std_shadow_call(
        &mut self,
        e: ExprId,
        rt: Ty,
        base: Ty,
        name: Sym,
        span: Span,
        args: &[ExprId],
        explicit: &[Option<GenericArg>],
        expected: Option<Ty>,
    ) -> Option<Ty> {
        let tie = match self.std_shadow_method(e, rt, name, span) {
            StdShadow::None => return None,
            StdShadow::StdFirst => {
                self.std_first.push(e);
                return None;
            }
            StdShadow::Reject => {
                self.report_std_shadow(base, name, false, span);
                for &a in args {
                    self.expr(a, None);
                }
                return Some(ERROR);
            }
            StdShadow::UserFirst => false,
            StdShadow::Tie => true,
        };
        // The builtin dispatch would answer with std's item, so the trait
        // probe runs first, alone. On a tie only a std trait's pick stands.
        self.last_pick = None;
        let hit = method::generic_method_search(self, e, rt, name, span, args, explicit, expected);
        match hit {
            method::Probe::Failed => return Some(ERROR),
            method::Probe::Hit(ret) if !tie || self.last_pick.is_some_and(|(pe, d)| pe == e && !self.is_user_trait(d)) => return Some(ret),
            _ => {}
        }
        self.report_std_shadow(base, name, false, span);
        if matches!(hit, method::Probe::Miss) {
            for &a in args {
                self.expr(a, None);
            }
        }
        Some(ERROR)
    }

    /// Rule zero for a type-relative path `Type::name` with no written
    /// trait, at Self type `base`: every std item of the name on a std
    /// type wins over (inherent) or ties with (trait) a user trait's item,
    /// so a user trait item that may apply there is L0643. True when
    /// reported. `consts` also counts user traits' associated consts.
    pub(super) fn std_shadow_path(&mut self, base: Ty, name: Sym, consts: bool, span: Span) -> bool {
        if self.p.gx.instances.contains_key(&self.fid) || self.std_span(span) {
            return false;
        }
        let base = self.resolve(base);
        let item = self.name(name).to_string();
        if self.std_letters_at(base, &item).is_empty() {
            return false;
        }
        let p = self.p;
        let mut users: Vec<DefId> = self.user_traits_with(name).into_iter().map(|(d, _)| d).collect();
        if consts {
            for &assoc in p.gx.trait_assoc_consts.keys() {
                let Some(t) = p.gx.index.trait_of_assoc(assoc) else { continue };
                if p.gx.index.trait_record(t).is_some_and(|r| r.assoc_items.iter().any(|&(d, n, _)| d == assoc && n == name))
                    && !users.contains(&t)
                    && self.is_user_trait(t)
                    && method::trait_in_scope_pub(self, t)
                {
                    users.push(t);
                }
            }
        }
        if users.into_iter().any(|d| self.trait_may_apply(d, base)) {
            self.report_std_shadow(base, name, true, span);
            return true;
        }
        false
    }

    /// The L0643 diagnostic: std's item `item` on `ty` and a user trait's
    /// item of that name, where lust cannot give rustc's pick.
    pub(super) fn report_std_shadow(&mut self, ty: Ty, item: Sym, path: bool, span: Span) {
        let (tn, item) = (self.tn(ty), self.name(item).to_string());
        let call = if path { format!("`<Type as Trait>::{item}`") } else { format!("`Trait::{item}(x)`") };
        self.err(
            "L0643",
            span,
            format!("std's `{item}` for `{tn}` may win over or tie with a trait item of that name here, and lust cannot decide it yet"),
            format!("Name the trait in the call, as in {call}, or rename the trait item."),
        );
    }
}
