// Dependency graph nodes, read recording, and slot identity (docs/ARCH.md
// sections 4.2, 8.1, and 8.2; serial refactor S7).
//
// This file owns the frozen query surface of section 8.2: the `Reads` sink, its
// keys (`Binding`, `MethodSet`, `ImplSet`, `Sig`, `Layout`, `Checked`,
// `TraitInScope`), and the
// query functions on `Program` that log to it. Wave A packages (W-CORELANG,
// W-TRAITS-CORE, W-MACRO) code against these functions. Today's single-file,
// single-module resolver sits behind them; W-RESOLVE replaces that resolver
// with the module tree and import worklist of section 1.3 without changing any
// caller. S7 was record-only. W-DRIVER (wave A) turned reads into reuse
// for signature-only edits first; phase 2 extends the same walk to full
// mode: `Program::reads_dirty` below recomputes each recorded node's
// fingerprint in the new program, and compile.rs drops a recheck
// candidate only when its body is unchanged and every recorded read
// still matches. `Sig` fingerprints hash the layouts of named Adts
// deeply, and `Layout` has its own fingerprint, so type and impl edits
// dirty exactly the bodies that read through them.
//
// Fingerprints here hash normalized content only: name strings, stable def
// path hashes, and type structure. They never hash a `Sym`, a `Ty`, an
// `ArgsId`, or any other session-local id (section 8.1).
use crate::ast::SelfKind;
use crate::check::collect::{AdtDef, FnInfo, Program, VariantShape};
use crate::def::{DefId, DiskDefId, LocalDefId, StableCrateHash};
use crate::intern::{FxHasher, FxMap, Sym};
use crate::resolve::imports::{ResolvedTables, VisKind};
use crate::ty::defs::{DefData, DefKind as DefsKind, ModuleId, ROOT_MODULE};
use crate::ty::*;
use std::hash::{Hash, Hasher};

/// A node's 64-bit fingerprint over normalized content (section 8.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Fingerprint(pub u64);

/// One of Rust's three item namespaces (section 1.3). Modules live in `Type`.
/// Variant order is frozen; add nothing here.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Namespace {
    Type,
    Value,
    Macro,
}

/// The key of one `Binding` node: one name in one module and namespace.
/// Reads are per name, never per scope (section 8.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BindingKey {
    pub module: ModuleId,
    pub ns: Namespace,
    pub name: Sym,
}

/// The answer of a binding query. A tuple or unit struct answers in both the
/// type and the value namespace, with the Adt's own def: the constructor is not
/// a separate def (section 1.3). Local variables, primitives, and `Self` are
/// not module bindings and never appear here; callers resolve those scope
/// layers before they ask for a binding.
#[allow(dead_code)] // `Ambiguous` is produced by the glob worklist (W-RESOLVE).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingRes {
    Def(DefId),
    /// Two glob imports bring different defs under this name. An error only if
    /// code uses the name (section 1.3). Never produced by today's resolver.
    Ambiguous,
    Absent,
}

/// A receiver form probed by method resolution, in Rust's probe order
/// (section 2.10 step 2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ReceiverForm {
    Value,
    Ref,
    RefMut,
}

impl ReceiverForm {
    /// The probe order of section 2.10 step 2.
    pub const PROBE_ORDER: [ReceiverForm; 3] = [ReceiverForm::Value, ReceiverForm::Ref, ReceiverForm::RefMut];
}

/// The head of a receiver type: the part a method or impl bucket keys on.
/// References name their pointee head; the reference distinction rides in
/// `ReceiverForm`. `Unknown` is the head of a type with no bucket yet (an
/// unbound inference variable, a generic parameter): probes against it still
/// record a read, so a later impl or method rechecks the body.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Head {
    Adt(DefId),
    Int(IntTy),
    Float(FloatTy),
    Bool,
    Char,
    Str,
    Slice,
    Array,
    Tuple,
    Never,
    Unit,
    Unknown,
}

impl Head {
    /// The head of a type, through references and raw pointers.
    pub fn of(tys: &impl TyIntern, t: Ty) -> Head {
        match tys.kind(t) {
            TyKind::Adt(def, _) => Head::Adt(def),
            TyKind::Int(i) => Head::Int(i),
            TyKind::Float(f) => Head::Float(f),
            TyKind::Bool => Head::Bool,
            TyKind::Char => Head::Char,
            TyKind::Str => Head::Str,
            TyKind::Slice(_) => Head::Slice,
            TyKind::Array(..) => Head::Array,
            TyKind::Tuple(_) => Head::Tuple,
            TyKind::Never => Head::Never,
            TyKind::Unit => Head::Unit,
            TyKind::Ref(_, _, inner) | TyKind::RawPtr(_, inner) => Head::of(tys, inner),
            _ => Head::Unknown,
        }
    }
}

/// The key of one `MethodSet` node: the candidate set for one probe.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MethodSetKey {
    pub head: Head,
    pub name: Sym,
    pub form: ReceiverForm,
}

/// One method candidate. `trait_` is `None` for an inherent method.
/// `receiver` is `None` for an associated function without `self`: such a
/// candidate surfaces only in the `Value` probe, so the caller can report it
/// as "not a method" instead of "no such method". It is never callable as a
/// method.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MethodCandidate {
    pub def: DefId,
    pub receiver: Option<ReceiverForm>,
    pub trait_: Option<DefId>,
}

/// The candidate list of one method probe, in probe order (inherent first).
#[derive(Clone, Debug, Default)]
pub struct MethodSet {
    pub candidates: Vec<MethodCandidate>,
}

impl MethodSet {
    /// The first candidate. Method resolution iterates every
    /// candidate and unifies the receiver (section 2.10); this
    /// is for tests that inspect a set.
    #[cfg(test)]
    pub fn first(&self) -> Option<MethodCandidate> {
        self.candidates.first().copied()
    }
}

/// The key of one `ImplSet` node: the impl bucket for one trait and Self head.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ImplSetKey {
    pub trait_: DefId,
    pub head: Head,
}

/// The impl defs in one bucket, in no promised order. Only the impls of a
/// user trait (one written in this crate, with no associated const) fill
/// buckets: those impls are outside the trait-system key (driver/
/// gen_reuse.rs `trait_key`), so these reads are what rechecks a body when
/// one is added, removed, or edited. Any other trait's bucket reads as
/// empty; its impls stay under the trait-system key.
#[derive(Clone, Debug, Default)]
pub struct ImplSet {
    pub impls: Vec<DefId>,
}

/// One recorded read's key. Frozen (section 9.2): new node kinds go at the
/// end only.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ReadKey {
    Binding(BindingKey),
    MethodSet(MethodSetKey),
    ImplSet(ImplSetKey),
    Sig(DefId),
    Layout(DefId),
    /// A mono call edge to the checked body of a def (section 8.2).
    Checked(DefId),
    /// Whether a user trait is defined in or imported into one module,
    /// under any name (`as _` included): method probes ask it for each
    /// candidate trait. A `use` edit flips it without touching any
    /// binding the body names. The fingerprint is the answer.
    TraitInScope(ModuleId, DefId),
    /// The derive list of one local Adt template (PLAN R12): every
    /// `Program::derives_of` call inside a body check, and every selection
    /// of a derivable trait whose Self head is the Adt (a derived impl is a
    /// synthetic record, which no `ImplSet` read covers). The
    /// fingerprint is the list itself (`derives_fingerprint`).
    Derives(DefId),
    /// Some traits of the derive list of one local Adt template (sigedit
    /// P3.2): a reader that asked only those (`Program::derive_has`, a
    /// derivable trait's selection) records their bits
    /// (check/derive_delta.rs `bit`). The fingerprint is those flags.
    DeriveBits(DefId, u16),
}

/// One recorded read: the fingerprint the node had when it was read, and
/// whether the answer was "no such thing" (a failed lookup, a first-class
/// read per section 8.2 rule 3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Read {
    pub fingerprint: Fingerprint,
    pub failed: bool,
}

/// The read sink one stage run collects into (section 8.2). One sink per
/// checked body today; collect and mono get their own when their queries
/// land. Recording the same key twice in one run is a no-op: query answers
/// cannot change while the program tables are frozen for body checking.
#[derive(Clone, Debug, Default)]
pub struct Reads {
    map: FxMap<ReadKey, Read>,
    /// Set for a sink whose reads nobody will replay (a one-shot process
    /// exits after this compile): it records nothing and computes no
    /// fingerprints.
    off: bool,
    /// The identity the read index (`ReadIndex`) gave this set's content,
    /// or 0 when none: a new key resets it, so a changed set is indexed
    /// again.
    seal: u64,
    /// By mode (check, build), the generation of the kept program these
    /// reads last held against (`Program::verified`), or 0: the driver's
    /// keyed walk trusts a key a delta did not move only for a set of the
    /// delta's base program. A new set has none.
    pub(crate) verified: [u64; 2],
}

impl Reads {
    /// An empty sink.
    pub fn new() -> Reads {
        Reads::default()
    }

    /// A sink that records nothing (see `off`).
    pub fn off() -> Reads {
        Reads { map: FxMap::default(), off: true, seal: 0, verified: [0; 2] }
    }

    /// Records one read. The first record of a key wins.
    pub fn record(&mut self, key: ReadKey, fingerprint: Fingerprint, failed: bool) {
        if self.off {
            return;
        }
        if let std::collections::hash_map::Entry::Vacant(v) = self.map.entry(key) {
            v.insert(Read { fingerprint, failed });
            self.seal = 0;
        }
    }

    /// Records one read, computing the fingerprint only if the key is new:
    /// a body that asks the same question a hundred times pays for the
    /// fingerprint once.
    pub fn record_with(&mut self, key: ReadKey, failed: bool, fingerprint: impl FnOnce() -> Fingerprint) {
        if self.off {
            return;
        }
        if let std::collections::hash_map::Entry::Vacant(v) = self.map.entry(key) {
            v.insert(Read { fingerprint: fingerprint(), failed });
            self.seal = 0;
        }
    }

    /// Records a call edge to a checked body whose *body* (not only its
    /// signature) the reader's result depends on: today, a const fn body
    /// evaluated while checking a body (a const block, an array length).
    /// The fingerprint value does not matter yet: `read_fingerprint`
    /// cannot recompute a body fingerprint, so it reports a sentinel
    /// that never matches and the reader always rechecks when it is a
    /// walk candidate. Mono records the same key with a real body
    /// fingerprint when it lands (W-MONO, wave B).
    pub fn record_checked(&mut self, def: DefId, fingerprint: Fingerprint) {
        self.record(ReadKey::Checked(def), fingerprint, false);
    }

    /// The read recorded for a key, if this run read that node.
    #[allow(dead_code)] // Read by invalidation when it lands (W-DRIVER); tests use it now.
    pub fn get(&self, key: &ReadKey) -> Option<Read> {
        self.map.get(key).copied()
    }

    /// True if this run read that node.
    #[allow(dead_code)] // See `get`.
    pub fn contains(&self, key: &ReadKey) -> bool {
        self.map.contains_key(key)
    }

    /// Number of distinct nodes read.
    #[allow(dead_code)] // See `get`.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// True if nothing was read.
    #[allow(dead_code)] // See `get`.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Every recorded key, in hash order. For tests and debug dumps; the
    /// order is not stable, so nothing may key on it.
    #[allow(dead_code)] // See `get`.
    pub fn keys(&self) -> impl Iterator<Item = &ReadKey> {
        self.map.keys()
    }

    /// Every recorded (key, read) pair, in hash order. The dirty walk
    /// (`Program::reads_dirty`) iterates this; order does not matter there.
    pub fn iter(&self) -> impl Iterator<Item = (&ReadKey, &Read)> {
        self.map.iter()
    }
}

// ---------- Fingerprints ----------

/// The stable crate half a def hashes under in a fingerprint. Local-crate
/// defs use the program's stable crate hash and builtin defs use theirs, so
/// fingerprints match across sessions. A foreign session crate cannot occur
/// today (one crate per session); when W-RESOLVE loads more crates it gives
/// `Program` a crate table and this fallback goes away.
pub(crate) fn def_crate_hash(p: &Program, def: DefId) -> u64 {
    if def.krate == p.krate {
        p.stable_crate.0
    } else if def.krate == BUILTIN_CRATE {
        static BUILTIN: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
        *BUILTIN.get_or_init(|| crate::def::stable_crate_hash("lust-builtin-v1", "lib", "builtin", false).0)
    } else {
        def.krate.0 as u64
    }
}

/// Hashes one def by its stable identity: crate hash, then def path hash.
pub(crate) fn hash_def_pub(h: &mut FxHasher, p: &Program, def: DefId) {
    def_crate_hash(p, def).hash(h);
    def.hash.0.hash(h);
}

fn hash_region(h: &mut FxHasher, r: Region) {
    match r {
        Region::Static => 0u8.hash(h),
        Region::Param(i) => (1u8, i).hash(h),
        Region::Bound(i) => (2u8, i).hash(h),
        // Placeholders and region inference variables are proof-local and must
        // never reach a stored signature; hash only the form, never the id.
        Region::Placeholder(_) => 3u8.hash(h),
        Region::Infer(_) => 4u8.hash(h),
        Region::Erased => 5u8.hash(h),
    }
}

fn hash_const(h: &mut FxHasher, tys: &impl TyIntern, c: ConstId) {
    match tys.const_kind(c) {
        ConstKind::Int(v) => (0u8, v).hash(h),
        ConstKind::Bool(b) => (1u8, b).hash(h),
        ConstKind::Char(c) => (2u8, c).hash(h),
        ConstKind::Param(i) => (3u8, i).hash(h),
        ConstKind::Infer(_) => 4u8.hash(h),
    }
}

fn hash_args(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, args: ArgsId) {
    let list = tys.args(args);
    (list.len() as u64).hash(h);
    for a in list {
        match a {
            GenericArg::Ty(t) => {
                0u8.hash(h);
                hash_ty(h, p, tys, *t);
            }
            GenericArg::Lifetime(r) => {
                1u8.hash(h);
                hash_region(h, *r);
            }
            GenericArg::Const(c) => {
                2u8.hash(h);
                hash_const(h, tys, *c);
            }
        }
    }
}

fn hash_trait_ref(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, tr: &TraitRef) {
    hash_def_pub(h, p, tr.def);
    hash_args(h, p, tys, tr.args);
    let bindings = tys.bindings(tr.bindings);
    (bindings.len() as u64).hash(h);
    for (assoc, arg) in bindings {
        hash_def_pub(h, p, *assoc);
        match arg {
            GenericArg::Ty(t) => hash_ty(h, p, tys, *t),
            GenericArg::Lifetime(r) => hash_region(h, *r),
            GenericArg::Const(c) => hash_const(h, tys, *c),
        }
    }
}

/// Hashes one predicate: a bound, an associated type equality, or an
/// outlives fact, with defs in stable form.
fn hash_predicate(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, pred: &Predicate) {
    match pred {
        Predicate::Trait(b) => {
            (0u8, b.count).hash(h);
            hash_trait_ref(h, p, tys, &b.value);
        }
        Predicate::AssocEq(b) => {
            (1u8, b.count).hash(h);
            hash_def_pub(h, p, b.value.assoc);
            hash_args(h, p, tys, b.value.trait_args);
            hash_ty(h, p, tys, b.value.ty);
        }
        Predicate::Outlives(a, b) => {
            2u8.hash(h);
            hash_region(h, *a);
            hash_region(h, *b);
        }
        Predicate::TypeOutlives(t, r) => {
            3u8.hash(h);
            hash_ty(h, p, tys, *t);
            hash_region(h, *r);
        }
    }
}

/// Hashes one generics list: parameter kinds (names bind nothing a
/// reader sees) and predicates in source order.
fn hash_generics(h: &mut FxHasher, p: &Program, g: &Generics) {
    (g.params.len() as u64).hash(h);
    for param in &g.params {
        match param.kind {
            ParamKind::Lifetime => 0u8.hash(h),
            ParamKind::Type => 1u8.hash(h),
            ParamKind::Const(t) => {
                2u8.hash(h);
                hash_ty(h, p, &p.tys, t);
            }
        }
    }
    (g.predicates.len() as u64).hash(h);
    for pred in &g.predicates {
        hash_predicate(h, p, &p.tys, pred);
    }
}

/// Hashes one type by structure, with defs in stable form. This is the
/// in-memory fingerprint of section 8.1, not the 8.4 disk form: W-DRIVER owns
/// the disk translation and may reshape it. Kind tags follow `TyKind`
/// declaration order and change only when it grows at the end.
fn hash_ty(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, t: Ty) {
    match tys.kind(t) {
        TyKind::Error => 0u8.hash(h),
        TyKind::Unit => 1u8.hash(h),
        TyKind::Bool => 2u8.hash(h),
        TyKind::Char => 3u8.hash(h),
        TyKind::Never => 4u8.hash(h),
        TyKind::Int(i) => (5u8, i.name()).hash(h),
        TyKind::Float(f) => (6u8, f.name()).hash(h),
        TyKind::Str => 7u8.hash(h),
        TyKind::Ref(r, m, inner) => {
            8u8.hash(h);
            hash_region(h, r);
            m.is_mut().hash(h);
            hash_ty(h, p, tys, inner);
        }
        TyKind::RawPtr(m, inner) => {
            (9u8, m.is_mut()).hash(h);
            hash_ty(h, p, tys, inner);
        }
        TyKind::Slice(inner) => {
            10u8.hash(h);
            hash_ty(h, p, tys, inner);
        }
        TyKind::Array(inner, n) => {
            11u8.hash(h);
            hash_ty(h, p, tys, inner);
            hash_const(h, tys, n);
        }
        TyKind::Tuple(ts) => {
            12u8.hash(h);
            let list = tys.tys_of(ts);
            (list.len() as u64).hash(h);
            for e in list {
                hash_ty(h, p, tys, *e);
            }
        }
        TyKind::Adt(def, args) => {
            13u8.hash(h);
            hash_def_pub(h, p, def);
            hash_args(h, p, tys, args);
        }
        TyKind::FnPtr(sig) => {
            14u8.hash(h);
            let sig = tys.sig(sig);
            sig.count.hash(h);
            (sig.value.is_unsafe, sig.value.extern_c, sig.value.free_slots, sig.value.free_region).hash(h);
            for e in tys.tys_of(sig.value.inputs) {
                hash_ty(h, p, tys, *e);
            }
            hash_ty(h, p, tys, sig.value.output);
        }
        TyKind::FnDef(def, args) => {
            15u8.hash(h);
            hash_def_pub(h, p, def);
            hash_args(h, p, tys, args);
        }
        TyKind::Closure(def, args) => {
            16u8.hash(h);
            hash_def_pub(h, p, def);
            hash_args(h, p, tys, args);
        }
        TyKind::Dyn(bounds, r) => {
            17u8.hash(h);
            hash_region(h, r);
            let b = tys.dyn_bounds(bounds);
            match &b.principal {
                Some(pr) => {
                    pr.count.hash(h);
                    hash_trait_ref(h, p, tys, &pr.value);
                }
                None => u32::MAX.hash(h),
            }
            (b.supertraits.len() as u64).hash(h);
            for st in &b.supertraits {
                st.count.hash(h);
                hash_trait_ref(h, p, tys, &st.value);
            }
            (b.auto.send, b.auto.sync, b.auto.unpin).hash(h);
        }
        TyKind::Opaque(def, args) => {
            18u8.hash(h);
            hash_def_pub(h, p, def);
            hash_args(h, p, tys, args);
        }
        TyKind::Param(i) => (19u8, i.0).hash(h),
        TyKind::Projection(assoc, args) => {
            20u8.hash(h);
            hash_def_pub(h, p, assoc.0);
            hash_args(h, p, tys, args);
        }
        // A body-local inference variable has no stable content; signatures
        // never hold one. Hash only the integer-variable form.
        TyKind::Infer(v) => (21u8, v.is_int()).hash(h),
    }
}

/// The structural fingerprint of one type in this program's global store.
/// Mono's per-arg layout reads (section 8.2) are its first production user.
#[allow(dead_code)]
fn ty_fingerprint(p: &Program, t: Ty) -> Fingerprint {
    let mut h = FxHasher::default();
    hash_ty(&mut h, p, &p.tys, t);
    Fingerprint(h.finish())
}

/// Every Adt def named inside one type, in walk order (duplicates kept;
/// the caller dedups through its cycle stack). FnDef, Closure, Opaque,
/// and Projection defs are not Adt layouts and do not appear here: their
/// content is covered by their own `Sig` nodes when a body reads them.
fn collect_adt_defs(p: &Program, tys: &impl TyIntern, t: Ty, out: &mut Vec<DefId>) {
    fn args(p: &Program, tys: &impl TyIntern, a: ArgsId, out: &mut Vec<DefId>) {
        for a in tys.args(a) {
            if let GenericArg::Ty(t) = a {
                collect_adt_defs(p, tys, *t, out);
            }
        }
    }
    match tys.kind(t) {
        TyKind::Adt(def, a) => {
            out.push(def);
            args(p, tys, a, out);
        }
        TyKind::Ref(_, _, inner) | TyKind::RawPtr(_, inner) | TyKind::Slice(inner) | TyKind::Array(inner, _) => {
            collect_adt_defs(p, tys, inner, out)
        }
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts) {
                collect_adt_defs(p, tys, *e, out);
            }
        }
        TyKind::FnPtr(sig) => {
            let sig = tys.sig(sig);
            for e in tys.tys_of(sig.value.inputs) {
                collect_adt_defs(p, tys, *e, out);
            }
            collect_adt_defs(p, tys, sig.value.output, out);
        }
        TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => args(p, tys, a, out),
        TyKind::Dyn(bounds, _) => {
            let b = tys.dyn_bounds(bounds);
            let mut refs: Vec<&TraitRef> = b.principal.as_ref().map(|pr| &pr.value).into_iter().collect();
            refs.extend(b.supertraits.iter().map(|st| &st.value));
            for tr in refs {
                args(p, tys, tr.args, out);
                for (_, arg) in tys.bindings(tr.bindings) {
                    if let GenericArg::Ty(t) = arg {
                        collect_adt_defs(p, tys, *t, out);
                    }
                }
            }
        }
        _ => {}
    }
}

/// Which deep walk a memo entry belongs to: Adt layouts
/// (`hash_adt_layout`) or Adt regions (`hash_adt_regions`).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Deep {
    Layout,
    Regions,
}

/// The deep Adt fingerprints one fingerprint computation has made, so a
/// sub-type that many fields share is folded once (`adt_deep`). Callers
/// of `hash_ty_deep` make one per fingerprint and pass it along. The
/// program-wide `FpMemo` keeps the same values across computations.
/// The flag marks a fresh walk (`memo_check`): it neither reads nor
/// fills the program memo.
#[derive(Default)]
pub(crate) struct DeepMemo(FxMap<(Deep, DefId), u64>, bool);

/// The program-wide memo of deep Adt fingerprints, by `AdtId`. It is on
/// only while the program does not change: the driver turns it on after
/// collect and the std splice (`on`), and a kept program turns it off
/// before a patch edits it (`off`). Off, every fingerprint computation
/// still walks each Adt once (`DeepMemo`). Walks that fill it hold
/// `walk`: an Adt cycle publishes all its members before another walk
/// can see one of them, so no walk takes a member for a finished leaf.
///
/// Mono (`generics::materialize`) changes the program between body
/// checks, so there the memo follows it (`follow_begin`, `sync`): it is
/// on, and it starts empty again whenever `deep_stamp` moves.
#[derive(Default)]
pub struct FpMemo {
    layout: Vec<std::sync::OnceLock<u64>>,
    regions: Vec<std::sync::OnceLock<u64>>,
    walk: std::sync::Mutex<()>,
    /// While mono runs on a program whose memo was off: the
    /// `deep_stamp` the current values were made under.
    follow: Option<u64>,
}

impl FpMemo {
    /// Turns the memo on, empty, for a program with `adts` Adts.
    pub fn on(&mut self, adts: usize) {
        self.layout = (0..adts).map(|_| Default::default()).collect();
        self.regions = (0..adts).map(|_| Default::default()).collect();
    }

    /// Turns the memo off and drops its values.
    pub fn off(&mut self) {
        *self = FpMemo::default();
    }

    /// Starts following the program through mono when the memo is off
    /// (a collect); an on memo stays as its owner set it. `follow_end`
    /// turns a followed memo off again.
    pub(crate) fn follow_begin(&mut self) {
        if self.layout.is_empty() && self.regions.is_empty() {
            self.follow = Some(u64::MAX);
        }
    }

    /// `follow_begin` for a kept program delta (driver/kept_delta.rs,
    /// patch.rs): its body checks run after its edits, on a program that
    /// changes between them only as mono's does (`sync`). True when this
    /// call started following, so the caller ends it (`follow_end`).
    pub(crate) fn follow_scoped(&mut self) -> bool {
        let idle = self.follow.is_none() && self.layout.is_empty() && self.regions.is_empty();
        self.follow_begin();
        idle
    }

    pub(crate) fn follow_end(&mut self) {
        if self.follow.is_some() {
            self.off();
        }
    }

    /// Before each body check in mono: a followed memo drops its values
    /// when an input of the deep walk moved since they were made.
    pub(crate) fn sync(p: &mut Program) {
        if p.fp_memo.follow.is_none() {
            return;
        }
        let stamp = deep_stamp(p);
        if p.fp_memo.follow != Some(stamp) {
            p.fp_memo.on(p.adts.len());
            p.fp_memo.follow = Some(stamp);
        }
    }

    fn slot(&self, p: &Program, kind: Deep, def: DefId) -> Option<&std::sync::OnceLock<u64>> {
        let a = p.adt_by_def(def)?;
        match kind {
            Deep::Layout => self.layout.get(a.0 as usize),
            Deep::Regions => self.regions.get(a.0 as usize),
        }
    }
}

impl DeepMemo {
    fn get(&self, p: &Program, kind: Deep, def: DefId) -> Option<u64> {
        if let Some(&v) = self.0.get(&(kind, def)) {
            return Some(v);
        }
        if self.1 {
            return None;
        }
        let v = p.fp_memo.slot(p, kind, def).and_then(|s| s.get().copied())?;
        if memo_check() {
            let fresh = adt_deep(p, kind, def, &mut DeepMemo(FxMap::default(), true));
            assert_eq!(fresh, v, "internal: stale deep fingerprint memo for {def:?} (LUST_CHECK_FPMEMO)");
        }
        Some(v)
    }

    fn put(&mut self, p: &Program, kind: Deep, def: DefId, v: u64) {
        self.0.insert((kind, def), v);
        if !self.1
            && let Some(s) = p.fp_memo.slot(p, kind, def)
        {
            let _ = s.set(v);
        }
    }
}

/// LUST_CHECK_FPMEMO=1: every value the program memo gives is computed
/// again by a fresh walk, and a difference panics (test sweeps).
fn memo_check() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("LUST_CHECK_FPMEMO").is_some_and(|v| v == "1"))
}

/// A stamp of the tables the deep walk reads that mono can grow
/// (`hash_adt_layout`, `hash_adt_regions`): their sizes. Mono writes only
/// new instance rows of `Program::adts` (a def maps to its template row,
/// so a walk never reaches one) and adds entries to these tables; it
/// edits no entry in place, so equal sizes mean equal walk inputs.
fn deep_stamp(p: &Program) -> u64 {
    let gx = &p.gx;
    let mut h = FxHasher::default();
    (gx.glue_methods.len(), gx.written_hash.len(), gx.borrow_impls.len(), gx.dyn_keys.len(), gx.adt_lifetimes.len()).hash(&mut h);
    (gx.index.impls_of_trait(gx.lang.hasher).len(), gx.index.impls_of_trait(gx.lang.build_hasher).len()).hash(&mut h);
    (p.regions.adt_facts.len(), p.regions.adt_fields.len(), p.regions.adt_bounds.len()).hash(&mut h);
    h.finish()
}

/// Hashes one type shallowly (`hash_ty`), then calls `r` for every Adt
/// def it names, in walk order.
fn hash_ty_refs(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, t: Ty, r: &mut dyn FnMut(&mut FxHasher, DefId)) {
    hash_ty(h, p, tys, t);
    let mut defs = Vec::new();
    collect_adt_defs(p, tys, t, &mut defs);
    for def in defs {
        r(h, def);
    }
}

/// Hashes one type deeply: the shallow structure (`hash_ty`) plus the
/// deep layout fingerprint of every Adt it names (`adt_deep`), which
/// covers that Adt's layout and, transitively, every Adt its fields
/// name. A signature that mentions a type only by name must still
/// change when that type's fields, derives, or discriminants change,
/// because bodies checked against the signature read those facts
/// through the compat tables (field types, copy-ness, glue) without a
/// separate recorded read for each one.
pub(crate) fn hash_ty_deep(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, t: Ty, memo: &mut DeepMemo) {
    hash_ty_refs(h, p, tys, t, &mut |h, def| adt_deep(p, Deep::Layout, def, memo).hash(h));
}

/// The deep fingerprint of one Adt in one walk: its own content
/// (`hash_adt_layout` or `hash_adt_regions`), where each Adt it names
/// folds in as that Adt's deep fingerprint. Adts that name each other
/// in a cycle (one strongly connected component of the "names" graph)
/// fold each other by def only, and each one's fingerprint covers the
/// content of every member, sorted by stable def identity. So the
/// value is a pure function of the reachable content, the same in
/// every run and walk order, and the walk visits each Adt once.
fn adt_deep(p: &Program, kind: Deep, def: DefId, memo: &mut DeepMemo) -> u64 {
    if let Some(v) = memo.get(p, kind, def) {
        return v;
    }
    let _walk = (!memo.1 && !p.fp_memo.layout.is_empty()).then(|| p.fp_memo.walk.lock().unwrap_or_else(|e| e.into_inner()));
    if let Some(v) = memo.get(p, kind, def) {
        return v;
    }
    let mut scc = Scc { p, kind, order: FxMap::default(), stack: Vec::new() };
    scc.visit(def, memo);
    memo.get(p, kind, def).unwrap_or_default()
}

/// Folds one Adt's own content for walk `kind` into `h`; `r` folds each
/// Adt it names.
fn hash_adt_own(h: &mut FxHasher, p: &Program, kind: Deep, def: DefId, r: &mut dyn FnMut(&mut FxHasher, DefId)) {
    match kind {
        Deep::Layout => hash_adt_layout(h, p, def, r),
        Deep::Regions => hash_adt_regions(h, p, def, r),
    }
}

/// Tarjan's strongly connected components over the Adts one deep walk
/// reaches (`adt_deep`). `order` holds (visit index, low link) for each
/// def seen; a seen def without a memo value is still on `stack`.
struct Scc<'p> {
    p: &'p Program,
    kind: Deep,
    order: FxMap<DefId, (u32, u32)>,
    stack: Vec<DefId>,
}

impl Scc<'_> {
    fn visit(&mut self, v: DefId, memo: &mut DeepMemo) {
        let (p, kind) = (self.p, self.kind);
        let index = self.order.len() as u32;
        self.order.insert(v, (index, index));
        self.stack.push(v);
        let mut succ: Vec<DefId> = Vec::new();
        hash_adt_own(&mut FxHasher::default(), p, kind, v, &mut |_, d| {
            if !succ.contains(&d) {
                succ.push(d);
            }
        });
        for w in succ {
            if memo.get(p, kind, w).is_some() {
                continue;
            }
            let low = match self.order.get(&w) {
                Some(&(wi, _)) => wi,
                None => {
                    self.visit(w, memo);
                    self.order[&w].1
                }
            };
            let e = self.order.get_mut(&v).expect("visited");
            e.1 = e.1.min(low);
        }
        if self.order[&v].1 != index {
            return;
        }
        let at = self.stack.iter().rposition(|d| *d == v).expect("on stack");
        let mut members = self.stack.split_off(at);
        members.sort_unstable_by_key(|d| (def_crate_hash(p, *d), d.hash.0));
        let mut h = FxHasher::default();
        (if kind == Deep::Layout { "adt-deep-layout-v1" } else { "adt-deep-regions-v1" }).hash(&mut h);
        (members.len() as u64).hash(&mut h);
        for &m in &members {
            hash_adt_own(&mut h, p, kind, m, &mut |h, d| match members.contains(&d) {
                true => {
                    "scc-member".hash(h);
                    hash_def_pub(h, p, d);
                }
                false => memo.get(p, kind, d).unwrap_or_default().hash(h),
            });
        }
        let scc = h.finish();
        for &m in &members {
            let mut h = FxHasher::default();
            scc.hash(&mut h);
            hash_def_pub(&mut h, p, m);
            memo.put(p, kind, m, h.finish());
        }
    }
}

/// Folds one Adt's layout-relevant content into `h`: enum-ness, repr,
/// derives (every derived trait and the `#[default]` variant change
/// what checking and codegen do with a value, so they are part of this
/// fingerprint, not only of `Sig`), and per variant its name, shape, discriminant, and
/// field names and field types; `r` folds each Adt a type names (see
/// `adt_deep`). Builtin Adts (String, Vec, Option)
/// and unknown defs fold their def hash only: their layout is fixed by
/// the compiler, never by a user edit.
fn hash_adt_layout(h: &mut FxHasher, p: &Program, def: DefId, r: &mut dyn FnMut(&mut FxHasher, DefId)) {
    "adt-layout-v2".hash(h);
    hash_def_pub(h, p, def);
    let Some(a) = p.adt_by_def(def) else { return };
    let adt = p.adt(a);
    adt.is_enum.hash(h);
    match adt.repr.kind {
        crate::ty::layout::ReprKind::Default => 0u8.hash(h),
        crate::ty::layout::ReprKind::C => 1u8.hash(h),
        crate::ty::layout::ReprKind::Transparent => 2u8.hash(h),
    }
    adt.repr.int.hash(h);
    adt.repr.align.hash(h);
    adt.repr.pack.hash(h);
    // The derive list is not part of the layout (PLAN R12, P3.3): every
    // reader of it records its own `Derives` read (check/derive_delta.rs).
    // `#[non_exhaustive]` changes match exhaustiveness answers over
    // this type, which layout readers (a match's scrutinee type) see.
    adt.non_exhaustive.hash(h);
    // The written impls derive glue calls for a value of this type.
    let glue = |tr: DefId| p.gx.glue_methods.contains_key(&(a, tr));
    (glue(p.gx.lang.clone), glue(p.gx.lang.default), glue(p.gx.lang.partial_eq), glue(p.gx.lang.partial_ord)).hash(h);
    p.gx.written_hash.contains_key(&a).hash(h);
    p.gx.borrow_impls.keys().filter(|(b, _)| *b == a).count().hash(h);
    p.gx.dyn_keys.get(&a).map(|k| (k.eq, k.hash, k.borrow)).hash(h);
    // The written `Hasher` and `BuildHasher` impls the hash glue calls
    // into: which methods they write, and the `Hasher` type (W-STD-B).
    for tr in [p.gx.lang.hasher, p.gx.lang.build_hasher] {
        for &id in p.gx.index.impls_of_trait(tr) {
            let rec = p.gx.index.get(id);
            if rec.synthetic != crate::traits::index::Synthetic::None || rec.head != crate::traits::index::SelfHead::Adt(def) {
                continue;
            }
            for &m in &rec.items {
                if let Some(l) = p.local_def(m.hash) {
                    p.name(p.fn_info(l).name).hash(h);
                }
            }
            for &(_, t) in &rec.assoc_tys {
                hash_ty_refs(h, p, &p.tys, t, r);
            }
        }
    }
    // A generic Adt's parameters and bounds: a bound edit changes what
    // every use of the type must prove (generic reuse, W-PERF).
    if let Some(g) = p.gx.adt_generics.get(a.0 as usize) {
        hash_generics(h, p, g);
    }
    (adt.variants.len() as u64).hash(h);
    for v in &adt.variants {
        p.name(v.name).hash(h);
        match v.shape {
            VariantShape::Unit => 0u8.hash(h),
            VariantShape::Tuple => 1u8.hash(h),
            VariantShape::Named => 2u8.hash(h),
        }
        v.disc.hash(h);
        v.non_exhaustive.hash(h);
        (v.fields.len() as u64).hash(h);
        for (i, fd) in v.fields.iter().enumerate() {
            // Tuple fields carry a synthetic index `Sym`, not a name.
            if v.shape == VariantShape::Named {
                p.name(fd.name).hash(h);
            } else {
                (i as u64).hash(h);
            }
            hash_ty_refs(h, p, &p.tys, fd.ty, r);
        }
    }
}

/// The `Derives(def)` node's fingerprint: the derive list of the Adt
/// with that def, or a fixed value when this program has no such Adt.
fn derives_fingerprint(p: &Program, def: DefId) -> Fingerprint {
    let mut h = FxHasher::default();
    "derives-v1".hash(&mut h);
    if let Some(a) = p.adt_by_def(def) {
        let d = p.adt(a).derives_unlogged();
        (d.debug, d.clone, d.copy, d.partial_eq, d.eq, d.hash, d.partial_ord, d.ord, d.default, d.default_variant).hash(&mut h);
    }
    Fingerprint(h.finish())
}

/// The `DeriveBits(def, mask)` node's fingerprint: the derive flags of
/// the Adt with that def that `mask` selects (and the `#[default]` variant
/// with the `Default` bit), or a fixed value when there is no such Adt.
fn derive_bits_fingerprint(p: &Program, def: DefId, mask: u16) -> Fingerprint {
    let mut h = FxHasher::default();
    "derive-bits-v1".hash(&mut h);
    mask.hash(&mut h);
    if let Some(a) = p.adt_by_def(def) {
        let d = p.adt(a).derives_unlogged();
        crate::check::derive_delta::masked(&d, mask).hash(&mut h);
        if mask & crate::check::derive_delta::bit::DEFAULT != 0 {
            d.default_variant.hash(&mut h);
        }
    }
    Fingerprint(h.finish())
}

/// The `LayoutOf(adt)` node's fingerprint (section 8.1), separate from
/// `Sig`: it covers only what layout and value semantics read (see
/// `hash_adt_layout`), so an edit that changes a type's methods or a
/// field's visibility does not dirty layout readers, and a field edit
/// dirties them even when no signature that names the type changed text.
pub(crate) fn layout_fingerprint(p: &Program, def: DefId) -> Fingerprint {
    let mut h = FxHasher::default();
    "layout-v2".hash(&mut h);
    adt_deep(p, Deep::Layout, def, &mut DeepMemo::default()).hash(&mut h);
    Fingerprint(h.finish())
}

/// Folds the regions of one regioned type (W-BORROW, `p.regions`) into
/// `h`: its structure with regions, then the deep regions fingerprint
/// of every Adt it names (`adt_deep`). Erased types hide what the borrow
/// checker reads here (`&'static str` and `&str` are one erased type;
/// an Adt's variance comes from its fields' regions), so a region-only
/// edit must move the `Sig` fingerprint of what it changed.
fn hash_regions_deep(h: &mut FxHasher, p: &Program, t: Ty, memo: &mut DeepMemo) {
    hash_ty_refs(h, p, &p.tys, t, &mut |h, def| adt_deep(p, Deep::Regions, def, memo).hash(h));
}

/// Folds one Adt's lifetime params and regioned field types into `h`;
/// `r` folds each Adt a field type names (see `hash_regions_deep`).
fn hash_adt_regions(h: &mut FxHasher, p: &Program, def: DefId, r: &mut dyn FnMut(&mut FxHasher, DefId)) {
    "adt-regions-v2".hash(h);
    hash_def_pub(h, p, def);
    (p.gx.adt_lifetimes.get(&def).map_or(0, |v| v.len()) as u64).hash(h);
    p.regions.adt_facts.get(&def).hash(h);
    // Its regioned trait bounds (tf-borrow r9): building a value replays them.
    if let Some(bs) = p.regions.adt_bounds.get(&def) {
        (bs.len() as u64).hash(h);
        for b in bs {
            if let Predicate::Trait(t) = b {
                hash_def_pub(h, p, t.value.def);
                for g in p.tys.args(t.value.args) {
                    match *g {
                        GenericArg::Ty(x) => hash_ty_refs(h, p, &p.tys, x, r),
                        GenericArg::Lifetime(x) => hash_region(h, x),
                        _ => {}
                    }
                }
            }
        }
    }
    let Some(variants) = p.regions.adt_fields.get(&def) else { return 0u8.hash(h) };
    (variants.len() as u64).hash(h);
    for fields in variants {
        (fields.len() as u64).hash(h);
        for &t in fields {
            hash_ty_refs(h, p, &p.tys, t, r);
        }
    }
}

/// Folds a fn's region signature into `h`: regioned params and return
/// (deeply), outlives facts, and early-bound flags. A caller's borrow
/// check reads all of them; the erased signature shows none.
fn hash_region_sig(h: &mut FxHasher, p: &Program, rs: Option<&crate::borrowck::RegionSig>) {
    "region-sig-v2".hash(h);
    let Some(rs) = rs else { return 0u8.hash(h) };
    1u8.hash(h);
    rs.n_univ.hash(h);
    let mut seen = DeepMemo::default();
    (rs.params.len() as u64).hash(h);
    for &t in &rs.params {
        hash_regions_deep(h, p, t, &mut seen);
    }
    hash_regions_deep(h, p, rs.ret, &mut seen);
    (rs.facts.len() as u64).hash(h);
    for &(a, b) in &rs.facts {
        hash_region(h, a);
        hash_region(h, b);
    }
    rs.early.hash(h);
    rs.opaque_caps.hash(h);
    (rs.header.len() as u64).hash(h);
    for &t in &rs.header {
        hash_regions_deep(h, p, t, &mut seen);
    }
    (rs.fn_bounds.len() as u64).hash(h);
    for b in &rs.fn_bounds {
        b.param.hash(h);
        (b.inputs.len() as u64).hash(h);
        for &t in b.inputs.iter().chain(b.output.iter()) {
            hash_regions_deep(h, p, t, &mut seen);
        }
        b.output.is_some().hash(h);
    }
    (rs.trait_bounds.len() as u64).hash(h);
    for b in &rs.trait_bounds {
        b.param.hash(h);
        hash_def_pub(h, p, b.trait_def);
        for &r in &b.lifetimes {
            hash_region(h, r);
        }
    }
    (rs.item_bounds.len() as u64).hash(h);
    for &(j, d, t) in &rs.item_bounds {
        j.hash(h);
        hash_def_pub(h, p, d);
        hash_regions_deep(h, p, t, &mut seen);
    }
    hash_preds_regions(h, p, &rs.bounds, &mut seen);
}

/// Folds regioned predicates into `h` (`RegionSig::bounds`,
/// `ImplRegions::preds`): a caller's borrow check replays the impls they
/// select with these regions.
fn hash_preds_regions(h: &mut FxHasher, p: &Program, preds: &[Predicate], seen: &mut DeepMemo) {
    let args = |h: &mut FxHasher, a: crate::ty::ArgsId, seen: &mut DeepMemo| {
        for g in p.tys.args(a) {
            match *g {
                GenericArg::Ty(t) => hash_regions_deep(h, p, t, seen),
                GenericArg::Lifetime(r) => hash_region(h, r),
                _ => 9u8.hash(h),
            }
        }
    };
    (preds.len() as u64).hash(h);
    for pred in preds {
        match *pred {
            Predicate::Trait(b) => {
                (0u8, b.count).hash(h);
                hash_def_pub(h, p, b.value.def);
                args(h, b.value.args, seen);
            }
            Predicate::AssocEq(b) => {
                (1u8, b.count).hash(h);
                hash_def_pub(h, p, b.value.assoc);
                args(h, b.value.trait_args, seen);
                hash_regions_deep(h, p, b.value.ty, seen);
            }
            Predicate::Outlives(a, b) => {
                2u8.hash(h);
                hash_region(h, a);
                hash_region(h, b);
            }
            Predicate::TypeOutlives(t, r) => {
                3u8.hash(h);
                hash_regions_deep(h, p, t, seen);
                hash_region(h, r);
            }
        }
    }
}

/// The fingerprint of a `Binding` node's answer (section 8.1: the resolved
/// def in disk form, or ambiguous, or absent). Wave A also folds the
/// resolved def's `Sig` fingerprint in: read-based reuse must not keep a
/// body that recorded only the binding (a fn used as a value, say) when
/// that def's signature changed. This is coarser than section 8.1's
/// node split and can narrow once read-coverage reviews prove every
/// signature use records a `Sig` read.
fn binding_fingerprint(p: &Program, res: BindingRes) -> Fingerprint {
    let mut h = FxHasher::default();
    "binding-v2".hash(&mut h);
    match res {
        BindingRes::Def(def) => {
            0u8.hash(&mut h);
            hash_def_pub(&mut h, p, def);
            sig_fingerprint(p, def).0.hash(&mut h);
        }
        BindingRes::Ambiguous => 1u8.hash(&mut h),
        BindingRes::Absent => 2u8.hash(&mut h),
    }
    Fingerprint(h.finish())
}

/// The fingerprint of a `TraitInScope` node: its answer.
fn trait_in_scope_fingerprint(ans: bool) -> Fingerprint {
    let mut h = FxHasher::default();
    ("trait-in-scope-v1", ans).hash(&mut h);
    Fingerprint(h.finish())
}

/// Folds a probe head into a fingerprint. Head payloads hash by stable
/// content (def disk identity, scalar type name), never by session id.
fn hash_head(h: &mut FxHasher, p: &Program, head: Head) {
    match head {
        Head::Adt(def) => {
            0u8.hash(h);
            hash_def_pub(h, p, def);
        }
        Head::Int(i) => (1u8, i.name()).hash(h),
        Head::Float(f) => (2u8, f.name()).hash(h),
        Head::Bool => 3u8.hash(h),
        Head::Char => 4u8.hash(h),
        Head::Str => 5u8.hash(h),
        Head::Slice => 6u8.hash(h),
        Head::Array => 7u8.hash(h),
        Head::Tuple => 8u8.hash(h),
        Head::Never => 9u8.hash(h),
        Head::Unit => 10u8.hash(h),
        Head::Unknown => 11u8.hash(h),
    }
}

/// The fingerprint of a `MethodSet` node's candidate list, in probe order.
/// Candidate `Sig` fingerprints fold in for the same reason as in
/// `binding_fingerprint`. An empty set still folds the probe itself
/// (head, name, receiver form): builtin method dispatch answers those
/// probes through the compat path in check, so the probe is the read
/// on record for the builtin answer. That answer is fixed by the
/// compiler, and no user edit can add an inherent method to a builtin
/// or primitive head; when trait candidates join `method_candidates`,
/// they appear in the set and change this fingerprint by themselves.
fn method_set_fingerprint(p: &Program, key: &MethodSetKey, set: &MethodSet) -> Fingerprint {
    let mut h = FxHasher::default();
    "method-set-v3".hash(&mut h);
    (set.candidates.len() as u64).hash(&mut h);
    for c in &set.candidates {
        hash_def_pub(&mut h, p, c.def);
        sig_fingerprint(p, c.def).0.hash(&mut h);
        match c.trait_ {
            Some(t) => hash_def_pub(&mut h, p, t),
            None => 0u64.hash(&mut h),
        }
    }
    if set.candidates.is_empty() {
        "builtin-probe-v1".hash(&mut h);
        hash_head(&mut h, p, key.head);
        p.name(key.name).hash(&mut h);
        match key.form {
            ReceiverForm::Value => 0u8.hash(&mut h),
            ReceiverForm::Ref => 1u8.hash(&mut h),
            ReceiverForm::RefMut => 2u8.hash(&mut h),
        }
    }
    Fingerprint(h.finish())
}

/// The fingerprint of an `ImplSet` bucket: the bucket key (trait and
/// head) plus each impl's def and content (`impl_content`), sorted so the
/// bucket's discovery order does not matter (section 8.1). The content
/// joins because an impl keeps its def through edits to its where
/// clauses, associated types and consts, and method list.
fn impl_set_fingerprint(p: &Program, key: &ImplSetKey, set: &ImplSet) -> Fingerprint {
    // The `'static` dyn flag joins each impl (check::object): flipping
    // `impl X for dyn Tr` to `+ '_` keeps the def.
    let mut defs: Vec<(u64, u64, bool, u64)> = set
        .impls
        .iter()
        .map(|d| (def_crate_hash(p, *d), d.hash.0, p.gx.static_dyn_impls.contains(d), impl_content(p, *d)))
        .collect();
    defs.sort_unstable();
    let mut h = FxHasher::default();
    "impl-set-v2".hash(&mut h);
    hash_def_pub(&mut h, p, key.trait_);
    hash_head(&mut h, p, key.head);
    (defs.len() as u64).hash(&mut h);
    for d in defs {
        d.hash(&mut h);
    }
    // A blanket impl bounded by a derivable trait (`impl<T: Debug> U for
    // T`): whether a local Adt head selects it follows that Adt's derive
    // list, so the derive flags its bounds name join (sigedit R13 v2).
    if let Head::Adt(d) = key.head
        && let Some(a) = p.adt_by_def(d)
    {
        let mask = set
            .impls
            .iter()
            .filter_map(|&i| p.gx.index.by_def(i))
            .filter(|(_, rec)| rec.blanket.is_some())
            .fold(0u16, |m, (_, rec)| m | crate::check::derive_delta::bound_mask(p, &rec.generics.predicates));
        if mask != 0 {
            crate::check::derive_delta::masked(&p.adt(a).derives_unlogged(), mask).hash(&mut h);
        }
    }
    Fingerprint(h.finish())
}

/// The content of one impl as selection and its callers see it: header
/// (trait ref pattern), generics and where clauses, associated type and
/// const bindings, and each item's def and signature. Method bodies are
/// not in it (each is its own fn, checked on its own).
fn impl_content(p: &Program, def: DefId) -> u64 {
    let Some((_, rec)) = p.gx.index.by_def(def) else { return 0 };
    let mut h = FxHasher::default();
    "impl-content-v1".hash(&mut h);
    hash_trait_ref(&mut h, p, &p.tys, &rec.trait_ref);
    // A header's regions for a trait with lifetime params (W-BORROW):
    // callers' borrow checks replay them.
    // Any trait impl's regioned header and where-clauses (tf-borrow r9):
    // a bound that selects the impl replays them.
    if let Some(ir) = p.regions.impl_regions.get(&def) {
        let mut seen = DeepMemo::default();
        for &t in ir.header.iter().chain(ir.assoc.iter().map(|(_, t)| t)) {
            hash_regions_deep(&mut h, p, t, &mut seen);
        }
        ir.facts.hash(&mut h);
        hash_preds_regions(&mut h, p, &ir.preds, &mut seen);
    }
    if let Some(head) = p.regions.impl_heads.get(&def) {
        let mut seen = DeepMemo::default();
        hash_regions_deep(&mut h, p, head.self_ty, &mut seen);
        for &r in &head.trait_lifetimes {
            hash_region(&mut h, r);
        }
        for w in &head.where_lts {
            w.param.hash(&mut h);
            hash_def_pub(&mut h, p, w.trait_def);
            for &r in &w.lifetimes {
                hash_region(&mut h, r);
            }
        }
    }
    hash_generics(&mut h, p, &rec.generics);
    (rec.assoc_tys.len() as u64).hash(&mut h);
    for (d, t) in &rec.assoc_tys {
        hash_def_pub(&mut h, p, *d);
        hash_ty(&mut h, p, &p.tys, *t);
    }
    (rec.assoc_consts.len() as u64).hash(&mut h);
    for (d, c) in &rec.assoc_consts {
        hash_def_pub(&mut h, p, *d);
        hash_const(&mut h, &p.tys, *c);
    }
    (rec.items.len() as u64).hash(&mut h);
    for d in &rec.items {
        hash_def_pub(&mut h, p, *d);
        sig_fingerprint(p, *d).0.hash(&mut h);
    }
    h.finish()
}

/// Folds one visibility into `h`: its form, and for `pub(in path)` the
/// written path by name (never by `Sym` id).
fn hash_vis(h: &mut FxHasher, p: &Program, vis: &VisKind) {
    match vis {
        VisKind::Priv => 0u8.hash(h),
        VisKind::Pub => 1u8.hash(h),
        VisKind::Crate => 2u8.hash(h),
        VisKind::Super => 3u8.hash(h),
        VisKind::In(path) => {
            4u8.hash(h);
            (path.len() as u64).hash(h);
            for s in path {
                p.name(*s).hash(h);
            }
        }
    }
}

/// Folds one module into `h` by its name path from its crate root, never
/// by its session id. Privacy answers are functions of these paths: the
/// reader's own module is fixed by its def path, which keys its slot.
fn hash_module_path(h: &mut FxHasher, p: &Program, t: &ResolvedTables, m: ModuleId) {
    let path = t.modules.get(m.0 as usize).map_or(&[][..], |info| &info.path[..]);
    (path.len() as u64).hash(h);
    for s in path {
        p.name(*s).hash(h);
    }
}

/// Folds the visibility facts of one def into its `Sig` fingerprint
/// (section 8.1: `Sig` covers vis). These are the def's own visibility
/// and, for an Adt, the visibility of each named field, tuple field,
/// and inherent associated item, each with its defining module. Body
/// checking records a `Sig(adt)` read at every field, constructor, and
/// method privacy check (`check_field_vis` and kin in check/mod.rs), so
/// a visibility-only edit dirties those readers in the walk. Path and
/// re-export privacy are answered by the resolver, which reruns its
/// rewrite whenever `ResolvedTables::rewrite_epoch` moves; the own
/// visibility here also dirties the bodies whose `Binding` reads name
/// the def. Map entries fold order-free (their order is not a fact).
/// Programs without resolver tables are one module: no facts to fold.
fn hash_vis_facts(h: &mut FxHasher, p: &Program, def: DefId) {
    let Some(t) = &p.resolved else { return };
    if let Some(info) = t.def_info.get(&def) {
        hash_vis(h, p, &info.vis);
        hash_module_path(h, p, t, info.module);
    }
    if let Some((m, fields)) = t.field_vis.get(&def) {
        hash_module_path(h, p, t, *m);
        let mut acc = 0u64;
        for (name, vis) in fields {
            let mut e = FxHasher::default();
            p.name(*name).hash(&mut e);
            hash_vis(&mut e, p, vis);
            acc = acc.wrapping_add(e.finish());
        }
        (fields.len() as u64, acc).hash(h);
    }
    // `#[non_exhaustive]` (the type's and each variant's, in order):
    // construction, pattern, and exhaustiveness answers in other
    // crates read it through the same `Sig(adt)` reads as field
    // privacy, so toggling it must move this fingerprint.
    if let Some(a) = p.adt_by_def(def) {
        let adt = p.adt(a);
        adt.non_exhaustive.hash(h);
        for v in &adt.variants {
            v.non_exhaustive.hash(h);
        }
    }
    if let Some((m, fields)) = t.tuple_field_vis.get(&def) {
        hash_module_path(h, p, t, *m);
        (fields.len() as u64).hash(h);
        for vis in fields {
            hash_vis(h, p, vis);
        }
    }
    if let Some(items) = t.assoc_vis.get(&def) {
        let mut acc = 0u64;
        for (name, (vis, m)) in items {
            let mut e = FxHasher::default();
            p.name(*name).hash(&mut e);
            hash_vis(&mut e, p, vis);
            hash_module_path(&mut e, p, t, *m);
            acc = acc.wrapping_add(e.finish());
        }
        (items.len() as u64, acc).hash(h);
    }
}

/// Folds one evaluated const value into `h`. `StaticRef` (`StaticPlace`) indices are
/// collect-order positions, not stable content, so they fold the
/// referenced static's name and (depth-capped) value instead.
fn hash_const_value(h: &mut FxHasher, p: &Program, v: &crate::ty::consteval::ConstValue, depth: u32) {
    use crate::ty::consteval::ConstValue;
    match v {
        ConstValue::Int(x) => (0u8, x).hash(h),
        ConstValue::Float(bits, f) => (10u8, bits, f.name()).hash(h),
        ConstValue::Bool(b) => (1u8, b).hash(h),
        ConstValue::Char(c) => (2u8, c).hash(h),
        ConstValue::Str(i) => {
            3u8.hash(h);
            p.ast.strings.get(*i as usize).map_or("", String::as_str).hash(h);
        }
        // Hashed as the text, like a literal of the same text.
        ConstValue::StrBytes(b) => {
            3u8.hash(h);
            std::str::from_utf8(b.as_slice()).unwrap_or("").hash(h);
        }
        ConstValue::Unit => 4u8.hash(h),
        ConstValue::Aggregate(vals) => {
            5u8.hash(h);
            (vals.len() as u64).hash(h);
            for v in vals {
                hash_const_value(h, p, v, depth);
            }
        }
        ConstValue::Variant(variant, vals) => {
            (6u8, variant).hash(h);
            (vals.len() as u64).hash(h);
            for v in vals {
                hash_const_value(h, p, v, depth);
            }
        }
        ConstValue::Repeat(inner, n) => {
            (7u8, n).hash(h);
            hash_const_value(h, p, inner, depth);
        }
        ConstValue::Ref(inner) => {
            8u8.hash(h);
            hash_const_value(h, p, inner, depth);
        }
        ConstValue::FnPtr(f) => {
            11u8.hash(h);
            p.fn_defs.get(*f as usize).map(|d| d.hash.0).hash(h);
        }
        ConstValue::Bytes(b) => {
            12u8.hash(h);
            b.as_slice().hash(h);
        }
        ConstValue::StaticPlace(i, path) => {
            (13u8, path).hash(h);
            hash_const_value(h, p, &ConstValue::StaticRef(*i), depth);
        }
        ConstValue::StaticRef(i) => {
            9u8.hash(h);
            match p.statics.get(*i as usize) {
                Some(s) => {
                    p.name(s.name).hash(h);
                    if depth < 8 {
                        hash_const_value(h, p, &s.value, depth + 1);
                    }
                }
                None => 0u8.hash(h),
            }
        }
    }
}

/// The fingerprint of one def's resolved signature (section 8.1 `Sig` node):
/// signature types with defs in stable form, plus the def's visibility
/// facts (`hash_vis_facts`). Types hash *deeply* (see
/// `hash_ty_deep`): a field, layout, derive, or discriminant edit to a
/// named Adt changes every signature that names it, so the dirty walk
/// rechecks bodies that read the signature. That is what lets the walk
/// cover type edits, not only signature text edits. Const and static
/// defs fold their evaluated value in (a value edit that keeps the
/// value invalidates nothing); type aliases fold their resolved target.
/// Generics and predicates join when generic collect fills them
/// (W-TRAITS-CORE); today they are empty for every user def.
fn sig_fingerprint(p: &Program, def: DefId) -> Fingerprint {
    let mut h = FxHasher::default();
    "sig-v4".hash(&mut h);
    hash_vis_facts(&mut h, p, def);
    hash_def_pub(&mut h, p, def);
    let mut seen = DeepMemo::default();
    if let Some(local) = p.local_def(def.hash).filter(|l| p.def_id(*l) == def) {
        let f = p.fn_info(local);
        0u8.hash(&mut h);
        match f.owner {
            // A method's signature reads its Self type's layout (field
            // access through `self`, by-value copies, drop glue).
            Some(a) => layout_fingerprint(p, p.def_of_adt(a)).0.hash(&mut h),
            None => 0u64.hash(&mut h),
        }
        match f.self_kind {
            None => 0u8.hash(&mut h),
            Some(SelfKind::Value) => 1u8.hash(&mut h),
            Some(SelfKind::Ref) => 2u8.hash(&mut h),
            Some(SelfKind::RefMut) => 3u8.hash(&mut h),
            Some(SelfKind::Typed) => 4u8.hash(&mut h),
        }
        (f.params.len() as u64).hash(&mut h);
        for t in &f.params {
            hash_ty_deep(&mut h, p, &p.tys, *t, &mut seen);
        }
        // Qualifiers are part of the caller-visible signature (an
        // `unsafe fn` flip changes what callers may do). Parameter
        // names and patterns are not: they bind only the body's own
        // locals, and the driver guards those with its per-slot head
        // hash, so a param rename reuses callers.
        (f.def(&p.ast).qual.is_const, f.def(&p.ast).qual.is_async, f.def(&p.ast).qual.is_unsafe, f.def(&p.ast).variadic).hash(&mut h);
        // The written visibility and the defining module: a caller of an
        // `impl dyn Tr` method checks access against them at the call
        // (`Ctx::check_dyn_method_vis`). Methods have no `def_info`
        // entry, so `hash_vis_facts` does not cover them.
        if let Some(t) = &p.resolved {
            hash_vis(&mut h, p, &crate::resolve::imports::vis_from_ast(&f.def(&p.ast).vis, &p.interner));
            if let Some(&m) = t.fn_module.get(local.0 as usize) {
                hash_module_path(&mut h, p, t, m);
            }
        }
        // `impl dyn Tr` vs `impl dyn Tr + '_`: the same types, but only
        // the first needs a `'static` receiver (check::object).
        p.gx.static_dyn_fns.contains(&local).hash(&mut h);
        // `#[track_caller]` adds a C parameter callers pass (check/caller.rs).
        crate::check::caller::is_track_caller(p, local).hash(&mut h);
        hash_ty_deep(&mut h, p, &p.tys, f.ret, &mut seen);
        // A generic fn's `impl Trait` return: callers' revealed checks
        // read its hidden type (check/opaque.rs).
        if let Some(&hidden) = p.gx.opaque_hidden.get(&crate::check::generics::opaque_def(def)) {
            hash_ty_deep(&mut h, p, &p.tys, hidden, &mut seen);
        }
        // The bounds of its `impl Trait` return: all callers see of it
        // (`impl Sh + Clone` to `impl Sh + Send` drops `.clone()`).
        match p.gx.opaques.get(&crate::check::generics::opaque_def(def)) {
            Some(o) => {
                (o.bounds.len() as u64).hash(&mut h);
                for pred in &o.bounds {
                    hash_predicate(&mut h, p, &p.tys, pred);
                }
                // Their written regions (`&'static` in `impl Fn(&u8) ->
                // &'static u8`), which the bounds erase.
                for b in &o.fn_outs {
                    for &t in b.inputs.iter().chain(b.output.iter()) {
                        hash_regions_deep(&mut h, p, t, &mut seen);
                    }
                }
            }
            None => u64::MAX.hash(&mut h),
        }
        // `fn f(x: &str)` and `fn f(x: &'static str)` erase alike;
        // callers' borrow checks read the region signature (W-BORROW).
        hash_region_sig(&mut h, p, p.regions.fns.get(&local));
        hash_region_sig(&mut h, p, p.regions.opaque_sigs.get(&local));
        // Callers of a trait impl method see the trait's signature too
        // (`trait_view`): a trait-only region edit moves the impl's.
        if let Some(m) = crate::borrowck::impl_trait_method(p, local) {
            hash_region_sig(&mut h, p, p.regions.trait_methods.get(&m));
        }
        f.ret_borrows_from.map(|i| i as u64 + 1).unwrap_or(0).hash(&mut h);
        // A generic fn's parameters and bounds (its impl's too, merged
        // in by collect): callers prove the bounds (generic reuse).
        match p.gx.fn_templates.get(local.0 as usize) {
            Some(Some(t)) => hash_generics(&mut h, p, &t.generics),
            _ => u64::MAX.hash(&mut h),
        }
    } else if p.adt_by_def(def).is_some() {
        1u8.hash(&mut h);
        layout_fingerprint(p, def).0.hash(&mut h);
        // Lifetime params and field regions (W-BORROW): `&'a T` and
        // `&'static T` fields erase alike.
        adt_deep(p, Deep::Regions, def, &mut seen).hash(&mut h);
    } else if let Some(data) = p.defs.get(def) {
        2u8.hash(&mut h);
        // Const and static payloads are found by def; aliases by flat
        // name, which the def record carries.
        if let Some(item) = p.const_by_def(def).map(|i| &p.consts[i as usize]) {
            0u8.hash(&mut h);
            hash_ty_deep(&mut h, p, &p.tys, item.ty, &mut seen);
            hash_const_value(&mut h, p, &item.value, 0);
            // Whether `&C` is promoted (lower `promotable`).
            item.qualif.hash(&mut h);
        } else if let Some(item) = p.static_by_def(def).map(|i| &p.statics[i as usize]) {
            1u8.hash(&mut h);
            item.mutable.hash(&mut h);
            hash_ty_deep(&mut h, p, &p.tys, item.ty, &mut seen);
            hash_const_value(&mut h, p, &item.value, 0);
            // A `thread_local!` key's form and init fn (W-TLS): key
            // method calls carry both in their IR (lower/tls.rs).
            if let Some(k) = item.tls {
                k.eager.hash(&mut h);
                hash_def_pub(&mut h, p, p.def_id(k.init));
            }
        } else if let Some(ty) = p.aliases.get(&data.name) {
            1u8.hash(&mut h);
            hash_ty_deep(&mut h, p, &p.tys, *ty, &mut seen);
        } else if let Some(la) = p.gx.generic_aliases.get(&data.name) {
            // A lifetime alias (W-BORROW) resolves at each use: its tokens
            // carry the regions, its erased body the type.
            2u8.hash(&mut h);
            la.body_hash.hash(&mut h);
            hash_ty_deep(&mut h, p, &p.tys, la.erased, &mut seen);
        } else {
            p.name(data.name).hash(&mut h);
        }
    } else if let Some(item) = p.static_by_def(def).map(|i| &p.statics[i as usize]) {
        // A nested (fn-body) static: collect gives it a def in
        // `static_defs` but no `Defs` record, so the branch above
        // misses it. Its value must still fold in: `statics_fingerprint`
        // is the only record that makes a later build rebuild the
        // glue unit when a nested static's initializer edits.
        2u8.hash(&mut h);
        1u8.hash(&mut h);
        item.mutable.hash(&mut h);
        hash_ty_deep(&mut h, p, &p.tys, item.ty, &mut seen);
        hash_const_value(&mut h, p, &item.value, 0);
        if let Some(k) = item.tls {
            k.eager.hash(&mut h);
            hash_def_pub(&mut h, p, p.def_id(k.init));
        }
    } else {
        3u8.hash(&mut h);
    }
    // A trait method's region signature (W-BORROW): calls through a
    // bound or a stub read it, and the trait item's text alone does not
    // reach this node.
    if let Some(rs) = p.regions.trait_methods.get(&def) {
        hash_region_sig(&mut h, p, Some(rs));
    }
    // Param defaults (W-CHECK-G): `S<u8>` means `S<u8, D>`, so a default
    // edit changes what every path that omits the arg names.
    if let Some(ds) = p.gx.param_defaults.get(&def) {
        for d in ds {
            match d {
                Some(GenericArg::Ty(t)) => hash_ty_deep(&mut h, p, &p.tys, *t, &mut seen),
                Some(GenericArg::Const(c)) => p.tys.const_kind(*c).hash(&mut h),
                _ => 0u8.hash(&mut h),
            }
        }
    }
    Fingerprint(h.finish())
}

/// The fingerprint of the program's statics as the glue unit emits
/// them: each static's `Sig` fingerprint (deep type plus evaluated
/// value; its visibility rides along, so a visibility edit costs one
/// glue rebuild) in definition order. The driver stores the fingerprint of
/// the statics last built into a glue unit and rebuilds that unit
/// when a later build's statics differ. This must be a built-state
/// comparison, not an edit trigger: a `check` request consumes the
/// edit that moved a value, and the following `build` request sees
/// an unchanged file.
/// The (Adt, method slot) pairs glue calls: written Display/Debug `fmt`
/// methods (`gx.fmt_methods`) and Drop methods (`gx.drop_methods`), in a
/// stable order. `slots` is the build's fn slot table.
pub(crate) fn glue_method_slots_fp(p: &Program, slots: &[u32]) -> u64 {
    let mut h = FxHasher::default();
    "glue-slots-v1".hash(&mut h);
    let slot = |f: crate::def::LocalDefId| slots.get(f.0 as usize).copied().unwrap_or(u32::MAX);
    let mut fm: Vec<(u32, u8, u32)> = p.gx.fmt_methods.iter().map(|(&(a, k), &f)| (a.0, k, slot(f))).collect();
    fm.sort_unstable();
    fm.hash(&mut h);
    let mut dm: Vec<(u32, u32)> = p.gx.drop_methods.iter().map(|(&a, &f)| (a.0, slot(f))).collect();
    dm.sort_unstable();
    dm.hash(&mut h);
    h.finish()
}

/// The evaluated value of every const and static, by def, plus one
/// fingerprint over the body consts in order: what a const fn edit can
/// move. A full collect after a const fn edit keeps generic reuse when no
/// value of the last program moved (driver/compile.rs).
#[derive(Clone, Default, PartialEq)]
pub(crate) struct ConstValuesFp {
    by_def: FxMap<crate::def::DefId, u64>,
    body: u64,
}

impl ConstValuesFp {
    pub(crate) fn of(p: &Program) -> ConstValuesFp {
        let fp = |v: &crate::ty::consteval::ConstValue| {
            let mut h = FxHasher::default();
            hash_const_value(&mut h, p, v, 0);
            h.finish()
        };
        let mut by_def: FxMap<crate::def::DefId, u64> = FxMap::default();
        for (d, c) in p.const_defs.iter().zip(&p.consts) {
            by_def.insert(*d, fp(&c.value));
        }
        for (d, s) in p.static_defs.iter().zip(&p.statics) {
            by_def.insert(*d, fp(&s.value));
        }
        let mut h = FxHasher::default();
        for c in &p.body_consts {
            fp(&c.value).hash(&mut h);
        }
        ConstValuesFp { by_def, body: h.finish() }
    }

    /// True when every value of `self` (the last program) that `new` still
    /// has is the same, and the body consts are.
    pub(crate) fn kept_in(&self, new: &ConstValuesFp) -> bool {
        self.body == new.body && self.by_def.iter().all(|(d, v)| new.by_def.get(d).is_none_or(|n| n == v))
    }
}

pub(crate) fn statics_fingerprint(p: &Program) -> u64 {
    let mut h = FxHasher::default();
    "statics-v1".hash(&mut h);
    (p.static_defs.len() as u64).hash(&mut h);
    for &def in &p.static_defs {
        sig_fingerprint(p, def).0.hash(&mut h);
    }
    h.finish()
}

// ---------- Query functions (section 8.2) ----------

/// The signature payload a `sig_of` query returns. Fn and Adt payloads still
/// live in the compat tables today (`FnInfo`, `AdtDef`); the query is the
/// only door to them that records a read. Other defs answer with their
/// `Defs` record until their payloads land.
#[allow(dead_code)] // The `Other` payload is read when non-fn/Adt payloads land.
pub enum SigOf<'p> {
    Fn(&'p FnInfo),
    Adt(&'p AdtDef),
    Other(&'p DefData),
    Missing,
}

impl<'a> Program {
    /// Resolves one module name in one namespace and records the `Binding`
    /// read. This is the frozen binding query wave A codes against: callers
    /// get a `DefId` and turn it into a session-local index through
    /// `local_def`, `adt_by_def`, or `Defs` queries, never the other way.
    ///
    /// When the crate went through the resolver (W-RESOLVE), this reads
    /// the section 1.3 module tables: per-module bindings with glob
    /// ambiguity, plus the flat-name index the merged AST's rewritten
    /// names resolve through (the checker asks in the root module). A
    /// table miss falls through to the single-file layer below, which
    /// also still answers for the builtin `String`/`Vec`/`Option`
    /// prelude defs. With no resolved tables (single-file programs),
    /// only that layer answers: one root module, never `Ambiguous`.
    /// The signature is the frozen S7 one; no caller changed.
    pub fn binding(&self, reads: &mut Reads, module: ModuleId, ns: Namespace, name: Sym) -> BindingRes {
        let res = self.binding_res(module, ns, name);
        reads.record_with(ReadKey::Binding(BindingKey { module, ns, name }), res == BindingRes::Absent, || binding_fingerprint(self, res));
        res
    }

    /// The binding answer without recording. The dirty walk replays old
    /// reads against the new program through this; `binding` is the only
    /// recording door. The resolver tables (W-RESOLVE) answer here
    /// first, so replays see the same answers as `binding`.
    pub(crate) fn binding_res(&self, module: ModuleId, ns: Namespace, name: Sym) -> BindingRes {
        // Spliced std source sees no user names (see `STD_MODULE`).
        if module == crate::ty::defs::STD_MODULE {
            return BindingRes::Absent;
        }
        // W-RESOLVE: the section 1.3 module tables answer first when the
        // crate went through the resolver; a miss falls through to the
        // single-file layer (builtins) below.
        if let Some(tables) = &self.resolved
            && let Some(res) = tables.binding(module, ns, name)
        {
            return res;
        }
        if module != ROOT_MODULE {
            return BindingRes::Absent;
        }
        match ns {
            Namespace::Value => match self.fn_names.get(&name) {
                Some(&f) => BindingRes::Def(self.def_id(f)),
                None => match self.type_names.get(&name) {
                    // A struct's name in value space is its constructor.
                    Some(&a) if !self.adt(a).is_enum => BindingRes::Def(self.def_of_adt(a)),
                    _ => BindingRes::Absent,
                },
            },
            Namespace::Type => match self.type_names.get(&name) {
                Some(&a) => BindingRes::Def(self.def_of_adt(a)),
                None => {
                    let b = self.tys.builtins();
                    if name == self.known.String {
                        BindingRes::Def(b.string)
                    } else if name == self.known.Vec {
                        BindingRes::Def(b.vec)
                    } else if name == self.known.Option {
                        BindingRes::Def(b.option)
                    } else {
                        BindingRes::Absent
                    }
                }
            },
            Namespace::Macro => BindingRes::Absent,
        }
    }

    /// The macro-namespace binding query of section 8.2, recorded at every
    /// expansion. It is `binding` in the macro namespace; the separate name
    /// keeps expansion call sites from depending on namespace plumbing.
    #[allow(dead_code)] // First caller is macro expansion (W-MACRO, wave A).
    pub fn macro_binding(&self, reads: &mut Reads, module: ModuleId, name: Sym) -> BindingRes {
        self.binding(reads, module, Namespace::Macro, name)
    }

    /// The candidate set for one method probe, recorded hit or miss
    /// (section 2.10 step 5). Probe every form in `ReceiverForm::PROBE_ORDER`
    /// and stop at the first hit, exactly as method resolution does: a body
    /// that picked a trait method must recheck when an inherent method of
    /// the same name appears, and only the recorded probes say so.
    ///
    /// Today only inherent user methods exist here, one candidate
    /// per inherent impl that defines the name on this Adt.
    /// Builtin methods on builtin and primitive heads still dispatch through
    /// the compat path in `check` and answer as an empty set here; the read
    /// is still recorded, with the probe itself in the fingerprint (see
    /// `method_set_fingerprint`), so the probe is on record when source
    /// std turns those builtins into real defs.
    pub fn method_set(&self, reads: &mut Reads, head: Head, name: Sym, form: ReceiverForm) -> MethodSet {
        let set = self.method_candidates(head, name, form);
        let failed = set.candidates.is_empty();
        let key = MethodSetKey { head, name, form };
        reads.record_with(ReadKey::MethodSet(key), failed, || method_set_fingerprint(self, &key, &set));
        set
    }

    /// Records the `MethodSet` reads of every receiver form for one name on
    /// one Adt. A lookup that reads the inherent method tables directly (a
    /// `S::f` path, an inherent-first check) depends on the same candidates
    /// a method probe sees, so it records the same reads.
    pub fn inherent_reads(&self, reads: &mut Reads, adt: DefId, name: Sym) {
        for form in ReceiverForm::PROBE_ORDER {
            let _ = self.method_set(reads, Head::Adt(adt), name, form);
        }
    }

    /// The method candidate set without recording. See `binding_res`.
    /// Mono instances of an inherent template join the compat method
    /// table (`generics::fn_instance`), but the template is the
    /// candidate: which instances exist depends on what collect
    /// materialized, so with them the set (and a `MethodSet` read)
    /// would differ between a warm and a cold program of the same text.
    fn method_candidates(&self, head: Head, name: Sym, form: ReceiverForm) -> MethodSet {
        let mut set = MethodSet::default();
        if let Head::Adt(def) = head
            && let Some(a) = self.adt_by_def(def)
            && let Some(fs) = self.methods.get(&(a, name))
        {
            for &f in fs.iter().filter(|f| self.gx.fn_class.get(f.0 as usize) != Some(&crate::check::generics::FnClass::Instance)) {
                let receiver = match self.fn_info(f).self_kind {
                    Some(SelfKind::Value) | Some(SelfKind::Typed) => Some(ReceiverForm::Value),
                    Some(SelfKind::Ref) => Some(ReceiverForm::Ref),
                    Some(SelfKind::RefMut) => Some(ReceiverForm::RefMut),
                    None => None,
                };
                // An associated fn without `self` surfaces in the first probe
                // only, marked with no receiver (see `MethodCandidate`).
                if receiver == Some(form) || (receiver.is_none() && form == ReceiverForm::Value) {
                    set.candidates.push(MethodCandidate { def: self.def_id(f), receiver, trait_: None });
                }
            }
        }
        set
    }

    /// The impl bucket for one trait and Self head, recorded at every
    /// selection (section 8.2; `traits::solve` step 2 calls it through
    /// `SolveCx::record_impl_set`). See `ImplSet` for which buckets fill.
    pub fn impl_set(&self, reads: &mut Reads, trait_: DefId, head: Head) -> ImplSet {
        let set = self.impl_bucket(trait_, head);
        let key = ImplSetKey { trait_, head };
        reads.record_with(ReadKey::ImplSet(key), set.impls.is_empty(), || impl_set_fingerprint(self, &key, &set));
        // Only a derivable trait's answer reads the derive list (its
        // derived record, or the lack of one). Another trait's impls that
        // a derive list decides (a blanket bounded by `Debug`) prove that
        // bound as a goal of its own, which records its own read.
        let bit = crate::check::derive_delta::trait_bit(self, trait_);
        if let Head::Adt(def) = head
            && bit != 0
            && self.adt_by_def(def).is_some()
        {
            self.record_derive_bits(reads, def, bit);
        }
        set
    }

    /// The def a `Derives` read of Adt `a` keys on: the template's, for
    /// an instance (instances copy their template's list). None for a
    /// placeholder row.
    pub(crate) fn derive_def(&self, a: AdtId) -> Option<DefId> {
        match self.gx.adt_instance_of.get(a.0 as usize).copied().flatten() {
            Some((template, _)) => Some(template),
            None => self.gx.adt_info.get(a.0 as usize).map(|&(def, _)| def).filter(|&d| d != DefId::PLACEHOLDER),
        }
    }

    /// Records a `Derives` read of the Adt template `def`.
    /// check/derive_delta.rs calls it for each def a scope noted.
    pub(crate) fn record_derives(&self, reads: &mut Reads, def: DefId) {
        reads.record_with(ReadKey::Derives(def), self.adt_by_def(def).is_none(), || derives_fingerprint(self, def));
    }

    /// Records a `DeriveBits` read of the traits `mask` of the Adt template
    /// `def` (check/derive_delta.rs `bit`).
    pub(crate) fn record_derive_bits(&self, reads: &mut Reads, def: DefId, mask: u16) {
        reads.record_with(ReadKey::DeriveBits(def, mask), self.adt_by_def(def).is_none(), || derive_bits_fingerprint(self, def, mask));
    }

    /// True for a trait whose impls fill `ImplSet` buckets, and so stay out
    /// of the trait-system key (`gen_reuse::trait_key`): a user trait (a
    /// trait item of this crate) with no associated const. A `<T as K>::C`
    /// path reads an impl's const with no recorded read.
    pub(crate) fn impls_read_covered(&self, trait_: DefId) -> bool {
        self.gx.index.trait_record(trait_).is_some_and(|r| r.local && r.assoc_items.iter().all(|&(_, _, is_type)| is_type))
    }

    /// The impls of trait `trait_` that a Self type with this head can
    /// select: the same head after `Head::of` peels references, or a Self
    /// pattern with no head (a blanket impl). An `Unknown` head takes every
    /// impl. Empty unless `impls_read_covered` (see `ImplSet`).
    fn impl_bucket(&self, trait_: DefId, head: Head) -> ImplSet {
        let mut set = ImplSet::default();
        if !self.impls_read_covered(trait_) {
            return set;
        }
        for &id in self.gx.index.impls_of_trait(trait_) {
            let rec = self.gx.index.get(id);
            let h = Head::of(&self.tys, rec.self_ty(&self.tys));
            if head == Head::Unknown || h == Head::Unknown || h == head {
                set.impls.push(rec.def);
            }
        }
        set
    }

    /// One def's resolved signature. Callers that only need identity facts
    /// (kind, parent, generics, param env) use `Defs` queries, which read
    /// this same `Sig` node per section 2.1; `sig_of` is for the payload.
    pub fn sig_of(&self, reads: &mut Reads, def: DefId) -> SigOf<'_> {
        let (out, failed) = if let Some(local) = self.local_def(def.hash).filter(|l| self.def_id(*l) == def) {
            (SigOf::Fn(self.fn_info(local)), false)
        } else if let Some(a) = self.adt_by_def(def) {
            (SigOf::Adt(self.adt(a)), false)
        } else if let Some(data) = self.defs.get(def) {
            (SigOf::Other(data), false)
        } else {
            (SigOf::Missing, true)
        };
        reads.record_with(ReadKey::Sig(def), failed, || sig_fingerprint(self, def));
        out
    }

    /// The layout fingerprint of one Adt def (`layout_fingerprint`),
    /// recorded as a `Layout` read. It is separate from the Adt's `Sig`
    /// fingerprint: a method or visibility edit on the type does not
    /// move it, and a field, repr, derive, or discriminant edit does.
    pub fn layout_of(&self, reads: &mut Reads, adt: DefId) -> Option<Fingerprint> {
        let known = self.adt_by_def(adt).is_some() || self.defs.get(adt).is_some();
        if !known {
            reads.record_with(ReadKey::Layout(adt), true, || layout_fingerprint(self, adt));
            return None;
        }
        if let Some(r) = reads.get(&ReadKey::Layout(adt)) {
            return Some(r.fingerprint);
        }
        let fp = layout_fingerprint(self, adt);
        reads.record(ReadKey::Layout(adt), fp, false);
        Some(fp)
    }

    /// Records a `Layout` read for every Adt named inside one type.
    /// Body checking uses this where it consumes a layout answer
    /// directly (`size_of`/`align_of` on a compound written type,
    /// `offset_of!`, layout queries inside body const evaluation): a
    /// written-type `Binding` read only names the outermost path, so
    /// `[S; 2]` or `(S, u8)` would otherwise record nothing for `S`.
    pub fn record_layout_reads(&self, reads: &mut Reads, tys: &impl TyIntern, t: Ty) {
        if reads.off {
            return;
        }
        let mut defs = Vec::new();
        collect_adt_defs(self, tys, t, &mut defs);
        for def in defs {
            let _ = self.layout_of(reads, def);
        }
    }

    /// Whether a user trait is defined in or imported into `module`
    /// (under any name, `as _` included), recorded as a `TraitInScope`
    /// read. Method probes ask this for each candidate trait; the
    /// answer has no binding read of its own, since the import may use
    /// any name. Without resolver tables, and for a trait the tables do
    /// not know, every local trait counts as in scope.
    pub fn trait_in_module(&self, reads: &mut Reads, module: ModuleId, trait_def: DefId) -> bool {
        let ans = self.trait_in_module_answer(module, trait_def);
        reads.record_with(ReadKey::TraitInScope(module, trait_def), !ans, || trait_in_scope_fingerprint(ans));
        ans
    }

    /// The `trait_in_module` answer without recording. See `binding_res`.
    pub(crate) fn trait_in_module_answer(&self, module: ModuleId, trait_def: DefId) -> bool {
        use crate::resolve::imports::{BindState, ns_index};
        let Some(res) = &self.resolved else { return true };
        let Some(info) = res.def_info.get(&trait_def) else { return true };
        info.module == module
            || res.maps.get(module.0 as usize).is_some_and(|maps| {
                maps[ns_index(Namespace::Type)]
                    .values()
                    .any(|s| matches!(s, BindState::One(b) if res.target_def(b.target) == trait_def))
            })
    }

    /// The kind of a def a binding resolved to, through the `Defs` table.
    /// Callers use it to tell a free fn from a struct constructor without
    /// reading the checker's name maps. Reads no node beyond the `Binding`
    /// read that produced the def.
    pub fn binding_kind(&self, def: DefId) -> Option<DefsKind> {
        self.defs.kind_of(def)
    }

    /// What one recorded read would answer in this program now, without
    /// recording anything: the node fingerprint and failed flag the query
    /// functions above would store today. The dirty walk compares this
    /// with the stored read (section 8.2 rule 2). `Checked` reads carry a
    /// mono body fingerprint this stage cannot recompute (no mono stage
    /// records them yet), so they report a sentinel that never matches a
    /// stored fingerprint: a body with such a read always rechecks.
    pub fn read_fingerprint(&self, key: &ReadKey) -> Read {
        match key {
            ReadKey::Binding(k) => {
                let res = self.binding_res(k.module, k.ns, k.name);
                Read { fingerprint: binding_fingerprint(self, res), failed: res == BindingRes::Absent }
            }
            ReadKey::MethodSet(k) => {
                let set = self.method_candidates(k.head, k.name, k.form);
                Read { fingerprint: method_set_fingerprint(self, k, &set), failed: set.candidates.is_empty() }
            }
            ReadKey::ImplSet(k) => {
                let set = self.impl_bucket(k.trait_, k.head);
                Read { fingerprint: impl_set_fingerprint(self, k, &set), failed: set.impls.is_empty() }
            }
            ReadKey::Sig(def) => {
                let known = self.local_def(def.hash).filter(|l| self.def_id(*l) == *def).is_some()
                    || self.adt_by_def(*def).is_some()
                    || self.defs.get(*def).is_some();
                Read { fingerprint: sig_fingerprint(self, *def), failed: !known }
            }
            ReadKey::Layout(def) => {
                let known = self.adt_by_def(*def).is_some() || self.defs.get(*def).is_some();
                Read { fingerprint: layout_fingerprint(self, *def), failed: !known }
            }
            ReadKey::Checked(_) => Read { fingerprint: Fingerprint(u64::MAX), failed: true },
            ReadKey::TraitInScope(module, trait_def) => {
                let ans = self.trait_in_module_answer(*module, *trait_def);
                Read { fingerprint: trait_in_scope_fingerprint(ans), failed: !ans }
            }
            ReadKey::Derives(def) => Read { fingerprint: derives_fingerprint(self, *def), failed: self.adt_by_def(*def).is_none() },
            ReadKey::DeriveBits(def, mask) => {
                Read { fingerprint: derive_bits_fingerprint(self, *def, *mask), failed: self.adt_by_def(*def).is_none() }
            }
        }
    }

    /// The dirty walk of section 8.3 step 5, one body at a time: how many
    /// of `reads` no longer match this program. Zero means every node the
    /// body read (per-name bindings, method-set probes hit and miss,
    /// failed lookups, signatures) has the same answer as when the body
    /// was checked, so the stored result can be reused if the body itself
    /// is unchanged. The count (not just a bool) feeds the scale gate's
    /// invalidated-query row.
    #[cfg(test)]
    pub fn reads_dirty(&self, reads: &Reads) -> usize {
        reads.iter().filter(|(k, stored)| self.read_fingerprint(k) != **stored).count()
    }

    /// `reads_dirty` with a per-program memo of node answers: a walk
    /// over many bodies computes each node's fingerprint once. The
    /// driver's walks use this form; tests use the plain one.
    pub fn reads_dirty_memo(&self, reads: &Reads, memo: &mut FxMap<ReadKey, Read>) -> usize {
        reads.iter().filter(|(k, stored)| *memo.entry(**k).or_insert_with(|| self.read_fingerprint(k)) != **stored).count()
    }
}

// ---------- The read index and the keyed dirty walk (sigedit P3.2) ----------

/// A reverse index over the per-slot read sets (`Caches::slot_reads`):
/// each read key to the slots whose stored reads hold it. A derive delta
/// knows which keys it can move (`Program::derive_key_moves`); the keyed
/// walk compares only those keys' fingerprints, for only the slots that
/// read them, in place of every passing body's whole read set.
///
/// Entries stay valid while the slot holds the same read set: `sync`
/// gives each new set a seal (`Reads::seal`, reset by any new key), and an
/// entry whose seal is not its slot's current one is stale and skipped.
#[derive(Default)]
pub(crate) struct ReadIndex {
    by_key: FxMap<ReadKey, Vec<(u32, u64)>>,
    /// The seal each slot was indexed under (0: none).
    stamp: Vec<u64>,
    next: u64,
    /// Entries in `by_key`, stale ones included (a rebuild drops those).
    entries: usize,
    live: usize,
}

impl ReadIndex {
    /// Indexes every slot whose read set changed since the last sync. The
    /// compile tail of a daemon calls it after each request, so a keyed
    /// walk finds it current (the first request builds it).
    pub(crate) fn sync(&mut self, slot_reads: &mut [Option<Reads>]) {
        if self.entries > 2 * self.live + 100_000 {
            *self = ReadIndex { next: self.next, ..ReadIndex::default() };
        }
        self.stamp.resize(slot_reads.len(), 0);
        for (s, r) in slot_reads.iter_mut().enumerate() {
            let cur = r.as_ref().map_or(0, |r| r.seal);
            if cur != 0 && cur == self.stamp[s] {
                continue;
            }
            match r {
                Some(r) => {
                    self.next += 1;
                    r.seal = self.next;
                    for k in r.map.keys() {
                        self.by_key.entry(*k).or_default().push((s as u32, r.seal));
                    }
                    self.entries += r.map.len();
                    self.stamp[s] = r.seal;
                }
                None => self.stamp[s] = 0,
            }
        }
        self.live = slot_reads.iter().flatten().map(Reads::len).sum();
    }

    /// The slots whose stored reads hold a key that `moves` takes and whose
    /// fingerprint differs from `p`'s now, and then, to a fixpoint, the
    /// slots with a `Checked(d)` read of a body `d` whose slot is dirty
    /// (`def_slot`; the oracle's rule: it checks again). Every other slot's
    /// reads are clean, given that no key outside `moves` changed (the
    /// caller's proof). Also returns, by slot, whether its reads hold any
    /// `Checked` key. Syncs the index first. The moved keys' fingerprints
    /// come from `answers`, the request's node answers for `p`, and the
    /// missing ones are computed in parallel and join it (the template and
    /// discovery replays read the same map, `GenReuse::memo`).
    pub(crate) fn dirty_slots(
        &mut self,
        p: &Program,
        slot_reads: &mut [Option<Reads>],
        quick: &(dyn Fn(&ReadKey) -> Option<bool> + Sync),
        moves: &mut dyn FnMut(&ReadKey) -> bool,
        def_slot: &dyn Fn(DefId) -> Option<usize>,
        answers: &mut FxMap<ReadKey, Read>,
    ) -> (Vec<bool>, Vec<bool>) {
        self.sync(slot_reads);
        crate::driver::laps::mark("keyed/sync");
        // `quick` answers most keys from tables on all cores; `moves` the
        // rest, one at a time.
        let entries: Vec<(&ReadKey, &Vec<(u32, u64)>)> = self.by_key.iter().collect();
        let quick_answers: Vec<Vec<Option<bool>>> =
            crate::driver::compile::par_map(&entries.chunks(4096).collect::<Vec<_>>(), |c| c.iter().map(|(k, _)| quick(k)).collect());
        let moved: Vec<(&ReadKey, &Vec<(u32, u64)>)> = entries
            .into_iter()
            .zip(quick_answers.into_iter().flatten())
            .filter(|((k, _), q)| q.unwrap_or_else(|| moves(k)))
            .map(|(e, _)| e)
            .collect();
        crate::driver::laps::mark("keyed/classify");
        let missing: Vec<ReadKey> = moved.iter().map(|(k, _)| **k).filter(|k| !answers.contains_key(k)).collect();
        let fresh = crate::driver::compile::par_map(&missing, |k| p.read_fingerprint(k));
        answers.extend(missing.into_iter().zip(fresh));
        crate::driver::laps::mark("keyed/fingerprint");
        // Each live entry compares its slot's stored answer, a lookup in a
        // read set apiece: a widely read moved key has many thousands, so
        // the entries go out in chunks to all cores.
        let mut dirty = vec![false; slot_reads.len()];
        let chunks: Vec<(&ReadKey, &[(u32, u64)])> = moved.iter().flat_map(|&(k, list)| list.chunks(2048).map(move |c| (k, c))).collect();
        let (stamp, reads, answers) = (&self.stamp, &*slot_reads, &*answers);
        let hits = crate::driver::compile::par_map(&chunks, |&(k, list)| {
            let now = answers[k];
            let live = |s: usize, seal: u64| stamp.get(s) == Some(&seal);
            let changed = |s: usize| reads[s].as_ref().and_then(|r| r.get(k)).is_some_and(|stored| stored != now);
            list.iter().map(|&(s, seal)| (s as usize, seal)).filter(|&(s, seal)| live(s, seal) && changed(s)).map(|(s, _)| s).collect::<Vec<_>>()
        });
        hits.into_iter().flatten().for_each(|s| dirty[s] = true);
        crate::driver::laps::mark("keyed/compare");
        let live = |s: usize, seal: u64| self.stamp.get(s) == Some(&seal);
        let mut has_checked = vec![false; slot_reads.len()];
        // The readers of each body by its slot, through `Checked` reads;
        // dirt spreads from each dirty slot to its live readers.
        let mut readers_of: FxMap<usize, Vec<&Vec<(u32, u64)>>> = FxMap::default();
        for (k, list) in &self.by_key {
            if let ReadKey::Checked(d) = k {
                list.iter().filter(|&&(s, seal)| live(s as usize, seal)).for_each(|&(s, _)| has_checked[s as usize] = true);
                if let Some(s) = def_slot(*d) {
                    readers_of.entry(s).or_default().push(list);
                }
            }
        }
        let mut work: Vec<usize> = (0..dirty.len()).filter(|&s| dirty[s]).collect();
        while let Some(s) = work.pop() {
            for list in readers_of.get(&s).into_iter().flatten() {
                for &(r, seal) in list.iter() {
                    let r = r as usize;
                    if live(r, seal) && !dirty[r] {
                        dirty[r] = true;
                        work.push(r);
                    }
                }
            }
        }
        crate::driver::laps::mark("keyed/checked");
        (dirty, has_checked)
    }
}

/// What a derive delta can move, per read key (`Program::derive_key_moves`),
/// with its answers per def memoized for one walk.
pub(crate) struct DeriveMoves<'a> {
    reach: &'a crate::check::derive_delta::Reach,
    sig: FxMap<DefId, bool>,
    /// Every key's answer, when asked for many read sets that share keys
    /// (`memoized`; the read index asks each key once).
    keys: Option<FxMap<ReadKey, bool>>,
    /// The names of the fns whose signature moves (`MethodSet` keys key
    /// on the method name).
    names: Option<FxMap<Sym, ()>>,
    /// The Adt defs with a written `Hasher` or `BuildHasher` impl whose
    /// associated type names the reach (`hasher_reaches`), made on use.
    hashers: Option<FxMap<DefId, ()>>,
}

/// A `Sync` view of a `DeriveMoves` whose moved fn names are made: the
/// tables `Program::derive_key_moves_quick` reads.
pub(crate) struct QuickMoves<'a> {
    defs: &'a FxMap<DefId, ()>,
    sig: &'a FxMap<DefId, bool>,
    names: &'a FxMap<Sym, ()>,
}

impl<'a> DeriveMoves<'a> {
    /// The tables of `derive_key_moves_quick` (None before `moved_fn_names`).
    pub(crate) fn quick(&self) -> Option<QuickMoves<'_>> {
        Some(QuickMoves { defs: self.reach.defs(), sig: &self.sig, names: self.names.as_ref()? })
    }

    pub(crate) fn new(reach: &'a crate::check::derive_delta::Reach) -> DeriveMoves<'a> {
        DeriveMoves { reach, sig: FxMap::default(), keys: None, names: None, hashers: None }
    }

    /// As `new`, with every key's answer memoized.
    pub(crate) fn memoized(reach: &'a crate::check::derive_delta::Reach) -> DeriveMoves<'a> {
        DeriveMoves { keys: Some(FxMap::default()), ..DeriveMoves::new(reach) }
    }
}

impl Program {
    /// True when a derive delta over `m.reach` may move the fingerprint of
    /// `key` (sigedit P3.2, the keyed walk). It must hold for every key
    /// whose fingerprint reads a derive list of the reach, directly or
    /// through a deep hash: `Derives` and `Layout` of a reach Adt (a
    /// layout folds the layouts of its field types, and the reach holds
    /// every field user); `Sig` of a reach Adt, of a fn whose signature,
    /// owner, hidden type, or bounds name one, and of a const, static, or
    /// alias whose type names one; `Binding` through the `Sig` it folds;
    /// `MethodSet` for a reach head or a moved method's name; `ImplSet`
    /// for a reach head or a bucket with an impl that names one. `Checked`
    /// and `TraitInScope` read no derive list.
    pub(crate) fn derive_key_moves(&self, m: &mut DeriveMoves, key: &ReadKey) -> bool {
        if let Some(&b) = m.keys.as_ref().and_then(|k| k.get(key)) {
            return b;
        }
        let b = self.derive_key_moves_uncached(m, key);
        if let Some(k) = &mut m.keys {
            k.insert(*key, b);
        }
        b
    }

    /// `derive_key_moves` without the per-key memo.
    fn derive_key_moves_uncached(&self, m: &mut DeriveMoves, key: &ReadKey) -> bool {
        let reach = m.reach;
        match key {
            ReadKey::Derives(d) | ReadKey::DeriveBits(d, _) | ReadKey::Layout(d) => self.adt_by_def(*d).is_none_or(|a| reach.row(self, a.0 as usize)) || self.hasher_reaches(m, *d),
            ReadKey::Sig(def) => self.sig_moves(m, *def),
            ReadKey::Binding(k) => match self.binding_res(k.module, k.ns, k.name) {
                BindingRes::Def(def) => self.sig_moves(m, def),
                _ => false,
            },
            ReadKey::MethodSet(k) => {
                if let Head::Adt(d) = k.head
                    && self.adt_by_def(d).is_some_and(|a| reach.row(self, a.0 as usize))
                {
                    return true;
                }
                self.moved_fn_names(m);
                m.names.as_ref().is_some_and(|n| n.contains_key(&k.name))
            }
            ReadKey::ImplSet(k) => {
                if let Head::Adt(d) = k.head
                    && self.adt_by_def(d).is_some_and(|a| reach.row(self, a.0 as usize))
                {
                    return true;
                }
                self.impl_bucket(k.trait_, k.head).impls.iter().any(|&d| {
                    self.gx.index.by_def(d).is_none_or(|(_, rec)| reach.record(&self.tys, rec) || rec.items.iter().any(|&it| self.sig_moves(m, it)))
                })
            }
            ReadKey::Checked(_) | ReadKey::TraitInScope(..) => false,
        }
    }

    /// The names of the fns whose signature moves (`DeriveMoves::names`),
    /// made once per `m`. The `sig_moves` answers of every fn, Adt, const
    /// and static fill `m` on the way (`derive_key_moves_quick` reads them).
    pub(crate) fn moved_fn_names(&self, m: &mut DeriveMoves) {
        if m.names.is_some() {
            return;
        }
        let mut names = FxMap::default();
        for i in 0..self.fns.len() {
            let f = LocalDefId(i as u32);
            if self.sig_moves(m, self.def_id(f)) {
                names.insert(self.fn_info(f).name, ());
            }
        }
        m.names = Some(names);
        for i in 0..self.adts.len() {
            if let Some(d) = self.defs.def_of_adt(AdtId(i as u32)) {
                self.sig_moves(m, d);
            }
        }
        // A const's or static's answer is its type's (`sig_moves`, by index:
        // its lookups scan the def lists). The first index of a def counts.
        let not_fn_or_adt = |d: DefId| self.local_def(d.hash).filter(|l| self.def_id(*l) == d).is_none() && self.adt_by_def(d).is_none();
        let consts: FxMap<DefId, ()> = self.const_defs.iter().map(|&d| (d, ())).collect();
        for (i, &d) in self.const_defs.iter().enumerate() {
            if !m.sig.contains_key(&d) && not_fn_or_adt(d) {
                m.sig.insert(d, m.reach.ty(&self.tys, self.consts[i].ty));
            }
        }
        for (i, &d) in self.static_defs.iter().enumerate() {
            if !m.sig.contains_key(&d) && not_fn_or_adt(d) && !consts.contains_key(&d) {
                m.sig.insert(d, m.reach.ty(&self.tys, self.statics[i].ty));
            }
        }
    }

    /// `derive_key_moves` from tables only, for a parallel walk: None when
    /// the key needs the walk itself (the caller asks `derive_key_moves`).
    /// `m` must hold the moved fn names (`moved_fn_names`).
    pub(crate) fn derive_key_moves_quick(&self, m: &QuickMoves, key: &ReadKey) -> Option<bool> {
        let row = |d: DefId| self.adt_by_def(d).is_some_and(|a| self.derive_def(a).is_some_and(|x| m.defs.contains_key(&x)));
        match key {
            ReadKey::Sig(def) => m.sig.get(def).copied(),
            ReadKey::Binding(k) => match self.binding_res(k.module, k.ns, k.name) {
                BindingRes::Def(def) => m.sig.get(&def).copied(),
                _ => Some(false),
            },
            ReadKey::MethodSet(k) => Some(matches!(k.head, Head::Adt(d) if row(d)) || m.names.contains_key(&k.name)),
            ReadKey::Checked(_) | ReadKey::TraitInScope(..) => Some(false),
            // As `sig_moves` answers for an Adt def (no fn has that def).
            ReadKey::Derives(d) | ReadKey::DeriveBits(d, _) | ReadKey::Layout(d) => match self.adt_by_def(*d) {
                None => Some(true),
                Some(_) => m.sig.get(d).copied(),
            },
            ReadKey::ImplSet(_) => None,
        }
    }

    /// `derive_key_moves` for a `Sig` key (memoized in `m`).
    pub(crate) fn sig_moves(&self, m: &mut DeriveMoves, def: DefId) -> bool {
        if let Some(&b) = m.sig.get(&def) {
            return b;
        }
        let reach = m.reach;
        let tys = &self.tys;
        let b = if let Some(local) = self.local_def(def.hash).filter(|l| self.def_id(*l) == def) {
            let f = self.fn_info(local);
            let od = crate::check::generics::opaque_def(def);
            f.owner.is_some_and(|a| reach.row(self, a.0 as usize))
                || f.params.iter().any(|&t| reach.ty(tys, t))
                || reach.ty(tys, f.ret)
                || self.gx.opaque_hidden.get(&od).is_some_and(|&t| reach.ty(tys, t))
                || self.gx.opaques.get(&od).is_some_and(|o| o.bounds.iter().any(|q| reach.pred(tys, q)))
                || self.gx.fn_templates.get(local.0 as usize).and_then(Option::as_ref).is_some_and(|t| t.generics.predicates.iter().any(|q| reach.pred(tys, q)))
        } else if let Some(a) = self.adt_by_def(def) {
            reach.row(self, a.0 as usize) || self.hasher_reaches(m, def)
        } else if let Some(i) = self.const_by_def(def) {
            reach.ty(tys, self.consts[i as usize].ty)
        } else if let Some(i) = self.static_by_def(def) {
            reach.ty(tys, self.statics[i as usize].ty)
        } else if let Some(data) = self.defs.get(def) {
            // `sig_fingerprint`: an alias folds its type; any other def
            // only its name.
            match (self.aliases.get(&data.name), self.gx.generic_aliases.get(&data.name)) {
                (Some(&t), _) => reach.ty(tys, t),
                (None, Some(la)) => reach.ty(tys, la.erased),
                (None, None) => false,
            }
        } else {
            false
        };
        m.sig.insert(def, b);
        b
    }

    /// True when Adt `def`'s layout fingerprint folds a written `Hasher`
    /// or `BuildHasher` impl's associated type that names a reach Adt
    /// (`hash_adt_layout`).
    fn hasher_reaches(&self, m: &mut DeriveMoves, def: DefId) -> bool {
        if m.hashers.is_none() {
            let mut heads = FxMap::default();
            for tr in [self.gx.lang.hasher, self.gx.lang.build_hasher] {
                for &id in self.gx.index.impls_of_trait(tr) {
                    let rec = self.gx.index.get(id);
                    if let crate::traits::index::SelfHead::Adt(d) = rec.head
                        && rec.assoc_tys.iter().any(|&(_, t)| m.reach.ty(&self.tys, t))
                    {
                        heads.insert(d, ());
                    }
                }
            }
            m.hashers = Some(heads);
        }
        m.hashers.as_ref().is_some_and(|h| h.contains_key(&def))
    }
}

// ---------- Instance keys and the slot manifest (section 4.2) ----------

/// The discovery key of one monomorphized instance: a fn, method, closure,
/// or static initializer def plus its type and const args. Regions never
/// enter the key. Owned by W-TRAITS-CORE through wave A (the minimal generic
/// pipeline may reshape it); S7 only fixes the type and its hash.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InstanceKey {
    pub def: DefId,
    pub args: ArgsId,
}

impl InstanceKey {
    /// A non-generic def is an instance with empty args (section 4.2).
    pub fn mono(def: DefId) -> InstanceKey {
        InstanceKey { def, args: EMPTY_ARGS }
    }
}

/// The stable hash of an instance key: def disk identity plus arg type and
/// const fingerprints, with lifetime args erased. Slot tables and manifest
/// files key on this, never on session ids inside `InstanceKey`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InstanceKeyHash(pub u64);

impl InstanceKeyHash {
    /// The hash of one def in disk form applied to an already-computed args
    /// fingerprint. This is the bridge from today's slot keys, which are
    /// plain disk defs: they are instance keys with the empty-args
    /// fingerprint.
    pub fn of_disk_def(disk: DiskDefId, args_fingerprint: Fingerprint) -> InstanceKeyHash {
        let mut h = FxHasher::default();
        "instance-v1".hash(&mut h);
        disk.krate.0.hash(&mut h);
        disk.hash.0.hash(&mut h);
        args_fingerprint.0.hash(&mut h);
        InstanceKeyHash(h.finish())
    }

    /// The args fingerprint of the empty argument list.
    pub fn empty_args_fingerprint() -> Fingerprint {
        let mut h = FxHasher::default();
        "instance-args-v1".hash(&mut h);
        0u64.hash(&mut h);
        Fingerprint(h.finish())
    }
}

impl<'a> Program {
    /// The instance key of one of today's non-generic functions.
    #[allow(dead_code)] // First caller is mono (wave B); the slot manifest tests use it now.
    pub fn instance_key(&self, f: LocalDefId) -> InstanceKey {
        InstanceKey::mono(self.def_id(f))
    }

    /// The stable hash of an instance key under this program. Lifetime args
    /// are skipped: regions do not affect code (section 4.2).
    #[allow(dead_code)] // See `instance_key`.
    pub fn instance_key_hash(&self, key: &InstanceKey) -> InstanceKeyHash {
        let mut h = FxHasher::default();
        "instance-args-v1".hash(&mut h);
        let args = self.tys.args(key.args);
        let n_value_args = args.iter().filter(|a| !matches!(a, GenericArg::Lifetime(_))).count();
        (n_value_args as u64).hash(&mut h);
        for a in args {
            match a {
                GenericArg::Ty(t) => {
                    0u8.hash(&mut h);
                    hash_ty(&mut h, self, &self.tys, *t);
                }
                GenericArg::Lifetime(_) => {}
                GenericArg::Const(c) => {
                    2u8.hash(&mut h);
                    hash_const(&mut h, &self.tys, *c);
                }
            }
        }
        let args_fp = Fingerprint(h.finish());
        let disk = DiskDefId { krate: StableCrateHash(def_crate_hash(self, key.def)), hash: key.def.hash };
        InstanceKeyHash::of_disk_def(disk, args_fp)
    }
}

/// The final binary's slot manifest: which slot each instance owns in the
/// one `lust_fns` table (sections 1.7 and 4.2). Assignment is append-only
/// per bin session; unreachable instances leave dead slots, which stay in
/// the manifest so no live slot ever moves. The persisted byte form for
/// today's non-generic subset lives in `driver::session`
/// (`encode_slot_manifest`); the general disk form is W-DRIVER's, under the
/// versioned cache file of section 8.4, not frozen here.
#[derive(Clone, Debug, Default)]
pub struct SlotManifest {
    by_key: FxMap<InstanceKeyHash, u32>,
    by_slot: Vec<InstanceKeyHash>,
}

impl SlotManifest {
    /// An empty manifest.
    #[allow(dead_code)] // First production owner is the slot store (W-DRIVER); tests use it now.
    pub fn new() -> SlotManifest {
        SlotManifest::default()
    }

    /// Builds a manifest from today's slot map (plain disk defs, which are
    /// empty-args instance keys). Slots must be dense, as `slot_update`
    /// assigns them; a sparse map is a driver bug, caught in debug builds.
    #[allow(dead_code)] // See `new`.
    pub fn from_disk_slots(slot_of: &FxMap<DiskDefId, u32>) -> SlotManifest {
        let empty = InstanceKeyHash::empty_args_fingerprint();
        let mut entries: Vec<(u32, InstanceKeyHash)> = slot_of.iter().map(|(k, &s)| (s, InstanceKeyHash::of_disk_def(*k, empty))).collect();
        entries.sort_unstable();
        let mut m = SlotManifest::default();
        for (slot, key) in entries {
            debug_assert_eq!(slot as usize, m.by_slot.len(), "slot manifest from a sparse slot map");
            m.by_key.insert(key, slot);
            m.by_slot.push(key);
        }
        m
    }

    /// The slot an instance owns, if it has one.
    #[allow(dead_code)] // See `new`.
    pub fn slot_of(&self, key: InstanceKeyHash) -> Option<u32> {
        self.by_key.get(&key).copied()
    }

    /// The slot an instance owns, assigning the next free slot if it has
    /// none. Append-only: an existing slot never moves.
    #[allow(dead_code)] // See `new`.
    pub fn assign(&mut self, key: InstanceKeyHash) -> u32 {
        match self.by_key.get(&key) {
            Some(&slot) => slot,
            None => {
                let slot = self.by_slot.len() as u32;
                self.by_key.insert(key, slot);
                self.by_slot.push(key);
                slot
            }
        }
    }

    /// Number of slots ever assigned, dead slots included.
    #[allow(dead_code)] // See `new`.
    pub fn len(&self) -> usize {
        self.by_slot.len()
    }

    /// True if no slot was ever assigned.
    #[allow(dead_code)] // See `new`.
    pub fn is_empty(&self) -> bool {
        self.by_slot.is_empty()
    }

    /// The hash of the whole manifest, by slot. Only the table unit (the
    /// unit that emits `lust_fns` itself) keys on this; every other unit
    /// keys on its used-slots hash, so one new slot rebuilds only the
    /// table (section 4.2).
    #[allow(dead_code)] // See `new`.
    pub fn manifest_hash(&self) -> u64 {
        let mut h = FxHasher::default();
        "slot-manifest-v1".hash(&mut h);
        (self.by_slot.len() as u64).hash(&mut h);
        for (slot, key) in self.by_slot.iter().enumerate() {
            (slot as u64, key.0).hash(&mut h);
        }
        h.finish()
    }

    /// The used-slots hash for one unit, given the instance keys its emitted
    /// code references (callees, its own instances, tables and trampolines
    /// it names). None if some key has no slot yet: the unit cannot be
    /// keyed until slot assignment covers it.
    #[allow(dead_code)] // See `new`.
    pub fn used_slots_hash(&self, used: &[InstanceKeyHash]) -> Option<u64> {
        let mut pairs: Vec<(u64, u64)> = Vec::with_capacity(used.len());
        for key in used {
            pairs.push((key.0, self.slot_of(*key)? as u64));
        }
        pairs.sort_unstable();
        pairs.dedup();
        let mut h = FxHasher::default();
        "used-slots-v1".hash(&mut h);
        (pairs.len() as u64).hash(&mut h);
        for pair in pairs {
            pair.hash(&mut h);
        }
        Some(h.finish())
    }

    /// The instance key at one slot, if the slot was ever assigned.
    #[allow(dead_code)] // See `new`.
    pub fn key_at(&self, slot: u32) -> Option<InstanceKeyHash> {
        self.by_slot.get(slot as usize).copied()
    }

    /// Serializes the manifest in slot order (magic, count, then one
    /// 8-byte instance key hash per slot). Dense by construction
    /// (`by_slot`), so slot numbers need no bytes. This is the 8.4 disk
    /// form for generic instances; the disk-def form for today's
    /// non-generic slots lives in `driver::session`. W-DRIVER owns both
    /// forms: change one only by bumping its magic.
    #[allow(dead_code)] // See `new`.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(8 + self.by_slot.len() * 8);
        out.extend_from_slice(SLOT_MANIFEST_INSTANCE_MAGIC);
        out.extend_from_slice(&(self.by_slot.len() as u32).to_le_bytes());
        for k in &self.by_slot {
            out.extend_from_slice(&k.0.to_le_bytes());
        }
        out
    }

    /// Reads bytes written by `encode`. None on any shape error (bad
    /// magic, wrong length, one instance in two slots), so a bad file is
    /// a cache miss, never a wrong slot. A decoded manifest assigns the
    /// same slots in any later discovery order: old keys answer from
    /// `by_key`, new keys append.
    #[allow(dead_code)] // See `new`.
    pub fn decode(b: &[u8]) -> Option<SlotManifest> {
        if b.get(..4)? != SLOT_MANIFEST_INSTANCE_MAGIC {
            return None;
        }
        let n = u32::from_le_bytes(b.get(4..8)?.try_into().ok()?) as usize;
        if b.len() != 8 + n.checked_mul(8)? {
            return None;
        }
        let mut m = SlotManifest::default();
        for i in 0..n {
            let at = 8 + i * 8;
            let key = InstanceKeyHash(u64::from_le_bytes(b[at..at + 8].try_into().ok()?));
            if m.by_key.insert(key, i as u32).is_some() {
                return None;
            }
            m.by_slot.push(key);
        }
        Some(m)
    }
}

/// Magic of the instance-hash slot manifest form. See `SlotManifest::encode`.
#[allow(dead_code)] // See `SlotManifest::new`.
const SLOT_MANIFEST_INSTANCE_MAGIC: &[u8; 4] = b"LSI1";

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::{check_fn, collect};
    use crate::def::{CrateIds, DefPathHash, LOCAL_CRATE};
    use crate::diag::FileId;
    use crate::intern::{Interner, Known};
    use crate::{lexer, parser};

    /// Parses and collects one sample file, then runs `run` on the program.
    fn with_program(src: &str, run: impl FnOnce(&Interner, &mut Program)) {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let mut program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        run(&interner, &mut program);
    }

    const SAMPLE: &str = "\
struct Foo { x: i64 }
impl Foo { fn get(&self) -> i64 { self.x } }
fn helper() -> i64 { 40 }
fn main() {
    let f: Foo = Foo { x: helper() };
    let y = f.get() + 2;
    println!(\"{}\", y);
}
";

    fn foo_head(p: &Program, interner: &Interner) -> Head {
        let a = p.type_names[&interner.intern("Foo")];
        Head::Adt(p.def_of_adt(a))
    }

    /// The S7 gate: a checked sample body records per-binding and
    /// method-set reads, hit and miss, through the query functions.
    #[test]
    fn sample_body_records_binding_and_method_set_reads() {
        with_program(SAMPLE, |interner, p| {
            let (ck, errs) = check_fn(p, p.main.unwrap());
            assert!(errs.is_empty(), "{errs:?}");
            let reads = &ck.reads;
            let value =
                |name: &str| ReadKey::Binding(BindingKey { module: ROOT_MODULE, ns: Namespace::Value, name: interner.intern(name) });
            // The `helper()` call reads one value binding, by that name only.
            let helper = reads.get(&value("helper")).expect("helper binding read");
            assert!(!helper.failed);
            // The `let f: Foo` annotation reads one type binding.
            let foo_ty = ReadKey::Binding(BindingKey { module: ROOT_MODULE, ns: Namespace::Type, name: interner.intern("Foo") });
            assert_eq!(reads.get(&foo_ty).map(|r| r.failed), Some(false));
            // A name the body never mentions has no read: reads are per name,
            // never per scope.
            assert!(!reads.contains(&value("missing")));
            // `f.get()` probes receiver forms in order: the by-value probe
            // misses and records a failed read, the `&self` probe hits, and
            // probing stops there.
            let head = foo_head(p, interner);
            let probe = |form| ReadKey::MethodSet(MethodSetKey { head, name: interner.intern("get"), form });
            assert_eq!(reads.get(&probe(ReceiverForm::Value)).map(|r| r.failed), Some(true), "by-value probe miss is recorded");
            assert_eq!(reads.get(&probe(ReceiverForm::Ref)).map(|r| r.failed), Some(false), "shared probe hit is recorded");
            assert!(!reads.contains(&probe(ReceiverForm::RefMut)), "probing stops at the hit");
            // The callee signatures the body used are on record too.
            let helper_def = p.def_id(p.fn_names[&interner.intern("helper")]);
            assert!(reads.contains(&ReadKey::Sig(helper_def)));
        });
    }

    /// A name that does not resolve is a failed read with the same key as a
    /// hit, so adding the def later rechecks exactly this body (8.2 rule 3).
    #[test]
    fn failed_binding_is_a_failed_read() {
        with_program("fn main() { nosuch(); }\n", |interner, p| {
            let (ck, errs) = check_fn(p, p.main.unwrap());
            assert!(!errs.is_empty(), "the call must also be an error");
            let key = ReadKey::Binding(BindingKey { module: ROOT_MODULE, ns: Namespace::Value, name: interner.intern("nosuch") });
            assert_eq!(ck.reads.get(&key).map(|r| r.failed), Some(true));
            // The same key in a program that defines the name is a hit with a
            // different fingerprint.
            let mut reads = Reads::new();
            assert_eq!(p.binding(&mut reads, ROOT_MODULE, Namespace::Macro, interner.intern("nosuch")), BindingRes::Absent);
            let macro_key = ReadKey::Binding(BindingKey { module: ROOT_MODULE, ns: Namespace::Macro, name: interner.intern("nosuch") });
            assert_eq!(reads.get(&macro_key).map(|r| r.failed), Some(true));
            // Different keys, same fingerprint: the fingerprint covers the
            // node's answer ("absent"), not which node was asked.
            assert_eq!(reads.get(&macro_key).unwrap().fingerprint, ck.reads.get(&key).unwrap().fingerprint);
        });
    }

    /// The frozen binding query answers per namespace behind today's
    /// single-file resolver, and records each key once.
    #[test]
    fn binding_query_answers_per_namespace() {
        with_program(SAMPLE, |interner, p| {
            let mut reads = Reads::new();
            let helper = p.binding(&mut reads, ROOT_MODULE, Namespace::Value, interner.intern("helper"));
            let BindingRes::Def(helper_def) = helper else { panic!("helper must resolve: {helper:?}") };
            assert_eq!(p.binding_kind(helper_def), Some(DefsKind::Fn));
            // A struct answers in both namespaces with the same def.
            let as_ty = p.binding(&mut reads, ROOT_MODULE, Namespace::Type, interner.intern("Foo"));
            let as_val = p.binding(&mut reads, ROOT_MODULE, Namespace::Value, interner.intern("Foo"));
            assert_eq!(as_ty, as_val);
            assert_eq!(
                p.binding_kind(match as_ty {
                    BindingRes::Def(d) => d,
                    _ => unreachable!(),
                }),
                Some(DefsKind::Struct)
            );
            // Builtin types resolve in the type namespace only.
            let b = p.tys.builtins();
            assert_eq!(p.binding(&mut reads, ROOT_MODULE, Namespace::Type, interner.intern("String")), BindingRes::Def(b.string));
            assert_eq!(p.binding(&mut reads, ROOT_MODULE, Namespace::Value, interner.intern("String")), BindingRes::Absent);
            // One module today: any other module is absent, and a repeated
            // query records nothing new.
            assert_eq!(p.binding(&mut reads, ModuleId(9), Namespace::Value, interner.intern("helper")), BindingRes::Absent);
            let n = reads.len();
            let _ = p.binding(&mut reads, ROOT_MODULE, Namespace::Value, interner.intern("helper"));
            assert_eq!(reads.len(), n, "the same key records once");
        });
    }

    /// Method-set probes split by receiver form, and an associated fn with
    /// no `self` surfaces only in the first probe, marked as no receiver.
    #[test]
    fn method_set_splits_by_receiver_form() {
        let src = "\
struct Foo { x: i64 }
impl Foo {
    fn make() -> Foo { Foo { x: 1 } }
    fn bump(&mut self) { self.x += 1; }
}
fn main() {}
";
        with_program(src, |interner, p| {
            let head = foo_head(p, interner);
            let mut reads = Reads::new();
            let make = p.method_set(&mut reads, head, interner.intern("make"), ReceiverForm::Value);
            assert_eq!(make.first().map(|c| c.receiver), Some(None), "assoc fn has no receiver");
            assert!(p.method_set(&mut reads, head, interner.intern("make"), ReceiverForm::Ref).candidates.is_empty());
            assert!(p.method_set(&mut reads, head, interner.intern("bump"), ReceiverForm::Value).candidates.is_empty());
            assert!(p.method_set(&mut reads, head, interner.intern("bump"), ReceiverForm::Ref).candidates.is_empty());
            let bump = p.method_set(&mut reads, head, interner.intern("bump"), ReceiverForm::RefMut);
            assert_eq!(bump.first().map(|c| (c.receiver, c.trait_)), Some((Some(ReceiverForm::RefMut), None)));
            // A miss on a primitive head still records, as a failed read.
            assert!(p.method_set(&mut reads, Head::Int(IntTy::I64), interner.intern("nope"), ReceiverForm::Value).candidates.is_empty());
            let key =
                ReadKey::MethodSet(MethodSetKey { head: Head::Int(IntTy::I64), name: interner.intern("nope"), form: ReceiverForm::Value });
            assert_eq!(reads.get(&key).map(|r| r.failed), Some(true));
        });
    }

    /// A def that is not a user trait reads an empty bucket, recorded as a
    /// failed lookup.
    #[test]
    fn impl_set_records_the_empty_bucket() {
        with_program(SAMPLE, |interner, p| {
            let mut reads = Reads::new();
            let any_trait = p.def_id(p.fn_names[&interner.intern("helper")]);
            let head = foo_head(p, interner);
            assert!(p.impl_set(&mut reads, any_trait, head).impls.is_empty());
            let key = ReadKey::ImplSet(ImplSetKey { trait_: any_trait, head });
            assert_eq!(reads.get(&key).map(|r| r.failed), Some(true));
            // The layout query answers for a known Adt and fails the read for
            // a def this crate does not have.
            let Head::Adt(adt) = head else { unreachable!() };
            assert!(p.layout_of(&mut reads, adt).is_some());
            let missing = DefId { krate: p.krate, hash: DefPathHash(0xdead) };
            assert_eq!(p.layout_of(&mut reads, missing), None);
            assert_eq!(reads.get(&ReadKey::Layout(missing)).map(|r| r.failed), Some(true));
        });
    }

    /// A user trait's bucket holds the impls for the head (through
    /// references) and the blankets, and its read moves when an impl joins
    /// the bucket or an impl in it changes; an impl for another head does
    /// not move it.
    #[test]
    fn impl_set_buckets_follow_user_trait_impls() {
        let base = "trait Tr { fn go(&self) -> i64; }\nstruct A;\nstruct B;\nimpl Tr for A { fn go(&self) -> i64 { 1 } }\nfn main() {}\n";
        let read = |src: &str| -> (usize, Fingerprint) {
            let mut out = (0, Fingerprint(0));
            with_program(src, |interner, p| {
                let mut reads = Reads::new();
                let tr = p.gx.trait_names[&interner.intern("Tr")];
                let head = Head::Adt(p.def_of_adt(p.type_names[&interner.intern("A")]));
                let n = p.impl_set(&mut reads, tr, head).impls.len();
                out = (n, reads.get(&ReadKey::ImplSet(ImplSetKey { trait_: tr, head })).unwrap().fingerprint);
            });
            out
        };
        let (n, fp) = read(base);
        assert_eq!(n, 1);
        let blanket = base.replace("fn main", "impl<T: Copy> Tr for &T { fn go(&self) -> i64 { 3 } }\nfn main");
        assert_eq!(read(&blanket).0, 2, "a blanket impl joins every bucket");
        let other = base.replace("fn main", "impl Tr for B { fn go(&self) -> i64 { 2 } }\nfn main");
        assert_eq!(read(&other), (1, fp), "an impl for another head keeps the read");
        let reff = base.replace("impl Tr for A", "impl Tr for &A");
        assert_ne!(read(&reff).1, fp, "an impl header edit moves the read");
    }

    /// A signature edit that keeps every name (so every DefId is the same)
    /// must still move the `Sig` fingerprint: the fingerprint is over
    /// resolved types, not identity.
    #[test]
    fn sig_fingerprint_tracks_signature_types() {
        let fp_of = |src: &str| -> Fingerprint {
            let mut out = Fingerprint(0);
            with_program(src, |interner, p| {
                let mut reads = Reads::new();
                let def = p.def_id(p.fn_names[&interner.intern("f")]);
                let _ = p.sig_of(&mut reads, def);
                out = reads.get(&ReadKey::Sig(def)).unwrap().fingerprint;
            });
            out
        };
        let a = fp_of("fn f(x: i64) -> i64 { x }\nfn main() {}\n");
        let same = fp_of("fn f(x: i64) -> i64 { x + 1 }\nfn main() {}\n");
        let changed = fp_of("fn f(x: bool) -> i64 { 1 }\nfn main() {}\n");
        assert_eq!(a, same, "a body edit does not move the signature fingerprint");
        assert_ne!(a, changed, "a parameter type edit does");
    }

    /// Non-generic instance keys hash exactly like today's disk-def slot
    /// keys, and lifetime args never enter the hash (section 4.2).
    #[test]
    fn instance_key_hash_erases_lifetimes() {
        with_program(SAMPLE, |interner, p| {
            let f = p.fn_names[&interner.intern("helper")];
            let key = p.instance_key(f);
            let hash = p.instance_key_hash(&key);
            assert_eq!(key.args, EMPTY_ARGS);
            assert_eq!(hash, InstanceKeyHash::of_disk_def(p.disk_id(f), InstanceKeyHash::empty_args_fingerprint()));
            let lt_args = p.tys.intern_args(&[GenericArg::Lifetime(Region::Static)]);
            let lt_key = InstanceKey { def: key.def, args: lt_args };
            assert_eq!(p.instance_key_hash(&lt_key), hash, "lifetime args are erased");
            let ty_args = p.tys.intern_args(&[GenericArg::Ty(int(IntTy::I64))]);
            let ty_key = InstanceKey { def: key.def, args: ty_args };
            assert_ne!(p.instance_key_hash(&ty_key), hash, "type args are not");
            // The type fingerprint helper behind these hashes is structural:
            // equal types built twice hash equal, different types do not.
            assert_eq!(ty_fingerprint(p, int(IntTy::I64)), ty_fingerprint(p, int(IntTy::I64)));
            assert_ne!(ty_fingerprint(p, int(IntTy::I64)), ty_fingerprint(p, BOOL));
        });
    }

    /// The section 4.2 slot rule in miniature: one new slot leaves every
    /// unrelated unit's used-slots hash alone and moves only the full
    /// manifest hash (the table unit's key).
    #[test]
    fn used_slots_hash_survives_a_new_slot() {
        let disk = |k: u64, h: u64| DiskDefId { krate: StableCrateHash(k), hash: DefPathHash(h) };
        let key = |k: u64, h: u64| InstanceKeyHash::of_disk_def(disk(k, h), InstanceKeyHash::empty_args_fingerprint());
        let mut slot_of = FxMap::default();
        slot_of.insert(disk(1, 10), 0);
        slot_of.insert(disk(1, 20), 1);
        slot_of.insert(disk(1, 30), 2);
        let mut m = SlotManifest::from_disk_slots(&slot_of);
        assert_eq!(m.len(), 3);
        assert_eq!(m.slot_of(key(1, 20)), Some(1));
        let unit = [key(1, 10), key(1, 30)];
        let before = m.used_slots_hash(&unit).unwrap();
        let table_before = m.manifest_hash();
        // One new reachable instance: append-only, old slots stay put.
        assert_eq!(m.assign(key(1, 99)), 3);
        assert_eq!(m.assign(key(1, 99)), 3, "assign is stable");
        assert_eq!(m.slot_of(key(1, 10)), Some(0));
        assert_eq!(m.used_slots_hash(&unit), Some(before), "unrelated units keep their key");
        assert_ne!(m.manifest_hash(), table_before, "the table unit rebuilds");
        assert_eq!(m.used_slots_hash(&[key(7, 7)]), None, "a key with no slot cannot key a unit");
    }

    /// The lowered sample body carries the read set with it, and every call
    /// in it is a terminator with a cleanup (unwind) successor.
    #[test]
    fn lowered_body_carries_reads_and_call_terminators() {
        use crate::ir::{CallTarget, Terminator};
        with_program(SAMPLE, |interner, p| {
            let main = p.main.unwrap();
            let (ck, errs) = check_fn(p, main);
            assert!(errs.is_empty(), "{errs:?}");
            let body = crate::lower::lower(p, main, ck);
            let key = ReadKey::Binding(BindingKey { module: ROOT_MODULE, ns: Namespace::Value, name: interner.intern("helper") });
            assert!(body.reads.contains(&key), "the read set rides with the body result");
            let (mut fn_calls, mut builtin_calls) = (0, 0);
            for b in &body.blocks {
                if let Terminator::Call { target, unwind, .. } = &b.term {
                    assert!(unwind.is_some(), "every call carries a cleanup edge (W-CORELANG)");
                    match target {
                        CallTarget::Fn(_) | CallTarget::Indirect(_) | CallTarget::Dyn(_) => fn_calls += 1,
                        CallTarget::Builtin(_) | CallTarget::Intrinsic(_) => builtin_calls += 1,
                    }
                }
            }
            assert!(fn_calls >= 2, "helper() and f.get() are fn call terminators, got {fn_calls}");
            let _ = builtin_calls;
            assert!(crate::borrowck::borrowck(p, &body).is_empty(), "the sample borrow-checks clean");
        });
    }

    /// Collects `src` under a shared interner (as one session does across
    /// requests) and returns main's recorded reads. The program itself is
    /// dropped; reads hold only stable keys (`Sym` in the shared
    /// interner, path-hash `DefId`s), so they replay against the next
    /// program built on the same interner.
    fn main_reads(interner: &std::sync::Arc<Interner>, known: &std::sync::Arc<Known>, src: &str) -> Reads {
        let lexed = lexer::lex(src, FileId(0), 0, interner).unwrap();
        let ast = parser::parse(&lexed, interner, known).unwrap();
        let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        let (ck, _) = check_fn(&program, program.main.unwrap());
        ck.reads
    }

    /// Dirty counts of `reads` replayed against a fresh collect of `src`
    /// on the same interner. See `main_reads`.
    fn dirty_in(interner: &std::sync::Arc<Interner>, known: &std::sync::Arc<Known>, src: &str, reads: &Reads) -> usize {
        let lexed = lexer::lex(src, FileId(0), 0, interner).unwrap();
        let ast = parser::parse(&lexed, interner, known).unwrap();
        let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        program.reads_dirty(reads)
    }

    /// The dirty walk (8.3 step 5): an unrelated added fn dirties nothing
    /// a body read; a callee signature edit, a moved method candidate,
    /// and a failed lookup that now resolves each dirty the body that
    /// read them (8.2 rule 3).
    #[test]
    fn dirty_walk_replays_reads_against_new_program() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let reads = main_reads(&interner, &known, SAMPLE);
        // Same program: clean by construction.
        assert_eq!(dirty_in(&interner, &known, SAMPLE, &reads), 0, "unchanged program");
        // One new unrelated pub fn: no read of main names it, so the walk
        // reuses main (the scale-gate new-fn scenario in miniature).
        let added = format!("{SAMPLE}fn extra() -> i64 {{ 3 }}\n");
        assert_eq!(dirty_in(&interner, &known, &added, &reads), 0, "unrelated fn added");
        // Callee signature edit (helper returns bool now): the Sig read
        // and the Binding read (sig folded in) both move.
        let sig_edit = SAMPLE.replace("fn helper() -> i64 { 40 }", "fn helper() -> bool { true }");
        assert!(dirty_in(&interner, &known, &sig_edit, &reads) >= 2, "callee sig edit dirties");
        // Method receiver edit (&self -> &mut self): the recorded Ref
        // probe hit becomes a miss, so the method-set read moves.
        let method_edit = SAMPLE.replace("fn get(&self)", "fn get(&mut self)");
        assert!(dirty_in(&interner, &known, &method_edit, &reads) >= 1, "method probe edit dirties");
        // Failed lookup: a body that called a missing fn rechecks once
        // the fn exists, and only because its failed Binding read moved.
        let failing = main_reads(&interner, &known, "fn main() { println!(\"{}\", nosuch()); }\n");
        assert_eq!(dirty_in(&interner, &known, "fn main() { println!(\"{}\", nosuch()); }\n", &failing), 0, "still missing");
        let fixed = "fn nosuch() -> i64 { 1 }\nfn main() { println!(\"{}\", nosuch()); }\n";
        assert!(dirty_in(&interner, &known, fixed, &failing) >= 1, "added def dirties the failed lookup");
    }

    /// Type edits dirty through deep signature fingerprints: a body
    /// that only receives a struct from a callee and reads a nested
    /// field rechecks when the nested type changes, and stays clean
    /// when an unrelated type changes. This is what lets the dirty
    /// walk run in full mode (type edits), not only on signature text.
    #[test]
    fn dirty_walk_covers_type_edits_through_deep_sigs() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let src = "\
struct Inner { x: i64 }
struct Outer { f: Inner }
struct Unused { n: i64 }
fn make() -> Outer { Outer { f: Inner { x: 1 } } }
fn main() { let v = make(); println!(\"{}\", v.f.x); }
";
        let reads = main_reads(&interner, &known, src);
        assert_eq!(dirty_in(&interner, &known, src, &reads), 0, "unchanged");
        let nested = src.replace("struct Inner { x: i64 }", "struct Inner { x: bool }");
        assert!(dirty_in(&interner, &known, &nested, &reads) >= 1, "nested field type edit dirties through make's Sig");
        // Derive lists left the layout (P3.3): a body dirties on a derive
        // edit only through its own Derives / DeriveBits reads.
        let derive = src.replace("struct Inner { x: i64 }", "#[derive(Clone)]\nstruct Inner { x: i64 }");
        assert_eq!(dirty_in(&interner, &known, &derive, &reads), 0, "a derive edit main never asks about stays clean");
        let unrelated = src.replace("struct Unused { n: i64 }", "struct Unused { n: bool }");
        assert_eq!(dirty_in(&interner, &known, &unrelated, &reads), 0, "unrelated type edit stays clean");
    }

    /// The layout fingerprint is its own node: it moves on field edits,
    /// not on a method or derive edit of the same type, and
    /// `layout_of` records it so the walk replays it.
    /// Deep fingerprints (`adt_deep`) over a type graph with a shared
    /// sub-type and a cycle: the same values with the program memo on or
    /// off, in any order, and for any item order in the source; an edit
    /// moves every type that reaches it and no other.
    #[test]
    fn deep_fingerprints_are_memo_and_order_free() {
        const SRC: &str = "struct A { b: Box<B>, c: C }\nstruct B { a: Option<Box<A>>, x: u8 }\nstruct C { x: u32 }\n\
                           struct D { a: A, c: C, e: (C, [C; 2]) }\nfn main() {}\n";
        fn fps(src: &str, memo: bool, rev: bool) -> Vec<(Fingerprint, Fingerprint)> {
            let mut out = Vec::new();
            with_program(src, |interner, p| {
                if memo {
                    p.fp_memo.on(p.adts.len());
                }
                let mut names = ["A", "B", "C", "D"];
                if rev {
                    names.reverse();
                }
                for n in names {
                    let def = p.def_of_adt(p.type_names[&interner.intern(n)]);
                    out.push((layout_fingerprint(p, def), sig_fingerprint(p, def)));
                }
                if rev {
                    out.reverse();
                }
            });
            out
        }
        let base = fps(SRC, false, false);
        assert_eq!(fps(SRC, true, false), base, "the program memo keeps the values");
        assert_eq!(fps(SRC, true, true), base, "walk order does not matter");
        let moved = SRC.replace("struct C { x: u32 }\n", "").replace("fn main", "struct C { x: u32 }\nfn main");
        assert_eq!(fps(&moved, true, false), base, "item order does not matter");
        let layouts = |v: &[(Fingerprint, Fingerprint)]| v.iter().map(|x| x.0).collect::<Vec<_>>();
        let (b, c) = (layouts(&base), layouts(&fps(&SRC.replace("x: u32", "x: u64"), true, false)));
        assert!(b.iter().zip(&c).all(|(x, y)| x != y), "C's edit moves A, B (through A), C, and D");
        let c = layouts(&fps(&SRC.replace("x: u8", "x: u16"), true, false));
        assert_eq!((b[0] != c[0], b[1] != c[1], b[2] != c[2], b[3] != c[3]), (true, true, false, true), "B's edit moves its cycle and D");
    }

    /// The memo that follows mono (`FpMemo::sync`): a table the deep
    /// walk reads grows (a glue method for C), and the next sync drops the
    /// values made before, so A's fingerprint is the fresh one again.
    #[test]
    fn followed_memo_drops_values_when_walk_inputs_grow() {
        const SRC: &str = "struct A { c: C }\nstruct C { x: u32 }\nfn main() {}\n";
        with_program(SRC, |interner, p| {
            let def = p.def_of_adt(p.type_names[&interner.intern("A")]);
            let c = p.type_names[&interner.intern("C")];
            p.fp_memo.follow_begin();
            FpMemo::sync(p);
            let before = layout_fingerprint(p, def);
            p.gx.glue_methods.insert((c, p.gx.lang.clone), LocalDefId(0));
            assert_eq!(layout_fingerprint(p, def), before, "the memo holds the old value until the next sync");
            FpMemo::sync(p);
            let after = layout_fingerprint(p, def);
            p.fp_memo.follow_end();
            assert!(p.fp_memo.layout.is_empty(), "a followed memo is off again after mono");
            assert_ne!(after, before, "C's glue moves A");
            assert_eq!(layout_fingerprint(p, def), after, "the synced value is the fresh walk's");
        });
    }

    #[test]
    fn layout_fingerprint_tracks_layout_not_methods() {
        fn layout_of_src(src: &str) -> Fingerprint {
            let interner = std::sync::Arc::new(Interner::default());
            let known = std::sync::Arc::new(Known::new(&interner));
            let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
            let ast = parser::parse(&lexed, &interner, &known).unwrap();
            let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
            let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
            let a = program.type_names[&interner.intern("Foo")];
            layout_fingerprint(&program, program.def_of_adt(a))
        }
        let base = "struct Foo { x: i64 }\nimpl Foo { fn get(&self) -> i64 { self.x } }\nfn main() {}\n";
        let method_edit = base.replace("fn get(&self) -> i64 { self.x }", "fn get(&self) -> i64 { self.x + 1 }");
        assert_eq!(layout_of_src(base), layout_of_src(&method_edit), "method body edit keeps the layout");
        let field_edit = base.replace("struct Foo { x: i64 }", "struct Foo { x: i64, y: i64 }");
        assert_ne!(layout_of_src(base), layout_of_src(&field_edit), "field edit moves the layout");
        // Derive lists are their own reads (Derives, DeriveBits), not
        // layout content (sigedit P3.3).
        let derive_edit = base.replace("struct Foo", "#[derive(Clone)]\nstruct Foo");
        assert_eq!(layout_of_src(base), layout_of_src(&derive_edit), "a derive edit keeps the layout fingerprint");
        let eq_base = base.replace("struct Foo", "#[derive(PartialEq, Eq, Hash)]\nstruct Foo");
        for (from, to) in [("Eq, Hash", "Hash"), ("Eq, Hash", "Eq")] {
            let edited = eq_base.replace(from, to);
            assert_eq!(layout_of_src(&eq_base), layout_of_src(&edited), "an `Eq` or `Hash` derive edit keeps the layout");
        }
        with_program(base, |interner, p| {
            let a = p.type_names[&interner.intern("Foo")];
            let def = p.def_of_adt(a);
            let mut reads = Reads::new();
            let fp = p.layout_of(&mut reads, def).expect("known adt");
            assert_eq!(reads.get(&ReadKey::Layout(def)).map(|r| r.fingerprint), Some(fp));
            assert_eq!(p.read_fingerprint(&ReadKey::Layout(def)).fingerprint, fp, "replay agrees with the recording");
            assert_ne!(fp, sig_fingerprint(p, def), "layout is a separate fingerprint from sig");
        });
    }

    /// `Sig` covers member visibility (ARCH 8.1): the field and method
    /// privacy checks record a `Sig(adt)` read, and a visibility-only
    /// edit moves that fingerprint (so the stored read is dirty) while
    /// the layout stands. The tables are built by hand here; the daemon
    /// cases in scripts/fuzz/smoke.py run the same edge end to end.
    #[test]
    fn sig_covers_member_visibility() {
        let src = "struct Foo { x: i64 }\nimpl Foo { fn get(&self) -> i64 { self.x } }\n\
                   fn make() -> Foo { Foo { x: 1 } }\nfn main() { let n = make().x + make().get(); println!(\"{}\", n); }\n";
        with_program(src, |interner, p| {
            let def = p.def_of_adt(p.type_names[&interner.intern("Foo")]);
            let main_reads = |p: &Program| {
                let (ck, errs) = check_fn(p, p.main.unwrap());
                assert!(errs.is_empty(), "{errs:?}");
                ck.reads.clone()
            };
            // No module tables: one module, no privacy check, no read.
            assert!(!main_reads(p).contains(&ReadKey::Sig(def)));
            let mut tables = ResolvedTables::new(interner.intern("test"));
            tables.field_vis.insert(def, (ROOT_MODULE, [(interner.intern("x"), VisKind::Pub)].into_iter().collect()));
            tables.assoc_vis.insert(def, [(interner.intern("get"), (VisKind::Pub, ROOT_MODULE))].into_iter().collect());
            p.resolved = Some(std::sync::Arc::new(tables));
            let stored = main_reads(p);
            let (sig, layout) = (sig_fingerprint(p, def), layout_fingerprint(p, def));
            assert_eq!(stored.get(&ReadKey::Sig(def)).map(|r| r.fingerprint), Some(sig), "privacy checks read Sig(Foo)");
            assert_eq!(p.reads_dirty(&stored), 0);
            let t = std::sync::Arc::get_mut(p.resolved.as_mut().unwrap()).unwrap();
            t.field_vis.get_mut(&def).unwrap().1.insert(interner.intern("x"), VisKind::Priv);
            assert_ne!(sig_fingerprint(p, def), sig, "a field visibility edit moves Sig");
            assert_eq!(layout_fingerprint(p, def), layout, "and not the layout");
            assert!(p.reads_dirty(&stored) > 0, "the field reader is dirty");
            let t = std::sync::Arc::get_mut(p.resolved.as_mut().unwrap()).unwrap();
            t.field_vis.get_mut(&def).unwrap().1.insert(interner.intern("x"), VisKind::Pub);
            assert_eq!(sig_fingerprint(p, def), sig, "the edit back restores Sig");
            let t = std::sync::Arc::get_mut(p.resolved.as_mut().unwrap()).unwrap();
            t.assoc_vis.get_mut(&def).unwrap().insert(interner.intern("get"), (VisKind::Crate, ROOT_MODULE));
            assert_ne!(sig_fingerprint(p, def), sig, "a method visibility edit moves Sig");
            assert!(p.reads_dirty(&stored) > 0, "the method caller is dirty");
        });
    }

    /// A body that copies an Adt only inside a tuple and clones it only
    /// inside an Option names no signature that holds it, yet its answer
    /// reads the Adt's derive list: it records a derive read of the trait
    /// it asks, which an edit of that trait dirties and an unrelated
    /// derive edit does not (R12).
    #[test]
    fn derive_answers_record_derives_reads() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let src = "#[derive(Clone, Copy)]\nstruct A { x: u8 }\n#[derive(Clone)]\nstruct U;\n\
                   fn main() { let t = (A { x: 1 }, 2u8); let u = t; let o = Some(A { x: 3 }); let p = o.clone(); \
                   println!(\"{} {} {}\", t.0.x, u.0.x, p.unwrap().x); }\n";
        let reads = main_reads(&interner, &known, src);
        assert!(reads.keys().any(|k| matches!(k, ReadKey::Derives(_) | ReadKey::DeriveBits(..))), "a derive read is recorded");
        assert_eq!(dirty_in(&interner, &known, src, &reads), 0, "unchanged");
        // Per trait (DeriveBits): the type check asks A only about Clone
        // (`o.clone()`). The tuple copy is borrowck's question, which the
        // driver's body scope records as its own read.
        let no_copy = src.replacen("#[derive(Clone, Copy)]", "#[derive(Clone)]", 1);
        assert_eq!(dirty_in(&interner, &known, &no_copy, &reads), 0, "-Copy on A: the type check never asked about Copy");
        let neither = src.replacen("#[derive(Clone, Copy)]\nstruct A", "struct A", 1);
        assert!(dirty_in(&interner, &known, &neither, &reads) >= 1, "-Clone on A dirties o.clone()");
        let unrelated = src.replacen("#[derive(Clone)]\nstruct U;", "#[derive(Clone, Copy)]\nstruct U;", 1);
        assert_eq!(dirty_in(&interner, &known, &unrelated, &reads), 0, "+Copy on an Adt main never asks about stays clean");
    }

    /// A const def's `Sig` fingerprint folds its evaluated value: a
    /// value edit moves it, a same-value rephrase does not (ARCH 8.1).
    #[test]
    fn const_sig_fingerprint_tracks_the_value() {
        fn const_fp(src: &str) -> Fingerprint {
            let interner = std::sync::Arc::new(Interner::default());
            let known = std::sync::Arc::new(Known::new(&interner));
            let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
            let ast = parser::parse(&lexed, &interner, &known).unwrap();
            let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
            let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
            let hash = crate::def::item_hash(ids.stable, &[], crate::def::DefKind::Const, "MAX", 0);
            sig_fingerprint(&program, DefId { krate: ids.local, hash })
        }
        let a = const_fp("const MAX: i64 = 3;\nfn main() { println!(\"{}\", MAX); }\n");
        let changed = const_fp("const MAX: i64 = 4;\nfn main() { println!(\"{}\", MAX); }\n");
        assert_ne!(a, changed, "value edit moves the const sig");
        let same = const_fp("const MAX: i64 = 1 + 2;\nfn main() { println!(\"{}\", MAX); }\n");
        assert_eq!(a, same, "same value, same fingerprint");
    }

    /// A const used as a pattern records its `Sig` read: a value edit
    /// dirties the matching body, an unrelated const edit does not.
    /// (Review B2: the pattern path used to read the flat const table
    /// with no recorded read, so a warm daemon kept the old value.)
    #[test]
    fn pattern_const_read_dirties_on_value_edit() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let src = "const K: i64 = 3;\nconst U: i64 = 9;\nfn main() { let x: i64 = 3; println!(\"{}\", match x { K => 1, _ => 0 }); }\n";
        let reads = main_reads(&interner, &known, src);
        assert_eq!(dirty_in(&interner, &known, src, &reads), 0, "unchanged");
        let edited = src.replace("const K: i64 = 3;", "const K: i64 = 4;");
        assert!(dirty_in(&interner, &known, &edited, &reads) >= 1, "pattern const value edit dirties");
        let unrelated = src.replace("const U: i64 = 9;", "const U: i64 = 10;");
        assert_eq!(dirty_in(&interner, &known, &unrelated, &reads), 0, "unrelated const edit stays clean");
    }

    /// A const fn body evaluated while checking a body records a
    /// `Checked` read, whose replay never matches: the reader
    /// rechecks whenever it is a walk candidate, even against the
    /// same program. That is the transitive edge from a body to the
    /// const fn bodies it evaluates (review B1, body-local half).
    #[test]
    fn const_block_call_records_checked_read() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let src = "const fn k() -> i64 { 3 }\nfn main() { let x = const { k() }; println!(\"{}\", x); }\n";
        let reads = main_reads(&interner, &known, src);
        assert!(reads.keys().any(|k| matches!(k, ReadKey::Checked(_))), "a Checked read is recorded");
        assert!(dirty_in(&interner, &known, src, &reads) >= 1, "Checked reads always dirty (sentinel replay)");
    }

    /// `size_of` over a compound type records a layout read for the
    /// Adt inside it: a field edit dirties the body even though the
    /// written type's outermost path is not the Adt.
    #[test]
    fn size_of_compound_type_records_layout_read() {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let src = "struct S { a: u8 }\nfn main() { println!(\"{}\", std::mem::size_of::<[S; 2]>()); }\n";
        let reads = main_reads(&interner, &known, src);
        assert!(reads.keys().any(|k| matches!(k, ReadKey::Layout(_))), "a Layout read is recorded");
        assert_eq!(dirty_in(&interner, &known, src, &reads), 0, "unchanged");
        let edited = src.replace("struct S { a: u8 }", "struct S { a: u64 }");
        assert!(dirty_in(&interner, &known, &edited, &reads) >= 1, "field edit dirties through the layout read");
    }

    /// A builtin method probe records the probe itself: two different
    /// builtin method names on the same head have different empty-set
    /// fingerprints, so the recorded read names the answer the compat
    /// dispatch gave, not a shared "empty bucket".
    #[test]
    fn builtin_method_probe_records_the_probe() {
        with_program("fn main() { let mut v = Vec::new(); v.push(1); println!(\"{}\", v.len()); }\n", |interner, p| {
            let (ck, _) = check_fn(p, p.main.unwrap());
            let vec_def = p.tys.builtins().vec;
            let push_key =
                ReadKey::MethodSet(MethodSetKey { head: Head::Adt(vec_def), name: interner.intern("push"), form: ReceiverForm::Value });
            let recorded = ck.reads.get(&push_key).expect("the push probe is recorded");
            assert!(recorded.failed, "no user candidate: a failed (builtin) probe");
            let pop_key =
                ReadKey::MethodSet(MethodSetKey { head: Head::Adt(vec_def), name: interner.intern("pop"), form: ReceiverForm::Value });
            assert_ne!(
                recorded.fingerprint,
                p.read_fingerprint(&pop_key).fingerprint,
                "different builtin probes have different fingerprints"
            );
            assert_eq!(recorded.fingerprint, p.read_fingerprint(&push_key).fingerprint, "replay agrees");
        });
    }

    /// The instance slot manifest survives a restart in any discovery
    /// order (4.2): decode gives every old instance its old slot, and bad
    /// bytes never decode.
    #[test]
    fn instance_manifest_round_trips() {
        let key = |h: u64| {
            InstanceKeyHash::of_disk_def(
                DiskDefId { krate: StableCrateHash(1), hash: DefPathHash(h) },
                InstanceKeyHash::empty_args_fingerprint(),
            )
        };
        let mut m = SlotManifest::new();
        // Discovery order 30, 10, 20 in the first daemon.
        assert_eq!(m.assign(key(30)), 0);
        assert_eq!(m.assign(key(10)), 1);
        assert_eq!(m.assign(key(20)), 2);
        let mut back = SlotManifest::decode(&m.encode()).unwrap();
        // A restarted daemon discovers in the opposite order.
        assert_eq!(back.assign(key(20)), 2, "old instance keeps its slot");
        assert_eq!(back.assign(key(10)), 1);
        assert_eq!(back.assign(key(30)), 0);
        assert_eq!(back.key_at(2), Some(key(20)));
        // Bad bytes never decode to wrong slots.
        let bytes = m.encode();
        assert_eq!(SlotManifest::decode(&bytes[..bytes.len() - 1]).map(|d| d.len()), None, "truncated");
        let mut dup = bytes.clone();
        dup[16..24].copy_from_slice(&bytes[8..16]);
        assert!(SlotManifest::decode(&dup).is_none(), "one instance in two slots");
    }
}
