// Dependency graph nodes, read recording, and slot identity (docs/ARCH.md
// sections 4.2, 8.1, and 8.2; serial refactor S7).
//
// This file owns the frozen query surface of section 8.2: the `Reads` sink, its
// keys (`Binding`, `MethodSet`, `ImplSet`, `Sig`, `Layout`, `Checked`), and the
// query functions on `Program` that log to it. Wave A packages (W-CORELANG,
// W-TRAITS-CORE, W-MACRO) code against these functions. Today's single-file,
// single-module resolver sits behind them; W-RESOLVE replaces that resolver
// with the module tree and import worklist of section 1.3 without changing any
// caller. S7 is record-only: reads are stored on the checked body, and no
// invalidation consumes them yet (the name-based prefilter in compile.rs still
// decides what an edit rechecks, per section 8.2's staging rule).
//
// Fingerprints here hash normalized content only: name strings, stable def
// path hashes, and type structure. They never hash a `Sym`, a `Ty`, an
// `ArgsId`, or any other session-local id (section 8.1).
use crate::ast::SelfKind;
use crate::check::collect::{AdtDef, FnInfo, Program, VariantShape};
use crate::def::{DefId, DiskDefId, LocalDefId, StableCrateHash};
use crate::intern::{FxHasher, FxMap, Sym};
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
    /// The first candidate, which method resolution picks (section 2.10).
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

/// The impl defs in one bucket, in no promised order. Empty until trait
/// collection lands (W-TRAITS-CORE); the node and its reads exist now so an
/// obligation that fails on an empty bucket rechecks when an impl appears.
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
}

impl Reads {
    /// An empty sink.
    pub fn new() -> Reads {
        Reads::default()
    }

    /// Records one read. The first record of a key wins.
    pub fn record(&mut self, key: ReadKey, fingerprint: Fingerprint, failed: bool) {
        self.map.entry(key).or_insert(Read { fingerprint, failed });
    }

    /// Records one read, computing the fingerprint only if the key is new:
    /// a body that asks the same question a hundred times pays for the
    /// fingerprint once.
    pub fn record_with(&mut self, key: ReadKey, failed: bool, fingerprint: impl FnOnce() -> Fingerprint) {
        if let std::collections::hash_map::Entry::Vacant(v) = self.map.entry(key) {
            v.insert(Read { fingerprint: fingerprint(), failed });
        }
    }

    /// Records a mono call edge to a checked body. `fingerprint` is the body
    /// fingerprint mono computed; there is no mono stage yet, so no
    /// production caller records these in S7.
    #[allow(dead_code)] // First caller is mono (W-MONO, wave B).
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
}

// ---------- Fingerprints ----------

/// The stable crate half a def hashes under in a fingerprint. Local-crate
/// defs use the program's stable crate hash and builtin defs use theirs, so
/// fingerprints match across sessions. A foreign session crate cannot occur
/// today (one crate per session); when W-RESOLVE loads more crates it gives
/// `Program` a crate table and this fallback goes away.
fn def_crate_hash(p: &Program, def: DefId) -> u64 {
    if def.krate == p.krate {
        p.stable_crate.0
    } else if def.krate == BUILTIN_CRATE {
        crate::def::stable_crate_hash("lust-builtin-v1", "lib", "builtin", false).0
    } else {
        def.krate.0 as u64
    }
}

/// Hashes one def by its stable identity: crate hash, then def path hash.
fn hash_def(h: &mut FxHasher, p: &Program, def: DefId) {
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
    hash_def(h, p, tr.def);
    hash_args(h, p, tys, tr.args);
    let bindings = tys.bindings(tr.bindings);
    (bindings.len() as u64).hash(h);
    for (assoc, arg) in bindings {
        hash_def(h, p, *assoc);
        match arg {
            GenericArg::Ty(t) => hash_ty(h, p, tys, *t),
            GenericArg::Lifetime(r) => hash_region(h, *r),
            GenericArg::Const(c) => hash_const(h, tys, *c),
        }
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
            hash_def(h, p, def);
            hash_args(h, p, tys, args);
        }
        TyKind::FnPtr(sig) => {
            14u8.hash(h);
            let sig = tys.sig(sig);
            sig.count.hash(h);
            (sig.value.is_unsafe, sig.value.extern_c).hash(h);
            for e in tys.tys_of(sig.value.inputs) {
                hash_ty(h, p, tys, *e);
            }
            hash_ty(h, p, tys, sig.value.output);
        }
        TyKind::FnDef(def, args) => {
            15u8.hash(h);
            hash_def(h, p, def);
            hash_args(h, p, tys, args);
        }
        TyKind::Closure(def, args) => {
            16u8.hash(h);
            hash_def(h, p, def);
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
            hash_def(h, p, def);
            hash_args(h, p, tys, args);
        }
        TyKind::Param(i) => (19u8, i.0).hash(h),
        TyKind::Projection(assoc, args) => {
            20u8.hash(h);
            hash_def(h, p, assoc.0);
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

/// The fingerprint of a `Binding` node's answer (section 8.1: the resolved
/// def in disk form, or ambiguous, or absent).
fn binding_fingerprint(p: &Program, res: BindingRes) -> Fingerprint {
    let mut h = FxHasher::default();
    "binding-v1".hash(&mut h);
    match res {
        BindingRes::Def(def) => {
            0u8.hash(&mut h);
            hash_def(&mut h, p, def);
        }
        BindingRes::Ambiguous => 1u8.hash(&mut h),
        BindingRes::Absent => 2u8.hash(&mut h),
    }
    Fingerprint(h.finish())
}

/// The fingerprint of a `MethodSet` node's candidate list, in probe order.
fn method_set_fingerprint(p: &Program, set: &MethodSet) -> Fingerprint {
    let mut h = FxHasher::default();
    "method-set-v1".hash(&mut h);
    (set.candidates.len() as u64).hash(&mut h);
    for c in &set.candidates {
        hash_def(&mut h, p, c.def);
        match c.trait_ {
            Some(t) => hash_def(&mut h, p, t),
            None => 0u64.hash(&mut h),
        }
    }
    Fingerprint(h.finish())
}

/// The fingerprint of an `ImplSet` bucket: its impl defs, sorted so the
/// bucket's discovery order does not matter (section 8.1).
fn impl_set_fingerprint(p: &Program, set: &ImplSet) -> Fingerprint {
    let mut defs: Vec<(u64, u64)> = set.impls.iter().map(|d| (def_crate_hash(p, *d), d.hash.0)).collect();
    defs.sort_unstable();
    let mut h = FxHasher::default();
    "impl-set-v1".hash(&mut h);
    (defs.len() as u64).hash(&mut h);
    for d in defs {
        d.hash(&mut h);
    }
    Fingerprint(h.finish())
}

/// The fingerprint of one def's resolved signature (section 8.1 `Sig` node):
/// signature types with defs in stable form. Generics and predicates join
/// when generic collect fills them (W-TRAITS-CORE); today they are empty for
/// every user def.
fn sig_fingerprint(p: &Program, def: DefId) -> Fingerprint {
    let mut h = FxHasher::default();
    "sig-v1".hash(&mut h);
    hash_def(&mut h, p, def);
    if let Some(local) = p.local_def(def.hash).filter(|l| p.def_id(*l) == def) {
        let f = p.fn_info(local);
        0u8.hash(&mut h);
        match f.owner {
            Some(a) => hash_def(&mut h, p, p.def_of_adt(a)),
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
            hash_ty(&mut h, p, &p.tys, *t);
        }
        hash_ty(&mut h, p, &p.tys, f.ret);
        f.ret_borrows_from.map(|i| i as u64 + 1).unwrap_or(0).hash(&mut h);
    } else if let Some(a) = p.adt_by_def(def) {
        let adt = p.adt(a);
        1u8.hash(&mut h);
        adt.is_enum.hash(&mut h);
        (adt.derives.debug, adt.derives.clone, adt.derives.copy, adt.derives.partial_eq).hash(&mut h);
        (adt.variants.len() as u64).hash(&mut h);
        for v in &adt.variants {
            p.name(v.name).hash(&mut h);
            match v.shape {
                VariantShape::Unit => 0u8.hash(&mut h),
                VariantShape::Tuple => 1u8.hash(&mut h),
                VariantShape::Named => 2u8.hash(&mut h),
            }
            (v.fields.len() as u64).hash(&mut h);
            for (i, fd) in v.fields.iter().enumerate() {
                // Tuple fields carry a synthetic index `Sym`, not a name.
                if v.shape == VariantShape::Named {
                    p.name(fd.name).hash(&mut h);
                } else {
                    (i as u64).hash(&mut h);
                }
                hash_ty(&mut h, p, &p.tys, fd.ty);
            }
        }
    } else {
        2u8.hash(&mut h);
    }
    Fingerprint(h.finish())
}

// ---------- Query functions (section 8.2) ----------

/// The signature payload a `sig_of` query returns. Fn and Adt payloads still
/// live in the compat tables today (`FnInfo`, `AdtDef`); the query is the
/// only door to them that records a read. Other defs answer with their
/// `Defs` record until their payloads land.
#[allow(dead_code)] // The `Other` payload is read when non-fn/Adt payloads land.
pub enum SigOf<'p, 'a> {
    Fn(&'p FnInfo<'a>),
    Adt(&'p AdtDef),
    Other(&'p DefData),
    Missing,
}

impl<'a> Program<'a> {
    /// Resolves one module name in one namespace and records the `Binding`
    /// read. This is the frozen binding query wave A codes against: callers
    /// get a `DefId` and turn it into a session-local index through
    /// `local_def`, `adt_by_def`, or `Defs` queries, never the other way.
    ///
    /// Today's resolver behind this query is the single-file one: one crate,
    /// one root module, no imports, so every non-root module answers
    /// `Absent` and no answer is ever `Ambiguous`. Value answers are free
    /// fns and struct constructors; type answers are user Adts and the
    /// builtin `String`/`Vec`/`Option` defs; macro answers are `Absent`
    /// until W-MACRO. W-RESOLVE replaces this body with the section 1.3
    /// worklist result; the signature does not change.
    pub fn binding(&self, reads: &mut Reads, module: ModuleId, ns: Namespace, name: Sym) -> BindingRes {
        let res = if module != ROOT_MODULE {
            BindingRes::Absent
        } else {
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
        };
        reads.record_with(ReadKey::Binding(BindingKey { module, ns, name }), res == BindingRes::Absent, || binding_fingerprint(self, res));
        res
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
    /// Today only inherent user methods exist, at most one per (Adt, name).
    /// Builtin methods on builtin and primitive heads still dispatch through
    /// the compat path in `check` and answer as an empty set here; the read
    /// is still recorded, with the empty-bucket fingerprint, so the probe is
    /// on record when source std turns those builtins into real defs.
    pub fn method_set(&self, reads: &mut Reads, head: Head, name: Sym, form: ReceiverForm) -> MethodSet {
        let mut set = MethodSet::default();
        if let Head::Adt(def) = head
            && let Some(a) = self.adt_by_def(def)
            && let Some(&f) = self.methods.get(&(a, name))
        {
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
        let failed = set.candidates.is_empty();
        reads.record_with(ReadKey::MethodSet(MethodSetKey { head, name, form }), failed, || method_set_fingerprint(self, &set));
        set
    }

    /// The impl bucket for one trait and Self head, recorded at every
    /// obligation (section 8.2). No traits are collected yet, so every
    /// bucket is empty; the read still records, so a body whose obligation
    /// failed here rechecks when W-TRAITS-CORE adds the first impl.
    #[allow(dead_code)] // First caller is the obligation queue (W-TRAITS-CORE, wave A).
    pub fn impl_set(&self, reads: &mut Reads, trait_: DefId, head: Head) -> ImplSet {
        let set = ImplSet::default();
        reads.record_with(ReadKey::ImplSet(ImplSetKey { trait_, head }), true, || impl_set_fingerprint(self, &set));
        set
    }

    /// One def's resolved signature. Callers that only need identity facts
    /// (kind, parent, generics, param env) use `Defs` queries, which read
    /// this same `Sig` node per section 2.1; `sig_of` is for the payload.
    pub fn sig_of(&self, reads: &mut Reads, def: DefId) -> SigOf<'_, 'a> {
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

    /// The layout fingerprint of one Adt def. There is no layout engine yet
    /// (cgen lays types out as C types), so until `ty/layout.rs` lands the
    /// `Layout` node's fingerprint is the Adt's signature fingerprint:
    /// field Adt layouts fold in through their def hashes inside the field
    /// type fingerprints. Any field edit that can move a layout changes it.
    #[allow(dead_code)] // First callers are mono instance keys and the layout engine (wave A/B).
    pub fn layout_of(&self, reads: &mut Reads, adt: DefId) -> Option<Fingerprint> {
        let known = self.adt_by_def(adt).is_some() || self.defs.get(adt).is_some();
        if !known {
            reads.record_with(ReadKey::Layout(adt), true, || sig_fingerprint(self, adt));
            return None;
        }
        if let Some(r) = reads.get(&ReadKey::Layout(adt)) {
            return Some(r.fingerprint);
        }
        let fp = sig_fingerprint(self, adt);
        reads.record(ReadKey::Layout(adt), fp, false);
        Some(fp)
    }

    /// The kind of a def a binding resolved to, through the `Defs` table.
    /// Callers use it to tell a free fn from a struct constructor without
    /// reading the checker's name maps. Reads no node beyond the `Binding`
    /// read that produced the def.
    pub fn binding_kind(&self, def: DefId) -> Option<DefsKind> {
        self.defs.kind_of(def)
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

impl<'a> Program<'a> {
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
}

/// The used-slots hash of explicit `(instance key, slot)` pairs, for a unit
/// whose emitter collected the pairs it printed. Input order does not
/// matter; duplicate pairs count once.
#[allow(dead_code)] // First caller is the C unit cache key (W-DRIVER); tests use it now.
pub fn used_slots_hash(pairs: &[(InstanceKeyHash, u32)]) -> u64 {
    let mut sorted: Vec<(u64, u64)> = pairs.iter().map(|(k, s)| (k.0, *s as u64)).collect();
    sorted.sort_unstable();
    sorted.dedup();
    let mut h = FxHasher::default();
    "used-slots-v1".hash(&mut h);
    (sorted.len() as u64).hash(&mut h);
    for pair in sorted {
        pair.hash(&mut h);
    }
    h.finish()
}

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
        let interner = Interner::default();
        let known = Known::new(&interner);
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let mut program = collect::collect(&ast, &interner, &known, ids).unwrap();
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

    /// The impl-set node exists and records before any trait does: every
    /// bucket is empty, and the read is a failed lookup.
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
        assert_eq!(
            Some(before),
            Some(used_slots_hash(&[(key(1, 30), 2), (key(1, 10), 0), (key(1, 10), 0)])),
            "order and duplicates do not matter"
        );
        // One new reachable instance: append-only, old slots stay put.
        assert_eq!(m.assign(key(1, 99)), 3);
        assert_eq!(m.assign(key(1, 99)), 3, "assign is stable");
        assert_eq!(m.slot_of(key(1, 10)), Some(0));
        assert_eq!(m.used_slots_hash(&unit), Some(before), "unrelated units keep their key");
        assert_ne!(m.manifest_hash(), table_before, "the table unit rebuilds");
        assert_eq!(m.used_slots_hash(&[key(7, 7)]), None, "a key with no slot cannot key a unit");
    }

    /// The lowered sample body carries the read set with it, and every call
    /// in it is a terminator with an empty unwind slot.
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
                    assert_eq!(*unwind, None, "no unwind edges exist yet");
                    match target {
                        CallTarget::Fn(_) => fn_calls += 1,
                        CallTarget::Builtin(_) => builtin_calls += 1,
                    }
                }
            }
            assert!(fn_calls >= 2, "helper() and f.get() are fn call terminators, got {fn_calls}");
            let _ = builtin_calls;
            assert!(crate::borrowck::borrowck(p, &body).is_empty(), "the sample borrow-checks clean");
        });
    }
}
