// The import worklist, module binding tables, visibility, and path
// resolution (docs/ARCH.md sections 1.3 and 1.5).
//
// State per module: for each namespace, a map `name -> BindState`. A
// binding's source sets priority: local def and explicit import beat glob
// at all times, even when the glob binding arrives first. Two globs that
// bring different defs under one name store `Ambiguous`, which is an
// error only when code uses the name. A re-export binding carries the
// `use` item's own visibility; the target def does not change, and there
// is no alias def. Visibility is checked per path segment against the
// binding found in that module, never as a minimum over the chain.
//
// Determinism: work items process in ModuleId order, names in name-string
// order. Each binding changes state at most twice (absent, glob,
// explicit), so the fixpoint ends; a round cap of `modules + 2` full
// sweeps guards against bugs (a hit is an internal error today).
use crate::ast;
use crate::def::DefId;
use crate::diag::{Diag, Span};
use crate::driver::graph::{BindingRes, Namespace};
use crate::intern::{FxMap, Interner, Sym};
use crate::ty::defs::ModuleId;
use std::collections::BTreeMap;

/// The namespace index of a binding table (type, value, macro).
pub fn ns_index(ns: Namespace) -> usize {
    match ns {
        Namespace::Type => 0,
        Namespace::Value => 1,
        Namespace::Macro => 2,
    }
}

/// Visibility in resolver form. `In` holds the written path segments of a
/// `pub(in ...)` after the `in` keyword, resolved against module paths by
/// name when checked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VisKind {
    Priv,
    Pub,
    Crate,
    Super,
    In(Vec<Sym>),
}

/// Converts written AST visibility to resolver form.
pub fn vis_from_ast(v: &ast::Vis, interner: &Interner) -> VisKind {
    match v {
        ast::Vis::Private => VisKind::Priv,
        ast::Vis::Public => VisKind::Pub,
        ast::Vis::Restricted { path, .. } => {
            let names: Vec<&str> = path.iter().map(|s| interner.get(s.name)).collect();
            match names.as_slice() {
                ["crate"] => VisKind::Crate,
                ["super"] => VisKind::Super,
                ["self"] => VisKind::Priv,
                _ => VisKind::In(path.iter().map(|s| s.name).collect()),
            }
        }
    }
}

/// What a binding resolves to. An extern crate root is a target of its
/// own: items behind it belong to another crate's resolver (or to the
/// std compat layer for `std`/`core`/`alloc`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    Def(DefId),
    Module(ModuleId),
    Extern(u32),
    /// An enum variant (`use a::E::V`, `use a::E::*`): the Adt def plus
    /// the variant name. Variants are not defs of their own here.
    Variant(DefId, Sym),
}

/// One binding: where it points, the visibility it carries (the item's
/// own vis for a local def, the `use` item's vis for an import), its
/// source rank (0 empty, 1 glob, 2 local or explicit), and the module
/// whose scope defines privacy for it.
#[derive(Clone, Debug)]
pub struct Bind {
    pub target: Target,
    pub vis: VisKind,
    pub rank: u8,
    pub def_module: ModuleId,
}

/// One name in one namespace of one module.
#[derive(Clone, Debug)]
pub enum BindState {
    One(Bind),
    Ambiguous,
}

/// What kind of local item a def names, for path rewriting.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResKind {
    Fn,
    Adt,
    Const,
    Static,
    Alias,
    Macro,
    Trait,
}

/// Facts the rewrite pass needs about one local def, by DefId.
#[derive(Clone, Debug)]
pub struct DefInfo {
    pub kind: ResKind,
    /// The flat name the def carries in the merged AST (the plain name in
    /// the root module, a module-mangled unique name elsewhere).
    pub flat: Sym,
    pub module: ModuleId,
    pub vis: VisKind,
}

/// One module of a crate's module tree. One `ResolvedTables` holds the
/// trees of every crate in the workspace session (ARCH 1.8): each crate
/// is a detached subtree whose root has no parent, and `path` is the
/// name path inside that crate.
#[derive(Clone, Debug)]
pub struct ModuleInfo {
    pub parent: Option<ModuleId>,
    /// The module's own name (the crate name for a crate root).
    pub name: Sym,
    /// Names from the crate root to this module (empty for a root).
    pub path: Vec<Sym>,
    pub vis: VisKind,
    pub span: Span,
    /// `#[no_implicit_prelude]` applies (inherited from the parent too).
    pub no_prelude: bool,
    /// The crate root module of the crate this module belongs to.
    pub krate_root: ModuleId,
    /// True when the `mod` declaration carried `#[macro_use]`.
    pub macro_use: bool,
}

/// One extern crate in one crate's extern prelude. The prelude is per
/// crate: two crates in one session can name different dependency
/// crates with the same extern name, so every entry carries its owner.
#[derive(Clone, Debug)]
pub struct ExternInfo {
    /// The name paths use (`std`, `core`, a renamed dependency).
    pub name: String,
    pub def: DefId,
    /// True for `std`, `core`, and `alloc`: paths rooted there keep the
    /// std compat handling in collect and check.
    pub is_std_lib: bool,
    /// The crate root module this entry belongs to (the dependent crate).
    pub owner: ModuleId,
    /// For a dependency lust compiles from source in this session: the
    /// dependency crate's root module in these tables. Paths then walk
    /// its real bindings with normal visibility. None for std libs and
    /// for unsupported dependencies.
    pub root_module: Option<ModuleId>,
    /// For a dependency with no lust source, adapter, or shim crate
    /// yet: the reason (it names the crate), reported as L0508 where
    /// the dependency is used. None when the crate is usable.
    pub unsupported: Option<String>,
}

/// The resolved binding tables of one crate: the swap-in implementation
/// behind the S7 `Binding` query fns (driver/graph.rs). The driver
/// attaches one to `Program` after collect; checkers keep calling the
/// same fns and now get module answers.
pub struct ResolvedTables {
    pub modules: Vec<ModuleInfo>,
    pub maps: Vec<[FxMap<Sym, BindState>; 3]>,
    pub externs: Vec<ExternInfo>,
    /// Adt def -> associated fn name -> (vis, defining module).
    pub assoc_vis: FxMap<DefId, FxMap<Sym, (VisKind, ModuleId)>>,
    /// Adt def -> (field name -> vis) plus the defining module, for the
    /// field-access visibility check in check.
    pub field_vis: FxMap<DefId, (ModuleId, FxMap<Sym, VisKind>)>,
    /// Tuple-struct def -> per-field vis in declaration order plus the
    /// defining module, for tuple field and constructor checks in check.
    pub tuple_field_vis: FxMap<DefId, (ModuleId, Vec<VisKind>)>,
    /// Adt def -> variant names, for variant imports and `use E::*`.
    pub variants: FxMap<DefId, Vec<Sym>>,
    pub def_info: FxMap<DefId, DefInfo>,
    /// The defining module of each const, static, and associated
    /// const item, keyed by the item's span. The const evaluator in
    /// collect reads it to check field privacy in initializers:
    /// a span survives flattening and Ast concatenation, and items
    /// with no def of their own (anonymous consts, associated
    /// consts) still have one. Filled in `register_items`.
    pub const_init_module: FxMap<Span, ModuleId>,
    /// Flat name -> the source path text for diagnostics (`m0::Stats`,
    /// or `base::inner::Deep` for a source dependency, whose flat name
    /// carries only a hash of the crate). Filled where defs are renamed
    /// to flat names in the worklist. Display only; never a lookup key.
    pub display_names: FxMap<Sym, Sym>,
    /// Each module's own def (index by ModuleId), filled at registration.
    pub module_defs: Vec<DefId>,
    /// Flat name -> def, per namespace, for the merged AST's names. The
    /// checker resolves the rewritten flat names in the root module, so a
    /// root query for a flat name answers here.
    pub flat: [FxMap<Sym, DefId>; 3],
    /// The defining module of each flattened fn, in LocalDefId order.
    pub fn_module: Vec<ModuleId>,
    /// Crate roots by their `$crate` magic segment name. A macro defined
    /// in one crate and expanded in another has its `$crate` rewritten
    /// to a magic first segment (`$lust$crate$<hex>`, not a legal Rust
    /// identifier, so source text can never write it) that resolves to
    /// the defining crate's root even when it is not a direct dependency
    /// of the expanding crate.
    pub crate_magic: FxMap<Sym, ModuleId>,
    /// `use std::... [as Name]` bindings: (module, namespace index,
    /// bound name) -> the import's visibility and the canonical
    /// std path the name stands for. Std items have no local def
    /// to bind, so the rewrite pass expands the name back to the
    /// written path check reads. Ordered by module, so a glob import
    /// reads the aliases of its source module as one range.
    pub std_aliases: BTreeMap<(ModuleId, u8, Sym), (VisKind, Vec<Sym>)>,
    /// The `std_aliases` keys a glob import brought (rank 1), with the
    /// module whose scope defines privacy for each (`Bind::def_module`;
    /// an explicit alias uses its own module). A local item or explicit
    /// import of the name replaces one; a glob binding of another item
    /// makes the name ambiguous (`insert_glob_std_alias`).
    pub std_glob_aliases: FxMap<(ModuleId, u8, Sym), ModuleId>,
    /// The source module a glob-bound name was copied from, keyed like
    /// `std_glob_aliases`. A glob copies the source module's current
    /// binding, and that binding can still upgrade (a glob binding in
    /// the source is replaced by its explicit import, which may name
    /// a different item): a later copy from the same source then
    /// replaces this binding instead of making the name ambiguous, as
    /// rustc resolves the name through the source's final binding.
    /// Fixpoint state only; the final answer stays in `maps`.
    pub glob_src: FxMap<(ModuleId, u8, Sym), ModuleId>,
    /// Macros a module already re-exported with the self `use` idiom
    /// (`macro_rules! m` then `pub(crate) use m;` in one module):
    /// rustc allows that one `use` even though the macro definition
    /// binds the name in the same module, and rejects a second one.
    pub macro_self_uses: FxMap<(ModuleId, Sym), ()>,
    /// The adapter crates of the session (ARCH 3.6) and the files each
    /// one read. Check reads it for intrinsic privilege and to keep
    /// layout queries off adapter types whose layout is not exact.
    pub adapters: Vec<AdapterCrate>,
    /// Glob `use`s of std modules (`use std::cell::*;`), which bind
    /// nothing in `maps`: (module, path). They answer whether a
    /// non-prelude std type lust knows by name
    /// (`ty::lang::STD_IMPORTED_TYPES`) is in scope by glob; an
    /// explicit import of one is a `std_aliases` entry instead.
    pub std_globs: Vec<(ModuleId, Vec<Sym>)>,
    /// The shipped std platform crate of the session (W-SHIM; see
    /// `std_platform_path`): its root module and its `$crate` magic
    /// name. None when no file of the session mentions a platform
    /// module, so the crate was not loaded.
    pub std_platform: Option<(ModuleId, Sym)>,
    /// The hidden std source modules the std splice defined in the
    /// selected crate's root (src/stdmods.rs, W-STD-C): their names and
    /// module ids. They are bound nowhere; `std_module_at` walks the
    /// std paths of their rows into them.
    pub std_modules: Vec<(Sym, ModuleId)>,
    /// Where the std splice starts in the selected crate's root file
    /// (`CrateInput::std_splice_lo`): every byte from here on in file 0
    /// is shipped std source.
    pub std_splice_lo: Option<u32>,
    /// The driver's std splice ranges with their shipped crates, set
    /// before collect (`Program::shipped_crate_at` reads them while
    /// `Program::shipped_ranges` is still empty).
    pub std_ranges: Vec<(u32, u32, crate::ty::lang::ShippedCrate)>,
}

/// The std modules whose items can come from the shipped platform
/// crate (`library/std/src/platform.rs`, W-SHIM): a written
/// `std::<module>::<item>` path resolves into that crate when the
/// crate defines the item. Other std paths keep the std compat
/// handling of collect and check.
pub const STD_PLATFORM_MODULES: &[&str] = &["io", "fs", "env", "path", "process", "ffi", "os"];

/// The platform modules the compiler has no std handling for at all:
/// every `std::<module>::<name>` path resolves in the platform crate,
/// so a name it lacks is an unresolved path, as in rustc, instead of
/// an unchecked std alias.
const STD_PLATFORM_FULL: &[&str] = &["io", "fs", "path", "ffi"];

/// One adapter crate in a session (see `resolve::adapters`).
#[derive(Clone, Debug)]
pub struct AdapterCrate {
    /// The crate name as paths write it (`rustc_hash`).
    pub name: String,
    pub files: Vec<crate::diag::FileId>,
    /// Source paths of the types whose layout equals upstream's.
    pub exact_layout: Vec<String>,
}

impl ResolvedTables {
    /// True when a glob of its std module imports the std type `name`
    /// into `module` (W-STD-A).
    pub fn std_glob_imports(&self, module: ModuleId, name: &str, interner: &Interner) -> bool {
        self.std_globs.iter().any(|(m, path)| {
            *m == module && {
                let p: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
                crate::ty::lang::std_glob_imports(&p, name)
            }
        })
    }

    /// The std module path of a module-level glob in `module` that
    /// imports `name` from a sync or thread module (W-THREADS): a type
    /// (`AtomicUsize`, `atomic::Ordering`) or a free fn (`fence`). The
    /// resolver rewrites the bare name to that full std path, as it does
    /// for a fn-body glob, so check never reads it by its bare name.
    pub fn std_sync_glob_path(&self, module: ModuleId, name: &str, interner: &Interner) -> Option<Vec<Sym>> {
        self.std_globs.iter().find_map(|(m, path)| {
            let p: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
            (*m == module && crate::ty::lang::std_sync_glob_imports(&p, name)).then(|| path.clone())
        })
    }

    /// True when `module` has a glob import of a std module or enum
    /// (`std_mod_only`: of a module, not an enum's variants). Lust does
    /// not know every name such a glob brings (`Rewrite::std_glob_check`).
    pub fn has_std_glob(&self, module: ModuleId, std_mod_only: bool, interner: &Interner) -> bool {
        self.std_globs.iter().any(|(m, path)| {
            *m == module && (!std_mod_only || {
                let p: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
                crate::ty::lang::std_enum_variants(&p).is_empty()
            })
        })
    }

    /// An empty table set with only the first crate's root module (id
    /// 0, the selected crate; dependency crates join with
    /// `add_crate_root`).
    pub fn new(crate_name: Sym) -> ResolvedTables {
        ResolvedTables {
            modules: vec![ModuleInfo {
                parent: None,
                name: crate_name,
                path: Vec::new(),
                vis: VisKind::Pub,
                span: Span::default(),
                no_prelude: false,
                krate_root: ModuleId(0),
                macro_use: false,
            }],
            maps: vec![Default::default()],
            externs: Vec::new(),
            assoc_vis: FxMap::default(),
            field_vis: FxMap::default(),
            tuple_field_vis: FxMap::default(),
            variants: FxMap::default(),
            def_info: FxMap::default(),
            const_init_module: FxMap::default(),
            display_names: FxMap::default(),
            module_defs: vec![DefId::PLACEHOLDER],
            flat: Default::default(),
            fn_module: Vec::new(),
            crate_magic: FxMap::default(),
            std_aliases: BTreeMap::new(),
            std_glob_aliases: FxMap::default(),
            glob_src: FxMap::default(),
            macro_self_uses: FxMap::default(),
            adapters: Vec::new(),
            std_globs: Vec::new(),
            std_platform: None,
            std_modules: Vec::new(),
            std_splice_lo: None,
            std_ranges: Vec::new(),
        }
    }

    /// Adds a detached crate root module for one more crate in the
    /// workspace session and returns its id.
    pub fn add_crate_root(&mut self, name: Sym) -> ModuleId {
        let id = ModuleId(self.modules.len() as u32);
        self.modules.push(ModuleInfo {
            parent: None,
            name,
            path: Vec::new(),
            vis: VisKind::Pub,
            span: Span::default(),
            no_prelude: false,
            krate_root: id,
            macro_use: false,
        });
        self.maps.push(Default::default());
        self.module_defs.push(DefId::PLACEHOLDER);
        id
    }

    /// The crate root module of the crate `m` belongs to.
    pub fn root_of(&self, m: ModuleId) -> ModuleId {
        self.modules[m.0 as usize].krate_root
    }

    /// True when `rest` (the segments after `std`) resolves in the
    /// shipped std platform crate: a platform module
    /// (`STD_PLATFORM_MODULES`) and at least one more segment. In a
    /// `STD_PLATFORM_FULL` module every such path does; in the others
    /// only an item the crate defines and `from` can see (modules, then
    /// a last item in any namespace), so items the platform crate lacks
    /// keep the std compat handling. A path that ends at the module
    /// (`std::env`) never redirects: module imports keep their std alias.
    pub fn std_platform_has(&self, rest: &[Sym], from: ModuleId, interner: &Interner) -> bool {
        let Some((root, _)) = self.std_platform else { return false };
        if rest.len() < 2 || !STD_PLATFORM_MODULES.contains(&interner.get(rest[0])) {
            return false;
        }
        if STD_PLATFORM_FULL.contains(&interner.get(rest[0])) {
            return true;
        }
        let mut m = root;
        for (k, &seg) in rest.iter().enumerate() {
            if k + 1 == rest.len() {
                return [Namespace::Type, Namespace::Value, Namespace::Macro]
                    .into_iter()
                    .any(|ns| matches!(self.segment_in(m, seg, ns, from, interner), PathRes::Done(_)));
            }
            match self.segment_in(m, seg, Namespace::Type, from, interner) {
                PathRes::Done(Target::Module(next)) => m = next,
                // An Adt with an associated item after it (`std::io::Error::other`).
                PathRes::Done(Target::Def(_)) => return k > 0,
                _ => return false,
            }
        }
        false
    }

    /// The written path of a `std::<platform module>::...` import or
    /// path with `std` replaced by the platform crate's magic root
    /// segment, when `std_platform_has` holds for it. `path[0]` must
    /// already be known to name the std extern.
    pub fn std_platform_path(&self, path: &[Sym], from: ModuleId, interner: &Interner) -> Option<Vec<Sym>> {
        let (_, magic) = self.std_platform?;
        if path.first().is_none_or(|s| interner.get(*s) != "std") || !self.std_platform_has(&path[1..], from, interner) {
            return None;
        }
        let mut out = path.to_vec();
        out[0] = magic;
        Some(out)
    }

    /// True when the first segment `std` of a path written in `from`
    /// names the std extern (no local item or import shadows it).
    fn std_is_extern(&self, from: ModuleId, interner: &Interner) -> bool {
        let std_sym = interner.intern("std");
        let i = match self.first_segment(from, std_sym, Namespace::Type, PathMode::Use, interner) {
            PathRes::Done(Target::Extern(i)) => i,
            _ => return false,
        };
        let e = &self.externs[i as usize];
        e.is_std_lib && e.name == "std"
    }

    /// Adds a module under a parent and returns its id.
    pub fn add_module(&mut self, parent: ModuleId, name: Sym, vis: VisKind, span: Span) -> ModuleId {
        let mut path = self.modules[parent.0 as usize].path.clone();
        path.push(name);
        let no_prelude = self.modules[parent.0 as usize].no_prelude;
        let krate_root = self.modules[parent.0 as usize].krate_root;
        let id = ModuleId(self.modules.len() as u32);
        self.modules.push(ModuleInfo { parent: Some(parent), name, path, vis, span, no_prelude, krate_root, macro_use: false });
        self.maps.push(Default::default());
        self.module_defs.push(DefId::PLACEHOLDER);
        id
    }

    /// The module at a name path from a crate root, if it exists.
    pub fn module_by_path_in(&self, root: ModuleId, path: &[Sym]) -> Option<ModuleId> {
        self.modules.iter().position(|m| m.krate_root == root && m.path == path).map(|i| ModuleId(i as u32))
    }

    /// The module at a name path from the first crate's root, if it
    /// exists. Kept for single-crate callers.
    pub fn module_by_path(&self, path: &[Sym]) -> Option<ModuleId> {
        self.module_by_path_in(ModuleId(0), path)
    }

    /// True when `m` is `anc` or a descendant of it.
    pub fn is_within(&self, m: ModuleId, anc: ModuleId) -> bool {
        let mut cur = Some(m);
        while let Some(c) = cur {
            if c == anc {
                return true;
            }
            cur = self.modules[c.0 as usize].parent;
        }
        false
    }

    /// The visibility rule of section 1.5: can code in module `from` use
    /// a binding with visibility `vis` defined in `def_module`? Spliced
    /// std source (`STD_MODULE`, no module of these tables) sees all: it
    /// reaches a user item only through generics, as `Option::map(Self)`
    /// calls a user tuple struct constructor, and privacy was checked
    /// where user code named the item.
    pub fn visible(&self, vis: &VisKind, def_module: ModuleId, from: ModuleId, interner: &Interner) -> bool {
        if from == crate::ty::defs::STD_MODULE {
            return true;
        }
        match vis {
            VisKind::Pub => true,
            VisKind::Crate => self.root_of(from) == self.root_of(def_module),
            VisKind::Priv => self.is_within(from, def_module),
            VisKind::Super => match self.modules[def_module.0 as usize].parent {
                Some(p) => self.is_within(from, p),
                None => true, // pub(super) at the root behaves as pub(crate)-ish in rustc (it warns); the root has no parent.
            },
            VisKind::In(path) => match self.resolve_in_path(path, def_module, interner) {
                Some(m) => self.is_within(from, m),
                None => false,
            },
        }
    }

    /// True when a written restricted visibility at `module` is one rustc
    /// accepts: `pub(super)` needs a parent module (E0433 at a crate
    /// root), and `pub(in path)` must start with `crate`, `self`, or
    /// `super` and name `module` or one of its ancestors (E0742).
    pub fn restriction_ok(&self, vis: &VisKind, module: ModuleId, interner: &Interner) -> bool {
        match vis {
            VisKind::Super => self.modules[module.0 as usize].parent.is_some(),
            // `pub(in $crate::..)` from another crate's macro starts with a
            // magic segment that `resolve_in_path` does not place; it is
            // not checked here.
            VisKind::In(path) if path.first().is_some_and(|s| self.crate_magic.contains_key(s)) => true,
            VisKind::In(path) => {
                matches!(path.first().map(|s| interner.get(*s)), Some("crate" | "self" | "super"))
                    && self.resolve_in_path(path, module, interner).is_some_and(|m| self.is_within(module, m))
            }
            VisKind::Priv | VisKind::Pub | VisKind::Crate => true,
        }
    }

    /// The set of modules a visibility reaches, as a region for the
    /// re-export subset check: everywhere (pub), the whole crate, or one
    /// module subtree.
    fn vis_region(&self, vis: &VisKind, def_module: ModuleId, interner: &Interner) -> (u8, Option<ModuleId>) {
        match vis {
            VisKind::Pub => (2, None),
            VisKind::Crate => (1, None),
            VisKind::Priv => (0, Some(def_module)),
            VisKind::Super => match self.modules[def_module.0 as usize].parent {
                Some(p) => (0, Some(p)),
                None => (1, None),
            },
            VisKind::In(path) => match self.resolve_in_path(path, def_module, interner) {
                Some(m) => (0, Some(m)),
                None => (0, Some(def_module)),
            },
        }
    }

    /// True when the region of `vis` (at `def_module`) is inside the
    /// region of `outer` (at `outer_module`).
    fn vis_within(&self, vis: &VisKind, def_module: ModuleId, outer: &VisKind, outer_module: ModuleId, interner: &Interner) -> bool {
        let (ra, ma) = self.vis_region(vis, def_module, interner);
        let (rb, mb) = self.vis_region(outer, outer_module, interner);
        if rb == 2 {
            return true;
        }
        if ra == 2 {
            return false;
        }
        if rb == 1 {
            return true;
        }
        if ra == 1 {
            return false;
        }
        match (ma, mb) {
            (Some(a), Some(b)) => self.is_within(a, b),
            _ => true,
        }
    }

    /// The re-export rule (rustc E0364): a non-private `use` of an item
    /// whose own visibility reaches less than the `use` would is an
    /// error. Reports and returns false when the import may not bind.
    fn check_reexport(&self, imp: &Import, target: Target, name: &str, interner: &Interner, diags: &mut Vec<Diag>) -> bool {
        if imp.vis == VisKind::Priv {
            return true;
        }
        let (item_vis, item_module) = match target {
            Target::Def(d) | Target::Variant(d, _) => match self.def_info.get(&d) {
                // Macros are textual: `#[macro_export]` puts them at the
                // crate root in public, so re-export rules do not bind
                // there. A macro without it is public only within its
                // crate: a `pub use` of it is rustc E0364 ("only public
                // within the crate"), while `pub(crate) use` is the
                // re-export idiom. An exported macro has a public
                // binding at its crate root.
                Some(info) if info.kind == ResKind::Macro => {
                    if imp.vis != VisKind::Pub {
                        return true;
                    }
                    let root = self.root_of(info.module);
                    let sym = interner.intern(name);
                    let exported = matches!(self.lookup(root, Namespace::Macro, sym),
                        Some(BindState::One(b)) if b.target == target && b.vis == VisKind::Pub);
                    if exported {
                        return true;
                    }
                    diags.push(reexport_diag(name, imp.span));
                    return false;
                }
                Some(info) => (info.vis.clone(), info.module),
                None => return true,
            },
            Target::Module(m) => {
                let info = &self.modules[m.0 as usize];
                (info.vis.clone(), info.parent.unwrap_or(crate::ty::defs::ROOT_MODULE))
            }
            Target::Extern(_) => return true,
        };
        if self.vis_within(&imp.vis, imp.module, &item_vis, item_module, interner) {
            return true;
        }
        diags.push(reexport_diag(name, imp.span));
        false
    }

    /// The visibility a glob import gives one name, as rustc does: the
    /// `use` visibility when the source binding reaches at least as far,
    /// else the source binding's own narrower visibility at its own
    /// module. So `pub use inner::*` of a `pub(super)` item binds it as
    /// that `pub(super)`, not as `pub`.
    fn glob_vis(&self, imp: &Import, vis: &VisKind, def_module: ModuleId, interner: &Interner) -> (VisKind, ModuleId) {
        if self.vis_within(&imp.vis, imp.module, vis, def_module, interner) {
            (imp.vis.clone(), imp.module)
        } else {
            (vis.clone(), def_module)
        }
    }

    /// Resolves a `pub(in path)` path, written relative to the defining
    /// module. The segments are module names (with `crate`, `self`, and
    /// `super` allowed in front), matched by name against module paths.
    fn resolve_in_path(&self, path: &[Sym], def_module: ModuleId, interner: &Interner) -> Option<ModuleId> {
        let crate_sym = interner.intern("crate");
        let self_sym = interner.intern("self");
        let super_sym = interner.intern("super");
        let (mut base_path, rest): (Vec<Sym>, &[Sym]) = match path.first() {
            Some(&s) if s == crate_sym => (Vec::new(), &path[1..]),
            Some(&s) if s == self_sym => (self.modules[def_module.0 as usize].path.clone(), &path[1..]),
            Some(&s) if s == super_sym => {
                let mut p = self.modules[def_module.0 as usize].path.clone();
                let mut rest = path;
                while rest.first() == Some(&super_sym) {
                    p.pop()?;
                    rest = &rest[1..];
                }
                (p, rest)
            }
            // A plain path in `pub(in ...)` is read from the crate root's
            // perspective when it names a root descendant chain; Rust
            // reads it relative to the current module, and the written
            // forms in practice start with `crate`/`self`/`super`. Treat
            // a bare path as relative to the defining module.
            _ => (self.modules[def_module.0 as usize].path.clone(), path),
        };
        base_path.extend_from_slice(rest);
        self.module_by_path_in(self.root_of(def_module), &base_path)
    }

    /// Inserts a binding, applying the priority rules. Returns `Changed`
    /// when the table now answers differently, `Dup` when two same-rank
    /// explicit sources name different targets (a user error the caller
    /// reports after the fixpoint).
    pub fn insert(&mut self, module: ModuleId, ns: Namespace, name: Sym, bind: Bind) -> InsertOut {
        // A glob std alias of the name loses to a local item or explicit
        // import, and is ambiguous with a glob binding of a crate item.
        let key = (module, ns_index(ns) as u8, name);
        if !self.std_glob_aliases.is_empty() && self.std_glob_aliases.remove(&key).is_some() {
            self.std_aliases.remove(&key);
            if bind.rank <= 1 {
                self.maps[module.0 as usize][ns_index(ns)].insert(name, BindState::Ambiguous);
                return InsertOut::Changed;
            }
        }
        let map = &mut self.maps[module.0 as usize][ns_index(ns)];
        match map.get(&name) {
            None => {
                map.insert(name, BindState::One(bind));
                InsertOut::Changed
            }
            Some(BindState::One(old)) => {
                if old.target == bind.target {
                    // The same target bound twice at explicit rank is still
                    // two definitions of one name (rustc E0252/E0255): a
                    // repeated `use`, or a `use` of an item this module
                    // defines. A glob (rank 1) re-binding the same target
                    // is legal and stays `Same`. An explicit import of the
                    // item a glob already brought is legal too, and it
                    // raises the binding to explicit rank: other globs
                    // can then no longer make the name ambiguous here.
                    if old.rank == 2 && bind.rank == 2 {
                        InsertOut::Dup
                    } else if bind.rank > old.rank {
                        map.insert(name, BindState::One(bind));
                        InsertOut::Changed
                    } else {
                        InsertOut::Same
                    }
                } else if bind.rank > old.rank {
                    map.insert(name, BindState::One(bind));
                    InsertOut::Changed
                } else if bind.rank < old.rank {
                    InsertOut::Same
                } else if bind.rank <= 1 {
                    map.insert(name, BindState::Ambiguous);
                    InsertOut::Changed
                } else {
                    InsertOut::Dup
                }
            }
            Some(BindState::Ambiguous) => {
                if bind.rank >= 2 {
                    map.insert(name, BindState::One(bind));
                    InsertOut::Changed
                } else {
                    InsertOut::Same
                }
            }
        }
    }

    /// Inserts one glob copy from source module `src` (see `glob_src`).
    /// A binding this same source put here earlier, with a different
    /// target, follows the source's upgrade: it is replaced, not made
    /// ambiguous. A copy from any other source keeps the plain rules.
    pub fn insert_glob(&mut self, module: ModuleId, ns: Namespace, name: Sym, bind: Bind, src: ModuleId) -> InsertOut {
        let key = (module, ns_index(ns) as u8, name);
        let stale = matches!(self.lookup(module, ns, name), Some(BindState::One(old)) if old.rank <= 1 && old.target != bind.target)
            && self.glob_src.get(&key) == Some(&src)
            && !self.std_glob_aliases.contains_key(&key);
        // The mirror case: this source made the name ambiguous here
        // (its own binding was ambiguous, propagated by the glob copy
        // in `try_import`), and its binding has since settled to one
        // item (its explicit import landed). The copy follows it back
        // to that item; any other live glob that still brings a
        // different item re-makes the ambiguity on a later sweep.
        let settled = matches!(self.lookup(module, ns, name), Some(BindState::Ambiguous))
            && self.glob_src.get(&key) == Some(&src)
            && !self.std_glob_aliases.contains_key(&key);
        if stale || settled {
            self.maps[module.0 as usize][ns_index(ns)].insert(name, BindState::One(bind));
            return InsertOut::Changed;
        }
        let out = self.insert(module, ns, name, bind);
        match self.lookup(module, ns, name) {
            Some(BindState::One(_)) => {
                if out == InsertOut::Changed {
                    self.glob_src.insert(key, src);
                }
            }
            _ => {
                self.glob_src.remove(&key);
            }
        }
        out
    }

    /// One name's binding, without prelude or flat-name fallback. This is
    /// the raw table read; `Program::binding` layers the fallbacks.
    pub fn lookup(&self, module: ModuleId, ns: Namespace, name: Sym) -> Option<&BindState> {
        self.maps.get(module.0 as usize).and_then(|m| m[ns_index(ns)].get(&name))
    }

    /// True when `module` has an explicit std alias (not a glob one)
    /// under this key.
    pub fn explicit_std_alias(&self, key: (ModuleId, u8, Sym)) -> bool {
        self.std_aliases.contains_key(&key) && !self.std_glob_aliases.contains_key(&key)
    }

    /// The module whose scope defines privacy for one std alias.
    pub fn std_alias_def_module(&self, key: (ModuleId, u8, Sym)) -> ModuleId {
        self.std_glob_aliases.get(&key).copied().unwrap_or(key.0)
    }

    /// The std aliases of one module that code in `from` can see, as
    /// (namespace index, name, vis, defining module, path). A glob of
    /// `module` imports these as it imports the module's bindings.
    pub fn visible_std_aliases(&self, module: ModuleId, from: ModuleId, interner: &Interner) -> Vec<(u8, Sym, VisKind, ModuleId, Vec<Sym>)> {
        self.std_aliases
            .range((module, 0, Sym(0))..=(module, u8::MAX, Sym(u32::MAX)))
            .filter_map(|(&key, (vis, path))| {
                let def_module = self.std_alias_def_module(key);
                self.visible(vis, def_module, from, interner).then(|| (key.1, key.2, vis.clone(), def_module, path.clone()))
            })
            .collect()
    }

    /// Binds a std alias at glob rank (`use prelude::*;` of a module
    /// with `pub use std::rc::Rc;`). A local item, an explicit import,
    /// or an explicit std alias of the name wins. A glob binding of a
    /// crate item, or a glob alias of another std item, makes the name
    /// ambiguous (rustc E0659 when used). Returns true on a change.
    pub fn insert_glob_std_alias(&mut self, module: ModuleId, ns: Namespace, name: Sym, vis: VisKind, def_module: ModuleId, path: Vec<Sym>) -> bool {
        let key = (module, ns_index(ns) as u8, name);
        match self.lookup(module, ns, name) {
            Some(BindState::One(b)) if b.rank >= 2 => return false,
            Some(BindState::Ambiguous) => return false,
            Some(BindState::One(_)) => {
                self.maps[module.0 as usize][ns_index(ns)].insert(name, BindState::Ambiguous);
                return true;
            }
            None => {}
        }
        match self.std_aliases.get(&key) {
            None => {
                self.std_aliases.insert(key, (vis, path));
                self.std_glob_aliases.insert(key, def_module);
                true
            }
            Some(_) if !self.std_glob_aliases.contains_key(&key) => false,
            Some((_, old)) if same_std_item(old, &path) => false,
            Some(_) => {
                self.std_aliases.remove(&key);
                self.std_glob_aliases.remove(&key);
                self.maps[module.0 as usize][ns_index(ns)].insert(name, BindState::Ambiguous);
                true
            }
        }
    }

    /// True when some module defines `name` locally (not by import), in
    /// any namespace. The rewrite pass uses it for the lexical-scope
    /// rule: a bare name that only an enclosing or sibling module
    /// defines must error, never fall through to the flat tables.
    pub fn any_local_named(&self, name: Sym) -> bool {
        self.maps.iter().enumerate().any(|(mi, maps)| {
            maps.iter().any(|m| matches!(m.get(&name), Some(BindState::One(b)) if b.rank == 2 && b.def_module.0 as usize == mi))
        })
    }

    /// Every name some module defines locally, as a set (see
    /// `any_local_named`). The rewrite pass builds this once over the
    /// frozen tables instead of rescanning every module map per
    /// unresolved path, which was quadratic in the module count.
    /// The value is a bit set of the namespaces (by `ns_index`) some
    /// module defines the name in.
    pub fn local_named_set(&self) -> FxMap<Sym, u8> {
        let mut out: FxMap<Sym, u8> = FxMap::default();
        for (mi, maps) in self.maps.iter().enumerate() {
            for (ns, m) in maps.iter().enumerate() {
                for (name, state) in m {
                    if matches!(state, BindState::One(b) if b.rank == 2 && b.def_module.0 as usize == mi) {
                        *out.entry(*name).or_default() |= 1 << ns;
                    }
                }
            }
        }
        out
    }

    /// A fingerprint of every fact the path rewrite pass can read:
    /// modules, bindings, def info, associated and field visibility,
    /// variants, flat names, module defs, and the extern prelude.
    /// Spans never hash (a line shift in one file must not move the
    /// epoch of the others). The worklist keys its per-file
    /// rewritten-Ast cache on this value: when it stands, a file
    /// whose text stands rewrites to the same Ast. Accumulation is
    /// order-independent per entry (map iteration order is not a
    /// fact), with entry counts folded in.
    pub fn rewrite_epoch(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        fn vis(h: &mut crate::intern::FxHasher, v: &VisKind) {
            match v {
                VisKind::Priv => h.write_u64(1),
                VisKind::Pub => h.write_u64(2),
                VisKind::Crate => h.write_u64(3),
                VisKind::Super => h.write_u64(4),
                VisKind::In(path) => {
                    h.write_u64(5);
                    for s in path {
                        h.write_u64(s.0 as u64);
                    }
                }
            }
        }
        fn target(h: &mut crate::intern::FxHasher, t: &Target) {
            match t {
                Target::Def(d) => {
                    h.write_u64(1);
                    h.write_u64(d.hash.0);
                    h.write_u64(d.krate.0 as u64);
                }
                Target::Module(m) => {
                    h.write_u64(2);
                    h.write_u64(m.0 as u64);
                }
                Target::Extern(i) => {
                    h.write_u64(3);
                    h.write_u64(*i as u64);
                }
                Target::Variant(d, s) => {
                    h.write_u64(4);
                    h.write_u64(d.hash.0);
                    h.write_u64(d.krate.0 as u64);
                    h.write_u64(s.0 as u64);
                }
            }
        }
        let mut acc: u64 = 0x51_7c_c1_b7_27_22_0a_95;
        let mut n: u64 = 0;
        macro_rules! fold {
            ($tag:expr, $body:expr) => {{
                let mut h = crate::intern::FxHasher::default();
                h.write_u64($tag);
                $body(&mut h);
                acc = acc.wrapping_add(h.finish().wrapping_mul(0x9e_37_79_b9_7f_4a_7c_15));
                n += 1;
            }};
        }
        for (i, m) in self.modules.iter().enumerate() {
            fold!(0x10, |h: &mut crate::intern::FxHasher| {
                h.write_u64(i as u64);
                h.write_u64(m.parent.map_or(u64::MAX, |p| p.0 as u64));
                h.write_u64(m.name.0 as u64);
                h.write_u64(m.no_prelude as u64);
                for s in &m.path {
                    h.write_u64(s.0 as u64);
                }
                vis(h, &m.vis);
            });
        }
        for (mi, maps) in self.maps.iter().enumerate() {
            for (ns, m) in maps.iter().enumerate() {
                for (name, state) in m {
                    fold!(0x20, |h: &mut crate::intern::FxHasher| {
                        h.write_u64(mi as u64);
                        h.write_u64(ns as u64);
                        h.write_u64(name.0 as u64);
                        match state {
                            BindState::Ambiguous => h.write_u64(0),
                            BindState::One(b) => {
                                h.write_u64(1);
                                target(h, &b.target);
                                vis(h, &b.vis);
                                h.write_u64(b.rank as u64);
                                h.write_u64(b.def_module.0 as u64);
                            }
                        }
                    });
                }
            }
        }
        for (i, e) in self.externs.iter().enumerate() {
            fold!(0x30, |h: &mut crate::intern::FxHasher| {
                h.write_u64(i as u64);
                e.name.hash(h);
                h.write_u64(e.def.hash.0);
                h.write_u64(e.def.krate.0 as u64);
                h.write_u64(e.is_std_lib as u64);
                h.write_u64(e.owner.0 as u64);
                h.write_u64(e.root_module.map_or(u64::MAX, |m| m.0 as u64));
                e.unsupported.hash(h);
            });
        }
        for (name, m) in &self.std_modules {
            fold!(0x48, |h: &mut crate::intern::FxHasher| {
                h.write_u64(name.0 as u64);
                h.write_u64(m.0 as u64);
                h.write_u64(self.std_splice_lo.map_or(u64::MAX, |lo| lo as u64));
            });
        }
        for (magic, root) in &self.crate_magic {
            fold!(0x46, |h: &mut crate::intern::FxHasher| {
                h.write_u64(magic.0 as u64);
                h.write_u64(root.0 as u64);
            });
        }
        for ((module, ns, name), (v, path)) in &self.std_aliases {
            fold!(0x47, |h: &mut crate::intern::FxHasher| {
                h.write_u64(module.0 as u64);
                h.write_u64(*ns as u64);
                h.write_u64(name.0 as u64);
                vis(h, v);
                for s in path {
                    h.write_u64(s.0 as u64);
                }
            });
        }
        for (module, path) in &self.std_globs {
            fold!(0x48, |h: &mut crate::intern::FxHasher| {
                h.write_u64(module.0 as u64);
                for s in path {
                    h.write_u64(s.0 as u64);
                }
            });
        }
        for (def, m) in &self.assoc_vis {
            for (name, (v, dm)) in m {
                fold!(0x40, |h: &mut crate::intern::FxHasher| {
                    h.write_u64(def.hash.0);
                    h.write_u64(def.krate.0 as u64);
                    h.write_u64(name.0 as u64);
                    h.write_u64(dm.0 as u64);
                    vis(h, v);
                });
            }
        }
        for (def, (dm, m)) in &self.field_vis {
            for (name, v) in m {
                fold!(0x41, |h: &mut crate::intern::FxHasher| {
                    h.write_u64(def.hash.0);
                    h.write_u64(def.krate.0 as u64);
                    h.write_u64(name.0 as u64);
                    h.write_u64(dm.0 as u64);
                    vis(h, v);
                });
            }
        }
        for (def, names) in &self.variants {
            fold!(0x42, |h: &mut crate::intern::FxHasher| {
                h.write_u64(def.hash.0);
                h.write_u64(def.krate.0 as u64);
                for s in names {
                    h.write_u64(s.0 as u64);
                }
            });
        }
        for (def, info) in &self.def_info {
            fold!(0x43, |h: &mut crate::intern::FxHasher| {
                h.write_u64(def.hash.0);
                h.write_u64(def.krate.0 as u64);
                h.write_u64(match info.kind {
                    ResKind::Fn => 1,
                    ResKind::Adt => 2,
                    ResKind::Const => 3,
                    ResKind::Static => 4,
                    ResKind::Alias => 5,
                    ResKind::Macro => 6,
                    ResKind::Trait => 7,
                });
                h.write_u64(info.flat.0 as u64);
                h.write_u64(info.module.0 as u64);
                vis(h, &info.vis);
            });
        }
        for (i, d) in self.module_defs.iter().enumerate() {
            fold!(0x44, |h: &mut crate::intern::FxHasher| {
                h.write_u64(i as u64);
                h.write_u64(d.hash.0);
                h.write_u64(d.krate.0 as u64);
            });
        }
        for (ns, m) in self.flat.iter().enumerate() {
            for (name, def) in m {
                fold!(0x45, |h: &mut crate::intern::FxHasher| {
                    h.write_u64(ns as u64);
                    h.write_u64(name.0 as u64);
                    h.write_u64(def.hash.0);
                    h.write_u64(def.krate.0 as u64);
                });
            }
        }
        let mut h = crate::intern::FxHasher::default();
        h.write_u64(acc);
        h.write_u64(n);
        h.finish()
    }

    /// The answer for the S7 query fns: the module table first, then the
    /// flat-name index (the merged AST's rewritten names, which the
    /// checker asks about in the root module). None means "no answer
    /// here": the caller falls back to builtins and the std prelude.
    pub fn binding(&self, module: ModuleId, ns: Namespace, name: Sym) -> Option<BindingRes> {
        if let Some(state) = self.lookup(module, ns, name) {
            return Some(match state {
                BindState::One(b) => BindingRes::Def(self.target_def(b.target)),
                BindState::Ambiguous => BindingRes::Ambiguous,
            });
        }
        self.flat[ns_index(ns)].get(&name).map(|d| BindingRes::Def(*d))
    }

    /// The DefId a target answers with in a binding query. A module's def
    /// is its module def; an extern's is the extern root def.
    pub fn target_def(&self, target: Target) -> DefId {
        match target {
            Target::Def(d) | Target::Variant(d, _) => d,
            Target::Module(m) => self.module_def(m),
            Target::Extern(i) => self.externs[i as usize].def,
        }
    }

    /// A module's own def, filled by the worklist at registration. The
    /// placeholder answers only before registration runs.
    pub fn module_def(&self, m: ModuleId) -> DefId {
        self.module_defs.get(m.0 as usize).copied().unwrap_or(DefId::PLACEHOLDER)
    }
}

/// The result of one insert, for the fixpoint's change tracking.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum InsertOut {
    Changed,
    Same,
    Dup,
}

// ---------- Path resolution ----------

/// How a path's first segment resolves (section 1.3 scope priority).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PathMode {
    /// Lexical paths in bodies and signatures: the current module only,
    /// then the extern prelude, then the std prelude.
    Lexical,
    /// `use` paths (2018 uniform paths): the current module, then the
    /// extern prelude.
    Use,
}

/// The answer of a path resolution. `rest` is the index of the first
/// segment the resolution did not consume: for an Adt, an associated
/// item or variant follows; for an extern, the rest belongs to that
/// crate. `Private` means the name exists but its binding's visibility
/// does not reach the asking module.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathRes {
    Done(Target),
    Partial(Target, usize),
    Ambiguous,
    Private,
    /// The first segment names a std prelude item. Callers leave the
    /// written path to the std compat handling.
    Prelude,
    Absent,
}

/// Type-namespace names in the std prelude (edition 2024). The list is
/// the classification layer of section 1.3: these names are never module
/// bindings, a glob never carries them, and a local def, explicit
/// import, or glob with the same name wins over them.
pub const STD_PRELUDE_TYPES: &[&str] = &[
    "Option",
    "Result",
    "String",
    "Vec",
    "Box",
    "Copy",
    "Clone",
    "Debug",
    "Default",
    "Eq",
    "PartialEq",
    "PartialOrd",
    "Ord",
    "Hash",
    "Iterator",
    "IntoIterator",
    "From",
    "Into",
    "Send",
    "Sync",
    "Sized",
    "Drop",
    "Fn",
    "FnMut",
    "FnOnce",
    "ToString",
    "ToOwned",
    "AsRef",
    "AsMut",
    "Borrow",
    "BorrowMut",
    "Deref",
    "DerefMut",
    "Unpin",
];

/// Value-namespace names in the std prelude.
pub const STD_PRELUDE_VALUES: &[&str] = &["Some", "None", "Ok", "Err"];

/// True when `name` is a std prelude name in namespace `ns`.
pub fn in_std_prelude(name: &str, ns: Namespace) -> bool {
    match ns {
        Namespace::Type => STD_PRELUDE_TYPES.contains(&name),
        Namespace::Value => STD_PRELUDE_VALUES.contains(&name),
        Namespace::Macro => false,
    }
}

impl ResolvedTables {
    /// The extern prelude index of a crate name in the prelude of the
    /// crate `from` belongs to, if it is one there.
    pub fn extern_by_name(&self, from: ModuleId, name: &str) -> Option<u32> {
        let owner = self.root_of(from);
        self.externs.iter().position(|e| e.owner == owner && e.name == name).map(|i| i as u32)
    }

    /// The hidden std source module that segment `seg` names under std
    /// extern `i` (`std::time`), when the std splice defined one
    /// (src/stdmods.rs).
    /// Also says whether the module is the whole std module (`full`) or
    /// an overlay that holds only some of its items.
    pub fn std_module_at(&self, i: u32, seg: Sym, interner: &Interner) -> Option<(ModuleId, bool)> {
        let e = &self.externs[i as usize];
        if !e.is_std_lib || self.std_modules.is_empty() {
            return None;
        }
        let seg = interner.get(seg);
        let row = crate::stdmods::STD_MODULES.iter().find(|m| m.paths.iter().any(|(k, s)| *k == e.name && *s == seg))?;
        self.std_modules.iter().find(|(n, _)| interner.get(*n) == row.name).map(|(_, m)| (*m, row.full))
    }

    /// The std source module a std path walks into at segment `seg`
    /// under std extern `i`, given the segment after it (`next`, read in
    /// `next_ns`): a whole module always, an overlay only when it
    /// defines `next` (other names stay the compiler's std items).
    pub fn std_module_walk(&self, i: u32, seg: Sym, next: Option<(Sym, Namespace)>, interner: &Interner) -> Option<ModuleId> {
        let (m, full) = self.std_module_at(i, seg, interner)?;
        if full {
            return Some(m);
        }
        let (n, ns) = next?;
        self.lookup(m, ns, n).is_some().then_some(m)
    }

    /// A deep std source module (`std::os::unix::net`): a row whose
    /// path has more than one segment, matched against the whole
    /// remaining path `segs`, so sibling paths under the same
    /// first segment (`std::os::unix::fs`) stay the compiler's.
    /// Returns the hidden module and how many segments it eats.
    /// An overlay row matches only when the segment after the deep
    /// path (when there is one) is defined in it.
    pub fn std_deep_module(&self, i: u32, segs: &[Sym], interner: &Interner) -> Option<(ModuleId, usize)> {
        let e = &self.externs[i as usize];
        if !e.is_std_lib || self.std_modules.is_empty() {
            return None;
        }
        for row in crate::stdmods::STD_MODULES {
            for (k, s) in row.paths {
                if *k != e.name || !s.contains("::") {
                    continue;
                }
                let parts: Vec<&str> = s.split("::").collect();
                if segs.len() < parts.len() || !parts.iter().zip(segs.iter()).all(|(p, g)| interner.get(*g) == *p) {
                    continue;
                }
                let m = self.std_modules.iter().find(|(n, _)| interner.get(*n) == row.name).map(|(_, m)| *m)?;
                if !row.full
                    && let Some(next) = segs.get(parts.len())
                    && ![Namespace::Type, Namespace::Value, Namespace::Macro].iter().any(|&ns| self.lookup(m, ns, *next).is_some())
                {
                    continue;
                }
                return Some((m, parts.len()));
            }
        }
        None
    }

    /// The path target an extern prelude entry resolves to: the
    /// dependency crate's root module when lust compiles it from
    /// source in this session, else the extern root itself.
    pub fn extern_target(&self, i: u32) -> Target {
        match self.externs[i as usize].root_module {
            Some(m) => Target::Module(m),
            None => Target::Extern(i),
        }
    }

    /// Looks up one first segment and checks visibility from `from`.
    /// Checks `from` itself, then the extern prelude, then the std
    /// prelude. Both modes read only `from`: as in rustc, items of a
    /// parent module are not in scope in a child (`mod a { use x::g; }`
    /// with `x` at the root is E0432), so a user `mod core` at the root
    /// does not shadow the `core` crate in any other module.
    fn first_segment(&self, from: ModuleId, name: Sym, ns: Namespace, _mode: PathMode, interner: &Interner) -> PathRes {
        match self.lookup(from, ns, name) {
            Some(BindState::One(b)) => {
                return if self.visible(&b.vis, b.def_module, from, interner) { PathRes::Done(b.target) } else { PathRes::Private };
            }
            Some(BindState::Ambiguous) => return PathRes::Ambiguous,
            None => {}
        }
        let name_str = interner.get(name);
        if let Some(i) = self.extern_by_name(from, name_str) {
            return PathRes::Done(self.extern_target(i));
        }
        if !self.modules[from.0 as usize].no_prelude && in_std_prelude(name_str, ns) {
            return PathRes::Prelude;
        }
        PathRes::Absent
    }

    /// Resolves one segment inside a module target, with visibility.
    fn segment_in(&self, module: ModuleId, name: Sym, ns: Namespace, from: ModuleId, interner: &Interner) -> PathRes {
        match self.lookup(module, ns, name) {
            Some(BindState::One(b)) => {
                if self.visible(&b.vis, b.def_module, from, interner) {
                    PathRes::Done(b.target)
                } else {
                    PathRes::Private
                }
            }
            Some(BindState::Ambiguous) => PathRes::Ambiguous,
            None => PathRes::Absent,
        }
    }

    /// Resolves a written path from module `from`. Segment names are
    /// already normalized by the caller: `crate`, `self`, and `super`
    /// arrive as those interned names. The walk consumes module
    /// segments in the type namespace and reads the last segment in
    /// `ns`; it stops at an Adt def (an associated item follows) or at
    /// an extern root.
    pub fn resolve_path(
        &self,
        from: ModuleId,
        segs: &[Sym],
        ns: Namespace,
        mode: PathMode,
        leading_colon: bool,
        interner: &Interner,
    ) -> PathRes {
        if segs.is_empty() {
            return PathRes::Absent;
        }
        let crate_sym = interner.intern("crate");
        let self_sym = interner.intern("self");
        let super_sym = interner.intern("super");
        let self_ty = interner.intern("Self");
        // `Self` in type position is a scope name, not a binding.
        if segs[0] == self_ty {
            return PathRes::Prelude;
        }
        let mut idx = 0usize;
        let cur: Target;
        if let Some(&root) = self.crate_magic.get(&segs[0]) {
            // A `$crate` magic segment from a cross-crate macro
            // expansion: the defining crate's root, direct dep or not.
            cur = Target::Module(root);
            idx = 1;
        } else if leading_colon {
            // `::dep::...`: extern prelude only.
            match self.extern_by_name(from, interner.get(segs[0])) {
                Some(i) => cur = self.extern_target(i),
                None => return PathRes::Absent,
            }
            idx = 1;
        } else if segs[0] == crate_sym {
            cur = Target::Module(self.root_of(from));
            idx = 1;
        } else if segs[0] == self_sym {
            cur = Target::Module(from);
            idx = 1;
        } else if segs[0] == super_sym {
            let mut m = from;
            while idx < segs.len() && segs[idx] == super_sym {
                match self.modules[m.0 as usize].parent {
                    Some(p) => m = p,
                    None => return PathRes::Absent,
                }
                idx += 1;
            }
            cur = Target::Module(m);
        } else {
            match self.first_segment(from, segs[0], ns_or_type(segs, ns), mode, interner) {
                PathRes::Done(t) => cur = t,
                other => return other,
            }
            idx = 1;
        }
        if idx >= segs.len() {
            return PathRes::Done(cur);
        }
        match self.walk_from(from, cur, &segs[idx..], ns, interner) {
            PathRes::Partial(t, rest) => PathRes::Partial(t, idx + rest),
            other => other,
        }
    }

    /// Continues a path walk from an already-resolved target over the
    /// remaining segments. The rewrite pass uses it for paths whose
    /// first segment came from a lexical (function-local) import.
    pub fn walk_from(&self, from: ModuleId, start: Target, segs: &[Sym], ns: Namespace, interner: &Interner) -> PathRes {
        let mut cur = start;
        let mut idx = 0usize;
        if segs.is_empty() {
            return PathRes::Done(cur);
        }
        loop {
            let seg = segs[idx];
            let last = idx + 1 == segs.len();
            let seg_ns = if last { ns } else { Namespace::Type };
            match cur {
                Target::Module(m) => match self.segment_in(m, seg, seg_ns, from, interner) {
                    PathRes::Done(t) => cur = t,
                    other => return other,
                },
                // `std::io::Write` and friends: the item lives in the
                // shipped platform crate (W-SHIM), so walk its tree.
                Target::Extern(i)
                    if self.externs[i as usize].is_std_lib
                        && self.externs[i as usize].name == "std"
                        && self.std_platform_has(&segs[idx..], from, interner) =>
                {
                    cur = Target::Module(self.std_platform.map(|(root, _)| root).unwrap_or(ModuleId(0)));
                    continue;
                }
                // Deep std source modules (`std::os::unix::net`) eat
                // their whole remaining path at the extern (W-CINTEROP2).
                Target::Extern(i)
                    if seg_ns == Namespace::Type
                        && let Some((m, eaten)) = self.std_deep_module(i, &segs[idx..], interner) =>
                {
                    cur = Target::Module(m);
                    idx += eaten;
                    if idx >= segs.len() {
                        return PathRes::Done(cur);
                    }
                    continue;
                }
                // `std::time` and the other std source modules walk into
                // their hidden module (W-STD-C).
                Target::Extern(i)
                    if seg_ns == Namespace::Type
                        && let Some(m) = self.std_module_walk(
                            i,
                            seg,
                            segs.get(idx + 1).map(|&n| (n, if idx + 2 == segs.len() { ns } else { Namespace::Type })),
                            interner,
                        ) =>
                {
                    cur = Target::Module(m);
                }
                Target::Def(_) | Target::Extern(_) | Target::Variant(..) => return PathRes::Partial(cur, idx),
            }
            idx += 1;
            if idx >= segs.len() {
                return PathRes::Done(cur);
            }
        }
    }

    /// Resolves the module part of a `use` path (all of it for a glob,
    /// all but the last segment for a single import). Returns the module
    /// or extern it names.
    pub fn resolve_module_path(&self, from: ModuleId, segs: &[Sym], leading_colon: bool, interner: &Interner) -> PathRes {
        if segs.is_empty() {
            return PathRes::Done(Target::Module(from));
        }
        match self.resolve_path(from, segs, Namespace::Type, PathMode::Use, leading_colon, interner) {
            PathRes::Done(t @ (Target::Module(_) | Target::Extern(_))) => PathRes::Done(t),
            // An extern root with more segments behind it is still the
            // extern: `std::cmp` as a module part resolves as extern.
            PathRes::Partial(Target::Extern(i), _) => PathRes::Done(Target::Extern(i)),
            PathRes::Done(_) => PathRes::Absent,
            other => other,
        }
    }
}

/// The namespace a path's first segment reads in: the type namespace
/// when more segments follow (it must name a module or a type), the
/// asked namespace for a one-segment path.
fn ns_or_type(segs: &[Sym], ns: Namespace) -> Namespace {
    if segs.len() > 1 { Namespace::Type } else { ns }
}

// ---------- The import fixpoint ----------

/// One flattened import from a `use` tree.
#[derive(Clone, Debug)]
pub struct Import {
    pub module: ModuleId,
    pub vis: VisKind,
    pub leading_colon: bool,
    pub span: Span,
    pub kind: ImportKind,
}

#[derive(Clone, Debug)]
pub enum ImportKind {
    /// `use a::b::Name;` or `use a::b::Name as Other;`. `name` is the
    /// binding name in the importing module.
    Single { path: Vec<Sym>, name: Sym },
    /// `use a::b::*;`.
    Glob { path: Vec<Sym> },
    /// The prefix of an empty group (`use a::b::{};`): it binds
    /// nothing, but rustc still resolves the prefix and rejects a bad
    /// one, so the path is checked and only that.
    CheckPath { path: Vec<Sym> },
    /// A leading `::` that is not in start position (`use a::{::b};`).
    /// The fixpoint reports it once and settles.
    BadLeading { path: Vec<Sym> },
}

/// Flattens one `use` tree into imports. Groups distribute their
/// prefix; `self` in a group is a prefix segment like any other here
/// (the import resolution reads a trailing `self` as the module).
pub fn flatten_use(tree: &ast::UseTree, module: ModuleId, vis: VisKind, out: &mut Vec<Import>, interner: &Interner) {
    fn walk(
        tree: &ast::UseTree,
        prefix: &mut Vec<Sym>,
        module: ModuleId,
        vis: &VisKind,
        leading: bool,
        out: &mut Vec<Import>,
        interner: &Interner,
    ) {
        let saved = prefix.len();
        prefix.extend(tree.prefix.iter().map(|s| s.name));
        // A leading `::` is the crate root and belongs in start
        // position only: `use {::std::..}` is a start, `use a::{::b}`
        // is an error (rustc E0433).
        if tree.leading_colon && saved > 0 {
            out.push(Import {
                module,
                vis: vis.clone(),
                leading_colon: true,
                span: tree.span,
                kind: ImportKind::BadLeading { path: prefix.clone() },
            });
            prefix.truncate(saved);
            return;
        }
        let leading = leading || tree.leading_colon;
        match &tree.kind {
            ast::UseKind::Simple { rename } => {
                if let Some(last) = prefix.last().copied() {
                    let name = rename.unwrap_or(last);
                    // `use a::self;` binds the module under its own name
                    // (or the rename); keep the path whole and let the
                    // resolver read the trailing `self`.
                    let _ = interner;
                    out.push(Import {
                        module,
                        vis: vis.clone(),
                        leading_colon: leading,
                        span: tree.span,
                        kind: ImportKind::Single { path: prefix.clone(), name },
                    });
                }
            }
            ast::UseKind::Glob => {
                out.push(Import {
                    module,
                    vis: vis.clone(),
                    leading_colon: leading,
                    span: tree.span,
                    kind: ImportKind::Glob { path: prefix.clone() },
                });
            }
            ast::UseKind::Group(children) => {
                if children.is_empty() {
                    out.push(Import {
                        module,
                        vis: vis.clone(),
                        leading_colon: leading,
                        span: tree.span,
                        kind: ImportKind::CheckPath { path: prefix.clone() },
                    });
                }
                for c in children {
                    walk(c, prefix, module, vis, leading, out, interner);
                }
            }
        }
        prefix.truncate(saved);
    }
    walk(tree, &mut Vec::new(), module, &vis, tree.leading_colon, out, interner);
}

/// Runs the import fixpoint of section 1.3 over the tables. Explicit
/// imports and globs are retried together until a full sweep changes
/// nothing. Returns diagnostics for imports that never resolved and for
/// duplicate explicit imports. An import through an extern crate root
/// (`use std::...`, `use dep::Name`) makes no local binding here: the
/// rewrite pass leaves those paths to the std compat layer, and binding
/// queries for them answer through the extern flat record the worklist
/// adds.
pub fn run_imports(tables: &mut ResolvedTables, imports: &[Import], interner: &Interner) -> Result<Vec<Diag>, String> {
    let self_sym = interner.intern("self");
    let mut diags = Vec::new();
    let mut pending: Vec<(usize, &Import)> = imports.iter().enumerate().collect();
    let mut resolved = vec![false; imports.len()];
    let cap = tables.modules.len() + 2;
    let mut rounds = 0;
    loop {
        rounds += 1;
        if rounds > cap + imports.len() {
            return Err("internal: import worklist did not settle".to_string());
        }
        let mut changed = false;
        let mut still: Vec<(usize, &Import)> = Vec::new();
        for (i, imp) in pending.drain(..) {
            match try_import(tables, imp, self_sym, interner, &mut diags) {
                TryOut::Done(did_change) => {
                    changed |= did_change;
                    resolved[i] = true;
                }
                TryOut::Stay { changed: c, resolved: r } => {
                    changed |= c;
                    resolved[i] |= r;
                    still.push((i, imp));
                }
                TryOut::Wait => still.push((i, imp)),
            }
        }
        pending = still;
        if pending.is_empty() || !changed {
            break;
        }
    }
    for (i, imp) in &pending {
        if resolved[*i] {
            continue;
        }
        let what = match &imp.kind {
            ImportKind::Single { path, .. }
            | ImportKind::Glob { path }
            | ImportKind::CheckPath { path }
            | ImportKind::BadLeading { path } => path.iter().map(|s| interner.get(*s)).collect::<Vec<_>>().join("::"),
        };
        diags.push(Diag::new(
            "L0506",
            imp.span,
            format!("unresolved import `{what}`"),
            "Check the path: every segment must name a module or item that is visible here.",
        ));
    }
    Ok(diags)
}

enum TryOut {
    Done(bool),
    /// Keep this import for the next sweep (a live glob).
    Stay {
        changed: bool,
        resolved: bool,
    },
    Wait,
}

/// The namespaces an explicit import of a canonical std path
/// binds, or None when the path is not a std item (or module)
/// lust knows by full path. `std::vec` is both a module (type
/// namespace) and a macro (macro namespace), so it binds in both.
pub fn std_import_namespaces(interner: &Interner, path: &[Sym]) -> Option<Vec<Namespace>> {
    use crate::ty::lang::{StdPathKind, std_is_module_path, std_path_kind};
    let strs: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
    let mut out = match std_path_kind(&strs) {
        Some(StdPathKind::Type | StdPathKind::Trait) => vec![Namespace::Type],
        Some(StdPathKind::Fn | StdPathKind::Variant) => vec![Namespace::Value],
        Some(StdPathKind::Macro) => vec![Namespace::Macro],
        None if std_is_module_path(&strs) => vec![Namespace::Type],
        // A std platform module (W-SHIM): its items resolve through the
        // alias into the platform crate.
        None if strs.len() == 2 && strs[0] == "std" && STD_PLATFORM_MODULES.contains(&strs[1]) => vec![Namespace::Type],
        None => return None,
    };
    if std_is_module_path(&strs) && !out.contains(&Namespace::Type) {
        out.push(Namespace::Type);
    }
    Some(out)
}

/// Records one std import alias in the tables, with the same
/// duplicate rules as a local explicit import: a name already
/// bound explicitly in the module (a local item, an earlier
/// import, or an earlier std alias) reports `dup_diag` and the
/// first binding keeps the name. `as _` binds no usable name: it is
/// stored under a synthetic name keyed by the path (never a
/// duplicate), so a std trait imported that way is in scope for its
/// methods (`use std::fmt::Write as _;` for `write!` into a String).
fn record_std_alias(tables: &mut ResolvedTables, imp: &Import, path: &[Sym], name: Sym, interner: &Interner, diags: &mut Vec<Diag>) -> bool {
    let Some(namespaces) = std_import_namespaces(interner, path) else { return false };
    let anon = interner.get(name) == "_";
    let name = if anon {
        let full: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
        interner.intern(&format!("$lust$anon$std${}", full.join("::")))
    } else {
        name
    };
    let mut dup = false;
    let mut inserted = false;
    for ns in namespaces {
        let key = (imp.module, ns_index(ns) as u8, name);
        if anon && tables.std_aliases.contains_key(&key) {
            continue;
        }
        if explicit_exists(tables, imp, ns, name) || tables.explicit_std_alias(key) {
            dup = true;
            continue;
        }
        // An explicit alias replaces a glob one of the same name.
        tables.std_glob_aliases.remove(&key);
        tables.std_aliases.insert(key, (imp.vis.clone(), path.to_vec()));
        inserted = true;
    }
    if dup {
        diags.push(dup_diag(imp, name, interner));
    }
    inserted
}

/// Tries one import against the current tables.
fn try_import(tables: &mut ResolvedTables, imp: &Import, self_sym: Sym, interner: &Interner, diags: &mut Vec<Diag>) -> TryOut {
    // `use std::io::Write;`: an item of the shipped platform crate
    // (W-SHIM) imports from that crate's module tree.
    if let ImportKind::Single { path, name } = &imp.kind
        && tables.std_platform.is_some()
        && let Some(redirected) = tables.std_platform_path(path, imp.module, interner)
        && (imp.leading_colon || tables.std_is_extern(imp.module, interner))
    {
        let imp2 = Import { kind: ImportKind::Single { path: redirected, name: *name }, leading_colon: false, ..imp.clone() };
        return try_import(tables, &imp2, self_sym, interner, diags);
    }
    match &imp.kind {
        ImportKind::BadLeading { .. } => {
            diags.push(Diag::new(
                "L0506",
                imp.span,
                "the crate root in a `use` path can only be used in start position",
                "Move the leading `::` to the start of the whole import, or remove it.",
            ));
            TryOut::Done(false)
        }
        ImportKind::CheckPath { path } => {
            // An empty group binds nothing, but its prefix must still
            // name a module (or an enum, like a glob prefix).
            if path.is_empty() {
                return TryOut::Done(false);
            }
            match tables.resolve_module_path(imp.module, path, imp.leading_colon, interner) {
                PathRes::Done(_) => TryOut::Done(false),
                PathRes::Private => {
                    diags.push(private_diag("that module", imp.span));
                    TryOut::Done(false)
                }
                _ => match tables.resolve_path(imp.module, path, Namespace::Type, PathMode::Use, imp.leading_colon, interner) {
                    PathRes::Done(Target::Def(adt)) if tables.variants.contains_key(&adt) => TryOut::Done(false),
                    PathRes::Private => {
                        diags.push(private_diag("that module", imp.span));
                        TryOut::Done(false)
                    }
                    _ => TryOut::Wait,
                },
            }
        }
        ImportKind::Glob { path } => {
            if path.is_empty() {
                // `use *;` and `use ::*;` name no module at all.
                diags.push(Diag::new(
                    "L0506",
                    imp.span,
                    "cannot glob-import all possible crates",
                    "Name the module before the `*`, such as `use a::*;`.",
                ));
                return TryOut::Done(false);
            }
            match tables.resolve_path(imp.module, path, Namespace::Type, PathMode::Use, imp.leading_colon, interner) {
                // `use a::E::*` imports the enum's variants.
                PathRes::Done(Target::Def(adt)) if tables.variants.contains_key(&adt) => {
                    let mut changed = false;
                    // Variants take the enum's visibility.
                    let (vis, def_module) = match tables.def_info.get(&adt) {
                        Some(info) => tables.glob_vis(imp, &info.vis, info.module, interner),
                        None => (imp.vis.clone(), imp.module),
                    };
                    for v in tables.variants[&adt].clone() {
                        let bind = Bind { target: Target::Variant(adt, v), vis: vis.clone(), rank: 1, def_module };
                        if tables.insert(imp.module, Namespace::Value, v, bind) == InsertOut::Changed {
                            changed = true;
                        }
                    }
                    TryOut::Done(changed)
                }
                _ => match tables.resolve_module_path(imp.module, path, imp.leading_colon, interner) {
                    PathRes::Done(Target::Module(src)) => {
                        if src == imp.module {
                            return TryOut::Done(false);
                        }
                        let mut changed = false;
                        // Copy in deterministic name order.
                        let mut entries: Vec<(Namespace, Sym, Bind)> = Vec::new();
                        for ns in [Namespace::Type, Namespace::Value, Namespace::Macro] {
                            let mut names: Vec<(&Sym, &BindState)> = tables.maps[src.0 as usize][ns_index(ns)].iter().collect();
                            names.sort_by(|a, b| interner.get(*a.0).cmp(interner.get(*b.0)));
                            for (name, state) in names {
                                if let BindState::One(b) = state
                                    && tables.visible(&b.vis, b.def_module, imp.module, interner)
                                {
                                    let (vis, def_module) = tables.glob_vis(imp, &b.vis, b.def_module, interner);
                                    entries.push((ns, *name, Bind { target: b.target, vis, rank: 1, def_module }));
                                }
                            }
                        }
                        for (ns, name, bind) in entries {
                            if tables.insert_glob(imp.module, ns, name, bind, src) == InsertOut::Changed {
                                changed = true;
                            }
                        }
                        // An ambiguous name in the source is ambiguous
                        // through this glob too, as in rustc: copying
                        // only its settled names would leave a stale
                        // binding from an earlier sweep, or let another
                        // glob's item win silently. The source records
                        // itself in `glob_src`, so its own later
                        // settling (an explicit import there) can undo
                        // exactly this poisoning (`insert_glob`).
                        for ns in [Namespace::Type, Namespace::Value, Namespace::Macro] {
                            let mut names: Vec<Sym> = tables.maps[src.0 as usize][ns_index(ns)]
                                .iter()
                                .filter_map(|(name, state)| matches!(state, BindState::Ambiguous).then_some(*name))
                                .collect();
                            names.sort_by(|a, b| interner.get(*a).cmp(interner.get(*b)));
                            for name in names {
                                if insert_ambiguous(tables, imp.module, ns, name) {
                                    tables.glob_src.insert((imp.module, ns_index(ns) as u8, name), src);
                                    changed = true;
                                }
                            }
                        }
                        // The std imports of the source module
                        // (`pub use std::rc::Rc;`) bind like its other names.
                        for (ns, name, vis, def_module, path) in tables.visible_std_aliases(src, imp.module, interner) {
                            let (vis, def_module) = tables.glob_vis(imp, &vis, def_module, interner);
                            let ns = [Namespace::Type, Namespace::Value, Namespace::Macro][ns as usize];
                            changed |= tables.insert_glob_std_alias(imp.module, ns, name, vis, def_module, path);
                        }
                        // A glob stays live: new names in the source module can
                        // appear as other imports settle. It stays pending until
                        // a no-change sweep; the caller drops a resolved glob
                        // without error at the end.
                        TryOut::Stay { changed, resolved: true }
                    }
                    PathRes::Done(Target::Extern(i)) => {
                        if let Some(why) = &tables.externs[i as usize].unsupported {
                            diags.push(unsupported_diag(why, imp.span));
                            return TryOut::Done(false);
                        }
                        // `use std::cmp::Ordering::*;`: the std enum's
                        // variants bind as std aliases (value namespace),
                        // below any binding the module already has.
                        let mut changed = false;
                        if tables.externs[i as usize].is_std_lib {
                            let strs: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
                            if std_glob_shadows_prelude(&strs) {
                                diags.push(std_glob_diag(imp.span));
                                return TryOut::Done(false);
                            }
                            for v in crate::ty::lang::std_enum_variants(&strs) {
                                let name = interner.intern(v);
                                let mut full = path.clone();
                                full.push(name);
                                changed |= tables.insert_glob_std_alias(imp.module, Namespace::Value, name, imp.vis.clone(), imp.module, full);
                            }
                        }
                        TryOut::Done(changed)
                    }
                    PathRes::Private => {
                        diags.push(private_diag("that module", imp.span));
                        TryOut::Done(false)
                    }
                    _ => TryOut::Wait,
                },
            }
        }
        ImportKind::Single { path, name } => {
            // `use a::E::V` imports one enum variant.
            if let PathRes::Partial(Target::Def(adt), rest) =
                tables.resolve_path(imp.module, path, Namespace::Type, PathMode::Use, imp.leading_colon, interner)
                && rest + 1 == path.len()
                && tables.variants.get(&adt).is_some_and(|vs| vs.contains(&path[rest]))
            {
                if !tables.check_reexport(imp, Target::Variant(adt, path[rest]), interner.get(path[rest]), interner, diags) {
                    return TryOut::Done(false);
                }
                let dup = explicit_exists(tables, imp, Namespace::Value, *name);
                let out = tables.insert(
                    imp.module,
                    Namespace::Value,
                    import_bind_name(*name, Target::Variant(adt, path[rest]), interner),
                    Bind { target: Target::Variant(adt, path[rest]), vis: imp.vis.clone(), rank: 2, def_module: imp.module },
                );
                if dup {
                    diags.push(dup_diag(imp, *name, interner));
                } else {
                    report_dup(out, imp, *name, interner, diags);
                }
                return TryOut::Done(out == InsertOut::Changed);
            }
            let (mod_path, last) = path.split_at(path.len() - 1);
            let last = last[0];
            let crate_sym = interner.intern("crate");
            let super_sym = interner.intern("super");
            let self_ty = interner.intern("Self");
            let kw = |s: Sym| s == crate_sym || s == self_sym || s == super_sym;
            // `use crate as x;`, `use super::super as x;`: the whole path
            // is module keywords and the rename is the binding name.
            // Without a rename these keep the plain lookup below, which
            // finds no such name and reports the import unresolved.
            if last != self_sym && *name != last && path.iter().all(|&s| kw(s)) {
                return match tables.resolve_module_path(imp.module, path, imp.leading_colon, interner) {
                    PathRes::Done(target) => {
                        if !tables.check_reexport(imp, target, interner.get(*name), interner, diags) {
                            return TryOut::Done(false);
                        }
                        let bind_name = import_bind_name(*name, target, interner);
                        let dup = explicit_exists(tables, imp, Namespace::Type, bind_name);
                        let out = tables.insert(
                            imp.module,
                            Namespace::Type,
                            bind_name,
                            Bind { target, vis: imp.vis.clone(), rank: 2, def_module: imp.module },
                        );
                        if dup && interner.get(*name) != "_" {
                            diags.push(dup_diag(imp, *name, interner));
                        } else {
                            report_dup(out, imp, *name, interner, diags);
                        }
                        TryOut::Done(out == InsertOut::Changed)
                    }
                    PathRes::Private => {
                        diags.push(private_diag("that module", imp.span));
                        TryOut::Done(false)
                    }
                    _ => TryOut::Wait,
                };
            }
            if last == self_sym {
                // `use a::b::{self}`: bind the module itself. The binding
                // name is the segment before `self`, or the rename (the
                // parser keeps an `as` name in `name`). When there is no
                // rename and no plain segment to take the name from
                // (`use self;`, `use crate::self;`), rustc rejects the
                // import: it needs to be explicitly named.
                if *name == self_sym && !matches!(mod_path.last(), Some(&c) if !kw(c) && c != self_ty) {
                    diags.push(Diag::new(
                        "L0506",
                        imp.span,
                        "this import needs to be explicitly named",
                        "Add a rename, such as `use self as here;`.",
                    ));
                    return TryOut::Done(false);
                }
                // A std module (`use std::rc::{self, Rc}`) binds as the
                // std alias `use std::rc;` records, not as the crate root.
                if mod_path.len() > 1
                    && let PathRes::Done(Target::Extern(i)) | PathRes::Partial(Target::Extern(i), _) =
                        tables.resolve_module_path(imp.module, mod_path, imp.leading_colon, interner)
                {
                    if let Some(why) = &tables.externs[i as usize].unsupported {
                        diags.push(unsupported_diag(why, imp.span));
                        return TryOut::Done(false);
                    }
                    if tables.externs[i as usize].is_std_lib {
                        let bind_name = if *name == self_sym { *mod_path.last().unwrap() } else { *name };
                        return TryOut::Done(record_std_alias(tables, imp, mod_path, bind_name, interner, diags));
                    }
                }
                // The prefix names a module, or an enum whose own name
                // `self` binds (`use a::E::{self, V}`).
                let target = match tables.resolve_module_path(imp.module, mod_path, imp.leading_colon, interner) {
                    PathRes::Done(target) => Some(target),
                    PathRes::Private => {
                        diags.push(private_diag("that module", imp.span));
                        return TryOut::Done(false);
                    }
                    _ => match tables.resolve_path(imp.module, mod_path, Namespace::Type, PathMode::Use, imp.leading_colon, interner) {
                        PathRes::Done(Target::Def(adt)) if tables.variants.contains_key(&adt) => Some(Target::Def(adt)),
                        PathRes::Private => {
                            diags.push(private_diag("that module", imp.span));
                            return TryOut::Done(false);
                        }
                        _ => None,
                    },
                };
                let Some(target) = target else { return TryOut::Wait };
                if !tables.check_reexport(imp, target, interner.get(*name), interner, diags) {
                    return TryOut::Done(false);
                }
                let bind_name = if *name == self_sym { mod_path.last().copied().unwrap_or(*name) } else { *name };
                let store_name = import_bind_name(bind_name, target, interner);
                let dup = explicit_exists(tables, imp, Namespace::Type, store_name);
                let out = tables.insert(
                    imp.module,
                    Namespace::Type,
                    store_name,
                    Bind { target, vis: imp.vis.clone(), rank: 2, def_module: imp.module },
                );
                if dup && interner.get(bind_name) != "_" {
                    diags.push(dup_diag(imp, bind_name, interner));
                } else {
                    report_dup(out, imp, bind_name, interner, diags);
                }
                return TryOut::Done(out == InsertOut::Changed);
            }
            // `use ::name;`: with a leading colon the one segment reads
            // in the extern prelude only, never in this module.
            if imp.leading_colon && mod_path.is_empty() {
                return match tables.resolve_path(imp.module, path, Namespace::Type, PathMode::Use, true, interner) {
                    PathRes::Done(Target::Extern(i)) => {
                        if let Some(why) = &tables.externs[i as usize].unsupported {
                            diags.push(unsupported_diag(why, imp.span));
                        }
                        TryOut::Done(false)
                    }
                    PathRes::Done(Target::Module(src)) => {
                        let bind_name = import_bind_name(*name, Target::Module(src), interner);
                        let dup = explicit_exists(tables, imp, Namespace::Type, bind_name);
                        let out = tables.insert(
                            imp.module,
                            Namespace::Type,
                            bind_name,
                            Bind { target: Target::Module(src), vis: imp.vis.clone(), rank: 2, def_module: imp.module },
                        );
                        if dup && interner.get(*name) != "_" {
                            diags.push(dup_diag(imp, *name, interner));
                        } else {
                            report_dup(out, imp, *name, interner, diags);
                        }
                        TryOut::Done(out == InsertOut::Changed)
                    }
                    PathRes::Private => {
                        diags.push(private_diag("that module", imp.span));
                        TryOut::Done(false)
                    }
                    _ => TryOut::Wait,
                };
            }
            // `use std;` and `use std as s;`: the one segment names
            // the extern crate root itself, so there is no module
            // part to split off.
            if path.len() == 1
                && let PathRes::Done(Target::Extern(i)) =
                    tables.resolve_path(imp.module, path, Namespace::Type, PathMode::Use, imp.leading_colon, interner)
            {
                let mut inserted = false;
                if let Some(why) = &tables.externs[i as usize].unsupported {
                    diags.push(unsupported_diag(why, imp.span));
                } else if tables.externs[i as usize].is_std_lib {
                    inserted = record_std_alias(tables, imp, path, *name, interner, diags);
                }
                return TryOut::Done(inserted);
            }
            let modres = match tables.resolve_module_path(imp.module, mod_path, imp.leading_colon, interner) {
                // `use std::marker::PhantomData;`: an item of a std
                // source overlay module imports from it (W-STD-C).
                PathRes::Done(Target::Extern(i))
                    if mod_path.len() == 2
                        && let Some((m, false)) = tables.std_module_at(i, mod_path[1], interner)
                        && [Namespace::Type, Namespace::Value, Namespace::Macro].iter().any(|&ns| tables.lookup(m, ns, last).is_some()) =>
                {
                    PathRes::Done(Target::Module(m))
                }
                other => other,
            };
            match modres {
                PathRes::Done(Target::Module(src)) => {
                    // Bind the name in every namespace that has it.
                    let mut any = false;
                    let mut changed = false;
                    let mut saw_private = false;
                    // A re-export of an import binding reaches no further
                    // than that binding (rustc E0364); `check_reexport`
                    // below checks the item's own visibility.
                    let mut narrower = false;
                    let mut found: Vec<(Namespace, Bind)> = Vec::new();
                    let mut alias_paths: Vec<Vec<Sym>> = Vec::new();
                    for ns in [Namespace::Type, Namespace::Value, Namespace::Macro] {
                        match tables.lookup(src, ns, last) {
                            Some(BindState::One(b)) => {
                                if tables.visible(&b.vis, b.def_module, imp.module, interner) {
                                    any = true;
                                    let is_macro = matches!(b.target, Target::Def(d) if tables.def_info.get(&d).is_some_and(|i| i.kind == ResKind::Macro));
                                    narrower |= imp.vis != VisKind::Priv
                                        && !is_macro
                                        && !matches!(b.target, Target::Extern(_))
                                        && !tables.vis_within(&imp.vis, imp.module, &b.vis, b.def_module, interner);
                                    found.push((ns, Bind { target: b.target, vis: imp.vis.clone(), rank: 2, def_module: imp.module }));
                                } else {
                                    saw_private = true;
                                }
                            }
                            Some(BindState::Ambiguous) => {
                                // An explicit import of an ambiguous name
                                // cannot settle it; it stays ambiguous.
                                any = true;
                                let out = insert_ambiguous(tables, imp.module, ns, *name);
                                changed |= out;
                            }
                            // A std import in the source module binds
                            // no target; importing it onward copies
                            // the alias under this import's name.
                            None => {
                                let key = (src, ns_index(ns) as u8, last);
                                if let Some((avis, apath)) = tables.std_aliases.get(&key).cloned() {
                                    let adef = tables.std_alias_def_module(key);
                                    if tables.visible(&avis, adef, imp.module, interner) {
                                        any = true;
                                        narrower |= imp.vis != VisKind::Priv && !tables.vis_within(&imp.vis, imp.module, &avis, adef, interner);
                                        if !alias_paths.contains(&apath) {
                                            alias_paths.push(apath);
                                        }
                                    } else {
                                        saw_private = true;
                                    }
                                }
                            }
                        }
                    }
                    if !any {
                        if saw_private {
                            diags.push(private_diag(interner.get(last), imp.span));
                            return TryOut::Done(false);
                        }
                        return TryOut::Wait;
                    }
                    // One re-export check per distinct target: a name in
                    // two namespaces usually names two items, a struct
                    // names the same def in type and value position.
                    let mut seen_targets: Vec<Target> = Vec::new();
                    for (_, bind) in &found {
                        if seen_targets.contains(&bind.target) {
                            continue;
                        }
                        seen_targets.push(bind.target);
                        if !tables.check_reexport(imp, bind.target, interner.get(last), interner, diags) {
                            return TryOut::Done(false);
                        }
                    }
                    if narrower {
                        diags.push(reexport_diag(interner.get(last), imp.span));
                        return TryOut::Done(false);
                    }
                    let mut dup_reported = false;
                    for (ns, bind) in found {
                        let bind_name = import_bind_name(*name, bind.target, interner);
                        // The macro self re-export idiom: `macro_rules! m`
                        // plus one `use m;` in the defining module is one
                        // binding in rustc, and the `use` sets how far the
                        // macro name reaches. It replaces the definition's
                        // private binding instead of duplicating it.
                        let is_macro_self_use = ns == Namespace::Macro
                            && bind_name == *name
                            && matches!(bind.target, Target::Def(d) if tables.def_info.get(&d).is_some_and(|i| i.kind == ResKind::Macro && i.module == imp.module))
                            && !tables.macro_self_uses.contains_key(&(imp.module, bind_name));
                        if is_macro_self_use {
                            tables.macro_self_uses.insert((imp.module, bind_name), ());
                            let changed_now = !matches!(tables.lookup(imp.module, ns, bind_name), Some(BindState::One(old)) if old.vis == bind.vis && old.target == bind.target);
                            tables.maps[imp.module.0 as usize][ns_index(ns)].insert(bind_name, BindState::One(bind));
                            changed |= changed_now;
                            continue;
                        }
                        // An earlier std alias of the same name in the
                        // same namespace is an explicit binding too.
                        let dup = explicit_exists(tables, imp, ns, bind_name)
                            || tables.explicit_std_alias((imp.module, ns_index(ns) as u8, bind_name));
                        let out = tables.insert(imp.module, ns, bind_name, bind);
                        if dup && interner.get(*name) != "_" {
                            if !dup_reported {
                                diags.push(dup_diag(imp, *name, interner));
                                dup_reported = true;
                            }
                        } else {
                            report_dup(out, imp, *name, interner, diags);
                        }
                        changed |= out == InsertOut::Changed;
                    }
                    for apath in &alias_paths {
                        changed |= record_std_alias(tables, imp, apath, *name, interner, diags);
                    }
                    TryOut::Done(changed)
                }
                PathRes::Done(Target::Extern(i)) => {
                    // `use dep::Name` where the path did not enter a
                    // source dependency's module tree: a canonical
                    // `std` path records an alias the rewrite pass
                    // expands back to the full path (renames bind,
                    // and a plain imported fn or module name works
                    // the same way). An unsupported dependency
                    // (adapter, shim, or other crate with no lust
                    // form yet) rejects at the import with L0508
                    // naming the crate, since its item names are
                    // unknown and a later plain use could not be
                    // told from a typo.
                    let mut inserted = false;
                    if let Some(why) = &tables.externs[i as usize].unsupported {
                        diags.push(unsupported_diag(why, imp.span));
                    } else if mod_path.len() == 1
                        && let Some((m, true)) = tables.std_module_at(i, last, interner)
                    {
                        // `use std::time;`: a std source module binds
                        // like a local module (W-STD-C).
                        let bind_name = import_bind_name(*name, Target::Module(m), interner);
                        let dup = explicit_exists(tables, imp, Namespace::Type, bind_name);
                        let out = tables.insert(
                            imp.module,
                            Namespace::Type,
                            bind_name,
                            Bind { target: Target::Module(m), vis: imp.vis.clone(), rank: 2, def_module: imp.module },
                        );
                        if dup && interner.get(*name) != "_" {
                            diags.push(dup_diag(imp, *name, interner));
                        } else {
                            report_dup(out, imp, *name, interner, diags);
                        }
                        inserted = out == InsertOut::Changed;
                    } else if tables.externs[i as usize].is_std_lib {
                        inserted = record_std_alias(tables, imp, path, *name, interner, diags);
                    }
                    TryOut::Done(inserted)
                }
                PathRes::Done(_) => TryOut::Wait,
                PathRes::Private => {
                    diags.push(private_diag("that module", imp.span));
                    TryOut::Done(false)
                }
                _ => TryOut::Wait,
            }
        }
    }
}

/// True when two canonical std paths name one item: equal, or equal
/// after the crate segment (`core::cell::RefCell` is `std::cell::RefCell`).
/// Other spellings of one item count as two (an ambiguity, which only
/// rejects).
fn same_std_item(a: &[Sym], b: &[Sym]) -> bool {
    a == b || (a.len() > 1 && a.len() == b.len() && a[1..] == b[1..])
}

/// Marks a name ambiguous through an explicit import of an ambiguous
/// glob name. Returns true on a change.
fn insert_ambiguous(tables: &mut ResolvedTables, module: ModuleId, ns: Namespace, name: Sym) -> bool {
    let map = &mut tables.maps[module.0 as usize][ns_index(ns)];
    match map.get(&name) {
        Some(BindState::Ambiguous) | Some(BindState::One(Bind { rank: 2, .. })) => false,
        _ => {
            map.insert(name, BindState::Ambiguous);
            true
        }
    }
}

/// True when `name` in `ns` is already bound in the importing module
/// by a local item or by an earlier explicit import. Rust rejects a
/// second explicit binding even for the same target (E0252, E0255),
/// which the rank rules in `insert` alone treat as `Same`, so callers
/// check this before they insert and report `dup_diag` once.
fn explicit_exists(tables: &ResolvedTables, imp: &Import, ns: Namespace, name: Sym) -> bool {
    matches!(tables.lookup(imp.module, ns, name), Some(BindState::One(b)) if b.rank >= 2)
}

/// The L0106 diagnostic for a name bound more than once in one module.
fn dup_diag(imp: &Import, name: Sym, interner: &Interner) -> Diag {
    Diag::new(
        "L0106",
        imp.span,
        format!("`{}` is defined more than once", interner.get(name)),
        "Rename one of the imports with `as`, or remove one.",
    )
}

/// The binding name for one explicit import. `as _` binds no usable
/// name, so it is stored under a synthetic name keyed by its target:
/// several `as _` imports of different items (the usual trait imports)
/// then coexist, and a repeat of one item lands on the same key. The
/// synthetic name is not a legal Rust identifier, so source text can
/// never name it.
pub fn import_bind_name(name: Sym, target: Target, interner: &Interner) -> Sym {
    if interner.get(name) != "_" {
        return name;
    }
    let key = match target {
        Target::Def(d) => d.hash.0 ^ ((d.krate.0 as u64) << 1),
        Target::Module(m) => (m.0 as u64) ^ 0x9e37_79b9,
        Target::Extern(i) => (i as u64) ^ 0x51f_15e,
        Target::Variant(d, s) => d.hash.0 ^ (s.0 as u64).rotate_left(17),
    };
    interner.intern(&format!("$lust$anon${key:x}"))
}

/// Reports a duplicate explicit import (two sources, one binding name).
/// An `as _` import binds no name and is never a duplicate.
fn report_dup(out: InsertOut, imp: &Import, name: Sym, interner: &Interner, diags: &mut Vec<Diag>) {
    if out == InsertOut::Dup && interner.get(name) != "_" {
        diags.push(dup_diag(imp, name, interner));
    }
}

/// The L0508 diagnostic for a use of a dependency crate that has no
/// lust source, adapter, or shim form yet. `why` names the crate.
pub fn unsupported_diag(why: &str, span: Span) -> Diag {
    Diag::new("L0508", span, why.to_string(), "Build this crate with Cargo, or remove the dependency from the lust dev build.")
}

/// The L0510 diagnostic for a name that exists but is not visible. The
/// fix names the smallest widening that would work, and never applies it.
pub fn private_diag(name: &str, span: Span) -> Diag {
    Diag::new(
        "L0510",
        span,
        format!("`{name}` is private"),
        "Make the item `pub(crate)` (the smallest widening that works), or add a public re-export.",
    )
}

/// The L0510 diagnostic for a re-export that reaches further than the
/// item or binding it re-exports (rustc E0364).
fn reexport_diag(name: &str, span: Span) -> Diag {
    Diag::new(
        "L0510",
        span,
        format!("`{name}` is private, and cannot be re-exported"),
        "Make the item `pub`, or lower the visibility of the `use` to match.",
    )
}

/// The L0507 diagnostic for a use of a glob-ambiguous name.
/// True for a glob of a std module that brings its own `Result`
/// (`std::io`, `std::fmt`, `std::thread`): it shadows the prelude's
/// `Result`, which lust would still use.
pub fn std_glob_shadows_prelude(path: &[&str]) -> bool {
    path.len() == 2 && matches!(path[0], "std" | "core") && matches!(path[1], "io" | "fmt" | "thread")
}

/// L0505 for a glob import of `std::io`, `std::fmt`, or `std::thread`.
pub fn std_glob_diag(span: Span) -> Diag {
    Diag::new(
        "L0505",
        span,
        "a glob import of a std module with its own `Result` is not supported yet",
        "Import the std items you use by name, such as `use std::io::{self, Write};`.",
    )
}

/// L0505 for a name a std glob import may bring or shadow: lust does
/// not know every name a std module exports.
pub fn std_glob_name_diag(name: &str, span: Span) -> Diag {
    Diag::new(
        "L0505",
        span,
        format!("`{name}` next to a std glob import is not supported yet: the glob may also bring `{name}`"),
        "Import the std items you use by name instead of with `*`, or import this name explicitly.",
    )
}

pub fn ambiguous_diag(name: &str, span: Span) -> Diag {
    Diag::new(
        "L0507",
        span,
        format!("`{name}` is ambiguous: two glob imports bring different items with this name"),
        "Import the one you mean explicitly: an explicit import wins over globs.",
    )
}
