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

/// One module of the crate's module tree.
#[derive(Clone, Debug)]
pub struct ModuleInfo {
    pub parent: Option<ModuleId>,
    /// The module's own name (the crate name for the root).
    pub name: Sym,
    /// Names from the crate root to this module (empty for the root).
    pub path: Vec<Sym>,
    pub vis: VisKind,
    pub span: Span,
    /// `#[no_implicit_prelude]` applies (inherited from the parent too).
    pub no_prelude: bool,
}

/// One extern crate in the extern prelude.
#[derive(Clone, Debug)]
pub struct ExternInfo {
    /// The name paths use (`std`, `core`, a renamed dependency).
    pub name: String,
    pub def: DefId,
    /// True for `std`, `core`, and `alloc`: paths rooted there keep the
    /// std compat handling in collect and check.
    pub is_std_lib: bool,
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
    /// Adt def -> variant names, for variant imports and `use E::*`.
    pub variants: FxMap<DefId, Vec<Sym>>,
    pub def_info: FxMap<DefId, DefInfo>,
    /// Each module's own def (index by ModuleId), filled at registration.
    pub module_defs: Vec<DefId>,
    /// Flat name -> def, per namespace, for the merged AST's names. The
    /// checker resolves the rewritten flat names in the root module, so a
    /// root query for a flat name answers here.
    pub flat: [FxMap<Sym, DefId>; 3],
    /// The defining module of each flattened fn, in LocalDefId order.
    pub fn_module: Vec<ModuleId>,
}

impl ResolvedTables {
    /// An empty table set with only the root module.
    pub fn new(crate_name: Sym) -> ResolvedTables {
        ResolvedTables {
            modules: vec![ModuleInfo {
                parent: None,
                name: crate_name,
                path: Vec::new(),
                vis: VisKind::Pub,
                span: Span::default(),
                no_prelude: false,
            }],
            maps: vec![Default::default()],
            externs: Vec::new(),
            assoc_vis: FxMap::default(),
            field_vis: FxMap::default(),
            variants: FxMap::default(),
            def_info: FxMap::default(),
            module_defs: vec![DefId::PLACEHOLDER],
            flat: Default::default(),
            fn_module: Vec::new(),
        }
    }

    /// Adds a module under a parent and returns its id.
    pub fn add_module(&mut self, parent: ModuleId, name: Sym, vis: VisKind, span: Span) -> ModuleId {
        let mut path = self.modules[parent.0 as usize].path.clone();
        path.push(name);
        let no_prelude = self.modules[parent.0 as usize].no_prelude;
        let id = ModuleId(self.modules.len() as u32);
        self.modules.push(ModuleInfo { parent: Some(parent), name, path, vis, span, no_prelude });
        self.maps.push(Default::default());
        self.module_defs.push(DefId::PLACEHOLDER);
        id
    }

    /// The module at a name path from the crate root, if it exists.
    pub fn module_by_path(&self, path: &[Sym]) -> Option<ModuleId> {
        self.modules.iter().position(|m| m.path == path).map(|i| ModuleId(i as u32))
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
    /// a binding with visibility `vis` defined in `def_module`?
    pub fn visible(&self, vis: &VisKind, def_module: ModuleId, from: ModuleId, interner: &Interner) -> bool {
        match vis {
            VisKind::Pub | VisKind::Crate => true,
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
        self.module_by_path(&base_path)
    }

    /// Inserts a binding, applying the priority rules. Returns `Changed`
    /// when the table now answers differently, `Dup` when two same-rank
    /// explicit sources name different targets (a user error the caller
    /// reports after the fixpoint).
    pub fn insert(&mut self, module: ModuleId, ns: Namespace, name: Sym, bind: Bind) -> InsertOut {
        let map = &mut self.maps[module.0 as usize][ns_index(ns)];
        match map.get(&name) {
            None => {
                map.insert(name, BindState::One(bind));
                InsertOut::Changed
            }
            Some(BindState::One(old)) => {
                if old.target == bind.target {
                    InsertOut::Same
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

    /// One name's binding, without prelude or flat-name fallback. This is
    /// the raw table read; `Program::binding` layers the fallbacks.
    pub fn lookup(&self, module: ModuleId, ns: Namespace, name: Sym) -> Option<&BindState> {
        self.maps.get(module.0 as usize).and_then(|m| m[ns_index(ns)].get(&name))
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
    /// `use` paths (2018 uniform paths): the enclosing module chain,
    /// then the extern prelude.
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
    /// The extern prelude index of a crate name, if it is one.
    pub fn extern_by_name(&self, name: &str) -> Option<u32> {
        self.externs.iter().position(|e| e.name == name).map(|i| i as u32)
    }

    /// Looks up one first segment and checks visibility from `from`.
    /// Checks the module chain for `use` paths, the one module for
    /// lexical paths, then the extern prelude, then the std prelude.
    fn first_segment(&self, from: ModuleId, name: Sym, ns: Namespace, mode: PathMode, interner: &Interner) -> PathRes {
        let mut mods: Vec<ModuleId> = vec![from];
        if mode == PathMode::Use {
            let mut cur = self.modules[from.0 as usize].parent;
            while let Some(m) = cur {
                mods.push(m);
                cur = self.modules[m.0 as usize].parent;
            }
        }
        for m in mods {
            match self.lookup(m, ns, name) {
                Some(BindState::One(b)) => {
                    return if self.visible(&b.vis, b.def_module, from, interner) { PathRes::Done(b.target) } else { PathRes::Private };
                }
                Some(BindState::Ambiguous) => return PathRes::Ambiguous,
                None => {}
            }
        }
        let name_str = interner.get(name);
        if let Some(i) = self.extern_by_name(name_str) {
            return PathRes::Done(Target::Extern(i));
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
        if leading_colon {
            // `::dep::...`: extern prelude only.
            match self.extern_by_name(interner.get(segs[0])) {
                Some(i) => cur = Target::Extern(i),
                None => return PathRes::Absent,
            }
            idx = 1;
        } else if segs[0] == crate_sym {
            cur = Target::Module(crate::ty::defs::ROOT_MODULE);
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
            ImportKind::Single { path, .. } | ImportKind::Glob { path } => {
                path.iter().map(|s| interner.get(*s)).collect::<Vec<_>>().join("::")
            }
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

/// Tries one import against the current tables.
fn try_import(tables: &mut ResolvedTables, imp: &Import, self_sym: Sym, interner: &Interner, diags: &mut Vec<Diag>) -> TryOut {
    match &imp.kind {
        ImportKind::Glob { path } => {
            match tables.resolve_path(imp.module, path, Namespace::Type, PathMode::Use, imp.leading_colon, interner) {
                // `use a::E::*` imports the enum's variants.
                PathRes::Done(Target::Def(adt)) if tables.variants.contains_key(&adt) => {
                    let mut changed = false;
                    for v in tables.variants[&adt].clone() {
                        let bind = Bind { target: Target::Variant(adt, v), vis: imp.vis.clone(), rank: 1, def_module: imp.module };
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
                                    entries.push((
                                        ns,
                                        *name,
                                        Bind { target: b.target, vis: imp.vis.clone(), rank: 1, def_module: imp.module },
                                    ));
                                }
                            }
                        }
                        for (ns, name, bind) in entries {
                            if tables.insert(imp.module, ns, name, bind) == InsertOut::Changed {
                                changed = true;
                            }
                        }
                        // A glob stays live: new names in the source module can
                        // appear as other imports settle. It stays pending until
                        // a no-change sweep; the caller drops a resolved glob
                        // without error at the end.
                        TryOut::Stay { changed, resolved: true }
                    }
                    PathRes::Done(Target::Extern(_)) => TryOut::Done(false),
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
                let out = tables.insert(
                    imp.module,
                    Namespace::Value,
                    *name,
                    Bind { target: Target::Variant(adt, path[rest]), vis: imp.vis.clone(), rank: 2, def_module: imp.module },
                );
                report_dup(out, imp, *name, interner, diags);
                return TryOut::Done(out == InsertOut::Changed);
            }
            let (mod_path, last) = path.split_at(path.len() - 1);
            let last = last[0];
            if last == self_sym {
                // `use a::b::{self}`: bind the module itself. The binding
                // name is the segment before `self`, or the rename (the
                // parser keeps an `as` name in `name`).
                return match tables.resolve_module_path(imp.module, mod_path, imp.leading_colon, interner) {
                    PathRes::Done(target) => {
                        let bind_name = if *name == self_sym { mod_path.last().copied().unwrap_or(*name) } else { *name };
                        let out = tables.insert(
                            imp.module,
                            Namespace::Type,
                            bind_name,
                            Bind { target, vis: imp.vis.clone(), rank: 2, def_module: imp.module },
                        );
                        report_dup(out, imp, *name, interner, diags);
                        TryOut::Done(out == InsertOut::Changed)
                    }
                    PathRes::Private => {
                        diags.push(private_diag("that module", imp.span));
                        TryOut::Done(false)
                    }
                    _ => TryOut::Wait,
                };
            }
            match tables.resolve_module_path(imp.module, mod_path, imp.leading_colon, interner) {
                PathRes::Done(Target::Module(src)) => {
                    // Bind the name in every namespace that has it.
                    let mut any = false;
                    let mut changed = false;
                    let mut saw_private = false;
                    let mut found: Vec<(Namespace, Bind)> = Vec::new();
                    for ns in [Namespace::Type, Namespace::Value, Namespace::Macro] {
                        match tables.lookup(src, ns, last) {
                            Some(BindState::One(b)) => {
                                if tables.visible(&b.vis, b.def_module, imp.module, interner) {
                                    any = true;
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
                            None => {}
                        }
                    }
                    if !any {
                        if saw_private {
                            diags.push(private_diag(interner.get(last), imp.span));
                            return TryOut::Done(false);
                        }
                        return TryOut::Wait;
                    }
                    for (ns, bind) in found {
                        let out = tables.insert(imp.module, ns, *name, bind);
                        report_dup(out, imp, *name, interner, diags);
                        changed |= out == InsertOut::Changed;
                    }
                    TryOut::Done(changed)
                }
                PathRes::Done(Target::Extern(i)) => {
                    // `use dep::Name`: no cross-crate item table exists
                    // yet. The only answer that keeps rule zero is to
                    // bind nothing and let the path stay written: a
                    // `std` path goes through std compat, a real dep
                    // item path rejects at its use site (L0505 from the
                    // rewrite pass). A bare renamed import with no use
                    // is accepted by rustc, so no error here.
                    let _ = i;
                    TryOut::Done(false)
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

/// Reports a duplicate explicit import (two sources, one binding name).
fn report_dup(out: InsertOut, imp: &Import, name: Sym, interner: &Interner, diags: &mut Vec<Diag>) {
    if out == InsertOut::Dup {
        diags.push(Diag::new(
            "L0106",
            imp.span,
            format!("`{}` is defined more than once", interner.get(name)),
            "Rename one of the imports with `as`, or remove one.",
        ));
    }
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

/// The L0507 diagnostic for a use of a glob-ambiguous name.
pub fn ambiguous_diag(name: &str, span: Span) -> Diag {
    Diag::new(
        "L0507",
        span,
        format!("`{name}` is ambiguous: two glob imports bring different items with this name"),
        "Import the one you mean explicitly: an explicit import wins over globs.",
    )
}
