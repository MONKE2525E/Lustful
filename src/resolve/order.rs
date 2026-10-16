// The glob order rule (a lust subset rule, L0509).
//
// rustc resolves glob imports in its own event order, and some answers
// depend on that order: which visibility a name keeps when two globs
// bring the same item with different visibility, and which item and
// visibility an ambiguity carries on to the next glob importer. lust does
// not copy rustc's order. After the import fixpoint, this pass computes
// for each glob-bound name every binding rustc could end with in some
// order (`OrderSet`). A read whose answer is not the same for all of them
// is rejected (`ResolvedTables::order_dependent`). The program may be
// valid Rust, but lust cannot be sure of rustc's answer there, and a
// reject is always safe. An explicit import of the name fixes it.
use super::imports::{AmbEntry, AmbItem, BindState, Import, ImportKind, PathMode, PathRes, ResolvedTables, Target, VisKind, ns_index};
use crate::diag::{Diag, Span};
use crate::driver::graph::Namespace;
use crate::intern::{FxMap, Interner, Sym};
use crate::ty::defs::ModuleId;

/// The bindings rustc may end with for one glob-bound name, each in some
/// event order: visibility, the module that defines privacy for it, and
/// the item (`AmbItem::Amb` for an ambiguity). `absent` says the name may
/// also end with no binding. Only names with more than one possible
/// answer are stored (`ResolvedTables::order_dep`).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct OrderSet {
    pub entries: Vec<AmbEntry>,
    pub absent: bool,
}

const NAMESPACES: [Namespace; 3] = [Namespace::Type, Namespace::Value, Namespace::Macro];

type Key = (ModuleId, u8, Sym);

/// The glob imports of the crate session after the fixpoint, as the
/// order pass reads them.
struct Globs<'a> {
    /// Importing module -> (source module, glob import).
    from: FxMap<ModuleId, Vec<(ModuleId, &'a Import)>>,
    /// Source module -> the modules that glob it.
    importers: FxMap<ModuleId, Vec<ModuleId>>,
    /// Names a glob of an enum binds, with what each brings: their
    /// answer never depends on order.
    fixed: FxMap<Key, Vec<AmbEntry>>,
}

impl ResolvedTables {
    /// True when a read of `name` in `module` from module `from` has an
    /// answer that depends on rustc's glob order (`order_dep`): `from`
    /// sees some possible binding, and the possible bindings differ in
    /// item, in whether `from` sees them, or the name may be ambiguous or
    /// absent. When `from` sees none of them, every order gives a
    /// private or unresolved name, which the plain lookup reports.
    pub fn order_dependent(&self, module: ModuleId, ns: Namespace, name: Sym, from: ModuleId, interner: &Interner) -> bool {
        if self.order_dep.is_empty() {
            return false;
        }
        let Some(set) = self.order_dep.get(&(module, ns_index(ns) as u8, name)) else { return false };
        let seen = set.entries.iter().filter(|(v, m, _)| self.visible(v, *m, from, interner)).count();
        seen > 0
            && (set.absent
                || seen < set.entries.len()
                || set.entries.iter().any(|(_, _, item)| matches!(item, AmbItem::Amb { .. }) || *item != set.entries[0].2))
    }

    /// True when a non-private single import `imp` of `name` from `src`
    /// passes the re-export rule (rustc E0364) for some possible binding
    /// and fails it for another.
    fn order_reexport_mixed(&self, imp: &Import, src: ModuleId, ns: Namespace, name: Sym, interner: &Interner) -> bool {
        if imp.vis == VisKind::Priv || ns == Namespace::Macro {
            return false;
        }
        let Some(set) = self.order_dep.get(&(src, ns_index(ns) as u8, name)) else { return false };
        let mut within = [false, false];
        for (v, m, item) in &set.entries {
            if matches!(item, AmbItem::Item(Target::Extern(_))) || !self.visible(v, *m, imp.module, interner) {
                continue;
            }
            within[self.vis_within(&imp.vis, imp.module, v, *m, interner) as usize] = true;
        }
        within[0] && within[1]
    }

    /// True when two visibilities reach the same set of modules.
    fn same_vis(&self, a: &VisKind, am: ModuleId, b: &VisKind, bm: ModuleId, interner: &Interner) -> bool {
        let (ra, ma) = self.vis_region(a, am, interner);
        let (rb, mb) = self.vis_region(b, bm, interner);
        ra == rb && ma == mb && (ra != 1 || self.root_of(am) == self.root_of(bm))
    }
}

/// Fills `tables.order_dep` from the final import tables. Seeds are the
/// names of every module with two or more glob sources and the glob
/// importers of every ambiguous name; a changed set re-runs its glob
/// importers. Sets only grow, so the loop ends.
pub fn compute_order_dep(tables: &mut ResolvedTables, imports: &[Import], interner: &Interner) {
    tables.order_dep.clear();
    let globs = collect_globs(tables, imports, interner);
    let mut work: Vec<Key> = globs.fixed.keys().copied().collect();
    let fixed_mods: FxMap<ModuleId, ()> = globs.fixed.keys().map(|k| (k.0, ())).collect();
    for (&m, list) in &globs.from {
        if list.len() + usize::from(fixed_mods.contains_key(&m)) < 2 {
            continue;
        }
        for &(src, _) in list {
            for nsi in 0..3u8 {
                work.extend(tables.maps[src.0 as usize][nsi as usize].keys().map(|&name| (m, nsi, name)));
            }
            let range = (src, 0, Sym(0))..=(src, u8::MAX, Sym(u32::MAX));
            work.extend(tables.std_aliases.range(range).map(|(&(_, nsi, name), _)| (m, nsi, name)));
        }
    }
    for (src, maps) in tables.maps.iter().enumerate() {
        let Some(list) = globs.importers.get(&ModuleId(src as u32)) else { continue };
        for (nsi, map) in maps.iter().enumerate() {
            for (&name, state) in map {
                if matches!(state, BindState::Ambiguous) {
                    work.extend(list.iter().map(|&m| (m, nsi as u8, name)));
                }
            }
        }
    }
    work.sort_unstable_by_key(|&(m, nsi, name)| (m.0, nsi, name.0));
    work.dedup();
    work.reverse();
    while let Some(key) = work.pop() {
        let Some(set) = key_set(tables, &globs, key, interner) else { continue };
        if set.entries.len() == 1 && !set.absent {
            continue;
        }
        if tables.order_dep.get(&key) == Some(&set) {
            continue;
        }
        tables.order_dep.insert(key, set);
        if let Some(list) = globs.importers.get(&key.0) {
            work.extend(list.iter().map(|&m| (m, key.1, key.2)));
        }
    }
}

/// Resolves every glob import again against the final tables.
fn collect_globs<'a>(tables: &ResolvedTables, imports: &'a [Import], interner: &Interner) -> Globs<'a> {
    let mut g = Globs { from: FxMap::default(), importers: FxMap::default(), fixed: FxMap::default() };
    let value = ns_index(Namespace::Value) as u8;
    for imp in imports {
        let ImportKind::Glob { path } = &imp.kind else { continue };
        if path.is_empty() {
            continue;
        }
        match tables.resolve_path(imp.module, path, Namespace::Type, PathMode::Use, imp.leading_colon, interner) {
            PathRes::Done(Target::Def(adt)) if tables.variants.contains_key(&adt) => {
                let (vis, dm) = match tables.def_info.get(&adt) {
                    Some(info) => tables.glob_vis(imp, &info.vis, info.module, interner),
                    None => (imp.vis.clone(), imp.module),
                };
                for &v in &tables.variants[&adt] {
                    g.fixed.entry((imp.module, value, v)).or_default().push((vis.clone(), dm, AmbItem::Item(Target::Variant(adt, v))));
                }
            }
            _ => match tables.resolve_module_path(imp.module, path, imp.leading_colon, interner) {
                PathRes::Done(Target::Module(src)) if src != imp.module => {
                    g.from.entry(imp.module).or_default().push((src, imp));
                    let list = g.importers.entry(src).or_default();
                    if !list.contains(&imp.module) {
                        list.push(imp.module);
                    }
                }
                PathRes::Done(Target::Extern(i)) if tables.externs[i as usize].is_std_lib => {
                    let strs: Vec<&str> = path.iter().map(|s| interner.get(*s)).collect();
                    for v in crate::ty::lang::std_enum_variants(&strs) {
                        let name = interner.intern(v);
                        let mut full = path.clone();
                        full.push(name);
                        g.fixed.entry((imp.module, value, name)).or_default().push((imp.vis.clone(), imp.module, AmbItem::Std(full)));
                    }
                }
                _ => {}
            },
        }
    }
    g
}

/// What a glob of `src` can bring for one name: the stored order set,
/// or the source's one binding (an ambiguity brings each of its
/// clashing bindings' visibility, as `AmbItem::Amb`). None when `src`
/// has no binding of the name a glob copies.
fn source_set(tables: &ResolvedTables, src: ModuleId, nsi: u8, name: Sym) -> Option<OrderSet> {
    let key = (src, nsi, name);
    let ns = NAMESPACES[nsi as usize];
    let mut set = tables.order_dep.get(&key).cloned().unwrap_or_default();
    match tables.lookup(src, ns, name) {
        Some(BindState::One(b)) => {
            if ns == Namespace::Macro && tables.is_textual_bind(src, name, b) {
                return None;
            }
            if set.entries.is_empty() {
                set.entries.push((b.vis.clone(), b.def_module, AmbItem::Item(b.target)));
            }
        }
        Some(BindState::Ambiguous) => {
            let amb = AmbItem::Amb { certain: false };
            match tables.ambig_vis.get(&key) {
                Some(list) if !list.is_empty() => {
                    for (v, m, _) in list {
                        let e = (v.clone(), *m, amb.clone());
                        if !set.entries.contains(&e) {
                            set.entries.push(e);
                        }
                    }
                }
                _ => set.entries.push((VisKind::Pub, src, amb)),
            }
        }
        None => {
            let (vis, path) = tables.std_aliases.get(&key)?;
            if set.entries.is_empty() {
                set.entries.push((vis.clone(), tables.std_alias_def_module(key), AmbItem::Std(path.clone())));
            }
        }
    }
    Some(set)
}

/// The order set of one name in one module from its globs, or None when
/// an explicit binding (a local item or a single import) holds the name
/// or no glob brings it.
fn key_set(tables: &ResolvedTables, globs: &Globs, key: Key, interner: &Interner) -> Option<OrderSet> {
    let (m, nsi, name) = key;
    if matches!(tables.lookup(m, NAMESPACES[nsi as usize], name), Some(BindState::One(b)) if b.rank >= 2)
        || (tables.std_aliases.contains_key(&key) && !tables.std_glob_aliases.contains_key(&key))
    {
        return None;
    }
    let mut set = OrderSet { entries: Vec::new(), absent: true };
    if let Some(list) = globs.fixed.get(&key) {
        set.entries = list.clone();
        set.absent = false;
    }
    for &(src, imp) in globs.from.get(&m).map(Vec::as_slice).unwrap_or(&[]) {
        let Some(from) = source_set(tables, src, nsi, name) else { continue };
        let mut maybe_absent = from.absent;
        for (v, dm, item) in from.entries {
            if !tables.visible(&v, dm, m, interner) {
                maybe_absent = true;
                continue;
            }
            let (v, dm) = tables.glob_vis(imp, &v, dm, interner);
            if !set.entries.iter().any(|(ev, em, eitem)| *eitem == item && tables.same_vis(ev, *em, &v, dm, interner)) {
                set.entries.push((v, dm, item));
            }
        }
        set.absent &= maybe_absent;
    }
    (!set.entries.is_empty()).then_some(set)
}

/// L0509 for each module-level import whose path reads a glob name with
/// an order-dependent answer (`order_dependent`), or whose re-export
/// check passes for one possible binding and fails for another. One
/// diagnostic per import; returns the spans reported.
pub fn report_order_imports(tables: &ResolvedTables, imports: &[Import], interner: &Interner, diags: &mut Vec<Diag>) -> Vec<Span> {
    let mut seen: Vec<Span> = Vec::new();
    if tables.order_dep.is_empty() {
        return seen;
    }
    for imp in imports {
        let (mod_path, last) = match &imp.kind {
            ImportKind::Single { path, .. } => match path.split_last() {
                Some((&last, rest)) => (rest, Some(last)),
                None => continue,
            },
            ImportKind::Glob { path } | ImportKind::CheckPath { path } => (path.as_slice(), None),
            ImportKind::BadLeading { .. } => continue,
        };
        if mod_path.is_empty() || seen.contains(&imp.span) {
            continue;
        }
        let src = match tables.resolve_module_path(imp.module, mod_path, imp.leading_colon, interner) {
            PathRes::OrderDep => {
                let text: Vec<&str> = mod_path.iter().map(|s| interner.get(*s)).collect();
                seen.push(imp.span);
                diags.push(order_diag(&text.join("::"), imp.span));
                continue;
            }
            PathRes::Done(Target::Module(src)) => src,
            _ => continue,
        };
        let Some(last) = last else { continue };
        let hit = NAMESPACES.iter().any(|&ns| {
            tables.order_dependent(src, ns, last, imp.module, interner) || tables.order_reexport_mixed(imp, src, ns, last, interner)
        });
        if hit {
            seen.push(imp.span);
            diags.push(order_diag(interner.get(last), imp.span));
        }
    }
    seen
}

/// The L0509 diagnostic for path `what`: it reads a name that glob
/// imports bring with an answer that depends on rustc's import order.
pub fn order_diag(what: &str, span: Span) -> Diag {
    Diag::new(
        "L0509",
        span,
        format!(
            "`{what}` reads a glob-imported name whose binding depends on rustc's import order; lust rejects this on purpose (a lust subset rule)"
        ),
        "Import the item explicitly from the module that defines it (`use crate::module::Name;`): an explicit import wins over globs.",
    )
}
