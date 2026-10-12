// The outline worklist driver (docs/ARCH.md section 6.1): per crate, cfg
// stripping, module loading, import resolution, and macro expansion are
// one loop, not separate phases. W-RESOLVE owns the loop and the cfg,
// module, and import steps; W-MACRO owns expansion behind the `Expander`
// interface. Until `src/expand` lands, the loop runs with expansion
// disabled (`NoExpand`): item-position macro calls still reject in the
// parser, so no expansion work item can exist yet.
//
// Output shape: one merged Ast for collect. Defs outside the root module
// carry module-mangled flat names (`a$b$name`, never a legal Rust
// identifier), and every path the resolver can prove is rewritten to the
// flat name (one segment, or two for `Type::assoc`), so collect and
// check keep their flat tables while the binding tables here hold the
// real module semantics. DefIds are computed with the same formulas
// collect uses on the flat names, so slot keys and def ids agree by
// construction (the mangled name carries the module path in the hash).
use super::cfg::{self, CfgEnv};
use super::imports::*;
use super::modules;
use crate::ast::*;
use crate::def::{self, CrateIds, DefId, DefPathHash};
use crate::diag::{Diag, FileId, SourceMap, Span};
use crate::driver::graph::Namespace;
use crate::intern::{FxMap, Interner, Known, Sym};
use crate::ty::defs::{ModuleId, ROOT_MODULE};
use crate::{lexer, parser, scan};
use std::path::PathBuf;

/// The expansion step of the worklist (section 6.1 step 4). W-MACRO
/// provides the real implementation behind this frozen shape:
/// `expand` returns true when it changed items, and the loop runs
/// another sweep. The resolver records the bindings each expansion used
/// through the tables it passes (the time-travel checks live there).
pub trait Expander {
    /// Expands every resolvable macro call in the crate's module items.
    /// Disabled expansion returns false.
    fn expand(&self, tables: &ResolvedTables) -> bool;
}

/// Expansion disabled: the worklist runs for macro-free crates until
/// W-MACRO lands `expand`.
pub struct NoExpand;
impl Expander for NoExpand {
    fn expand(&self, _tables: &ResolvedTables) -> bool {
        false
    }
}

/// One crate to resolve: its root file and text (with any std splice
/// already appended by the driver), its cfg environment, its stable
/// identity, and its extern prelude from the Cargo graph.
pub struct CrateInput {
    pub root_path: PathBuf,
    pub root_text: String,
    pub env: CfgEnv,
    pub crate_ids: CrateIds,
    pub crate_name: String,
    /// (extern name, package id string, lib root file) per dependency.
    pub externs: Vec<(String, String, PathBuf)>,
}

/// The resolved crate the driver compiles: the merged Ast, the source
/// map with every file's text, the binding tables, and per-fn panic
/// lines and body hashes in flattened order.
pub struct ResolvedCrate {
    pub ast: Ast,
    pub map: SourceMap,
    pub tables: ResolvedTables,
    pub fn_lines: Vec<u32>,
    pub body_hashes: Vec<u64>,
    /// Every file's text concatenated, for the diagnostic source hash.
    pub all_text: String,
    /// True when some file of the crate can mention a source std fn.
    /// The driver owns std splicing: when it did not splice and this is
    /// set, it splices and resolves once more.
    pub needs_std: bool,
}

/// A failed resolution: the source map and combined text for rendering,
/// plus the diagnostics (whose spans may name any discovered file).
pub struct ResolveError {
    pub map: SourceMap,
    pub all_text: String,
    pub needs_std: bool,
    pub diags: Vec<Diag>,
}

/// True when a crate root file needs the resolver: any `mod`, `use`,
/// `const`/`static`/`type` item keyword, `#[cfg`, `#[path`, or
/// `macro_rules` in its token stream. Token-exact (strings and comments
/// never count); a `use` of `std` alone also routes here, which costs a
/// full rebuild but keeps one code path for imports and cfg.
pub fn needs_resolve(root_text: &str, interner: &Interner) -> bool {
    let Ok(lexed) = lexer::lex(root_text, FileId(0), 0, interner) else { return false };
    needs_resolve_lexed(&lexed, interner)
}

/// The lexed form of `needs_resolve`, for callers that already lexed.
pub fn needs_resolve_lexed(lexed: &lexer::Lexed, interner: &Interner) -> bool {
    use crate::lexer::Tok;
    let toks = &lexed.tokens;
    for (i, t) in toks.iter().enumerate() {
        match t.tok {
            Tok::Mod | Tok::Use | Tok::Static | Tok::Extern | Tok::Crate | Tok::Super => return true,
            Tok::PathSep => {
                // A leading `::` (not a segment join): the token before
                // it is not a path segment end.
                let prev = if i == 0 { None } else { Some(toks[i - 1].tok) };
                if !matches!(
                    prev,
                    Some(Tok::Ident(_)) | Some(Tok::SelfUpper) | Some(Tok::Gt) | Some(Tok::Crate) | Some(Tok::Super) | Some(Tok::SelfLower)
                ) {
                    return true;
                }
            }
            Tok::Const if matches!(toks.get(i + 1).map(|t| t.tok), Some(Tok::Ident(_)) | Some(Tok::Underscore)) => return true,
            Tok::Type => return true,
            Tok::Pound => {
                // `#[cfg`, `#[cfg_attr`, `#[path`, `#[macro_use`, inner forms too.
                let mut j = i + 1;
                if toks.get(j).map(|t| t.tok) == Some(Tok::Bang) {
                    j += 1;
                }
                if toks.get(j).map(|t| t.tok) == Some(Tok::LBracket)
                    && let Some(Tok::Ident(s)) = toks.get(j + 1).map(|t| t.tok)
                    && matches!(interner.get(s), "cfg" | "cfg_attr" | "path" | "macro_use" | "macro_export" | "no_implicit_prelude")
                {
                    return true;
                }
            }
            Tok::Ident(s) if interner.get(s) == "macro_rules" => return true,
            _ => {}
        }
    }
    false
}

/// One file during resolution.
struct FileWork {
    path: PathBuf,
    text: String,
    file_id: FileId,
    ast: Ast,
    /// The module this file's top-level items belong to.
    module: ModuleId,
}

/// The key under which a module's item list is later found in the walks:
/// the file that holds it, plus the inline module name path inside it.
type ItemListKey = (usize, Vec<Sym>);

/// Builds a source map from discovered (path, text, file id) triples.
fn make_map(seen: &[(PathBuf, String, FileId)]) -> (SourceMap, String) {
    let mut map = SourceMap::default();
    let mut all = String::new();
    let mut sorted: Vec<&(PathBuf, String, FileId)> = seen.iter().collect();
    sorted.sort_by_key(|(_, _, f)| f.0);
    for (path, text, file_id) in sorted {
        while (map.file_count() as u32) < file_id.0 {
            map.add_file_with_text("", "");
        }
        if map.file_count() as u32 == file_id.0 {
            map.add_file_with_text(&path.to_string_lossy(), text);
        }
        all.push_str(text);
        all.push('\n');
    }
    (map, all)
}

/// Runs the outline worklist for one crate. See the file header.
pub fn resolve_crate(
    input: &CrateInput,
    interner: &Interner,
    known: &Known,
    expander: &dyn Expander,
) -> Result<ResolvedCrate, ResolveError> {
    let crate_sym = interner.intern(&input.crate_name);
    let mut tables = ResolvedTables::new(crate_sym);
    // The extern prelude: std, core, alloc, then the direct dependencies.
    for name in ["std", "core", "alloc"] {
        push_extern(&mut tables, input, name, true);
    }
    for (name, _, _) in &input.externs {
        if tables.extern_by_name(name).is_none() {
            push_extern(&mut tables, input, name, false);
        }
    }

    // ---- Discovery: lex, outline, and walk `mod` edges to the file set.
    // cfg on a `mod` declaration is evaluated here, before its file loads.
    let mut files: Vec<(PathBuf, String, ModuleId)> = Vec::new();
    let mut seen: Vec<(PathBuf, String, FileId)> = Vec::new();
    let mut needs_std = false;
    let mut diags: Vec<Diag> = Vec::new();
    let mut queue: Vec<(PathBuf, String, ModuleId, bool)> = vec![(input.root_path.clone(), input.root_text.clone(), ROOT_MODULE, true)];
    let mut text_by_path: FxMap<String, String> = FxMap::default();
    let mut file_ids: FxMap<String, FileId> = FxMap::default();
    let mut next_file = 0u32;
    while let Some((path, text, module, is_root)) = queue.pop() {
        let canon = modules::canonical_string(&path);
        let file_id = *file_ids.entry(format!("{}#{}", canon, module.0)).or_insert_with(|| {
            let id = FileId(next_file);
            next_file += 1;
            id
        });
        needs_std |= crate::ty::lang::needs_std_load(&text);
        if !seen.iter().any(|(_, _, f)| *f == file_id) {
            seen.push((path.clone(), text.clone(), file_id));
        }
        let lexed = match lexer::lex(&text, file_id, 0, interner) {
            Ok(l) => l,
            Err(d) => {
                diags.push(d);
                files.push((path, text, module));
                continue;
            }
        };
        let outline = scan::outline(&lexed, interner);
        // Inline module skeleton, keyed by name path from this file's module.
        let mut inline_modules: FxMap<Vec<Sym>, ModuleId> = FxMap::default();
        inline_modules.insert(Vec::new(), module);
        for decl in &outline.mods {
            let enabled = match cfg::outline_enabled(&input.env, &decl.cfg, &lexed.strings, interner, decl.span) {
                Ok(e) => e,
                Err(d) => {
                    diags.push(d);
                    false
                }
            };
            if !enabled {
                continue;
            }
            let parent = inline_modules.get(&decl.container).copied().unwrap_or(module);
            let vis = match decl.vis {
                scan::OutlineVis::Private => VisKind::Priv,
                scan::OutlineVis::Pub => VisKind::Pub,
                // The restricted path itself is re-read from the AST at
                // registration; the outline only needs the module node.
                scan::OutlineVis::Restricted => VisKind::Crate,
            };
            let child = tables.add_module(parent, decl.name, vis, decl.span);
            if decl.inline {
                let mut key = decl.container.clone();
                key.push(decl.name);
                inline_modules.insert(key, child);
            } else {
                let inline_names: Vec<String> = decl.container.iter().map(|s| interner.get(*s).to_string()).collect();
                match modules::module_file(&path, is_root, &inline_names, interner.get(decl.name), decl.path_attr.as_deref(), decl.span) {
                    Ok(f) => {
                        let fcanon = modules::canonical_string(&f);
                        let ftext = match text_by_path.get(&fcanon) {
                            Some(t) => t.clone(),
                            None => match std::fs::read_to_string(&f) {
                                Ok(t) => {
                                    text_by_path.insert(fcanon, t.clone());
                                    t
                                }
                                Err(e) => {
                                    diags.push(Diag::new(
                                        "L0503",
                                        decl.span,
                                        format!("cannot read module file {}: {e}", f.display()),
                                        "Check the file exists and is readable.",
                                    ));
                                    continue;
                                }
                            },
                        };
                        queue.push((f, ftext, child, false));
                    }
                    Err(d) => diags.push(d),
                }
            }
        }
        // Textual macro names from this file (the parser has no
        // macro_rules items yet): bind them in the macro namespace of
        // their module now, exported ones also at the crate root.
        for m in &outline.macros {
            let hash = macro_hash(input, interner, module, &tables, m.name);
            let def = DefId { krate: input.crate_ids.local, hash };
            tables.insert(
                module,
                Namespace::Macro,
                m.name,
                Bind { target: Target::Def(def), vis: VisKind::Priv, rank: 2, def_module: module },
            );
            if m.exported {
                tables.insert(
                    ROOT_MODULE,
                    Namespace::Macro,
                    m.name,
                    Bind { target: Target::Def(def), vis: VisKind::Pub, rank: 2, def_module: ROOT_MODULE },
                );
            }
            tables.def_info.insert(def, DefInfo { kind: ResKind::Macro, flat: m.name, module, vis: VisKind::Priv });
            tables.flat[ns_index(Namespace::Macro)].insert(m.name, def);
        }
        files.push((path, text, module));
    }
    if !diags.is_empty() {
        let (map, all_text) = make_map(&seen);
        return Err(ResolveError { map, all_text, needs_std, diags });
    }
    // The source map, in FileId order, with every file's text.
    files.sort_by_key(|(p, _, m)| file_ids[&format!("{}#{}", modules::canonical_string(p), m.0)].0);
    let (map, all_text) = make_map(&seen);
    let mut works: Vec<FileWork> = Vec::new();
    for (path, text, module) in files {
        let canon = modules::canonical_string(&path);
        let file_id = file_ids[&format!("{canon}#{}", module.0)];
        let lexed = match lexer::lex(&text, file_id, 0, interner) {
            Ok(l) => l,
            Err(d) => return Err(ResolveError { map: map.clone(), all_text: all_text.clone(), needs_std, diags: vec![d] }),
        };
        let ast = match parser::parse(&lexed, interner, known) {
            Ok(a) => a,
            Err(d) => return Err(ResolveError { map: map.clone(), all_text: all_text.clone(), needs_std, diags: vec![d] }),
        };
        works.push(FileWork { path, text, file_id, ast, module });
    }
    // The module of every item list, by (file, inline path).
    let mut list_module: FxMap<ItemListKey, ModuleId> = FxMap::default();
    for (fi, w) in works.iter().enumerate() {
        list_module.insert((fi, Vec::new()), w.module);
    }
    let list_module = &mut list_module;
    for (fi, w) in works.iter().enumerate() {
        collect_inline_modules(&w.ast.items, fi, &[], &tables, list_module);
    }

    // ---- The worklist loop: strip, register, import, expand.
    // Registration is idempotent (same target inserts are Same), so the
    // loop can re-run it after an expansion changed items. With
    // expansion disabled, round two confirms and stops.
    let mut inner_diags: Vec<Diag> = Vec::new();
    let mut imports: Vec<Import> = Vec::new();
    let mut stripped = vec![false; works.len()];
    let mut registered = vec![false; works.len()];
    for round in 0..4 {
        for (fi, w) in works.iter_mut().enumerate() {
            if !stripped[fi] {
                strip_file(w, fi, input, interner, list_module, &mut tables, &mut inner_diags);
                stripped[fi] = true;
            }
            // Registration renames defs, so it must run once per file
            // even when the loop sweeps again after an expansion.
            if !registered[fi] {
                register_items(&mut w.ast.items, w.module, fi, &[], input, interner, &mut tables, list_module, &mut imports);
                registered[fi] = true;
            }
        }
        match run_imports(&mut tables, &imports, interner) {
            Ok(ds) => inner_diags.extend(ds),
            Err(e) => {
                inner_diags.push(Diag::new("L0506", Span::default(), e, "This is a lust bug; report it."));
            }
        }
        imports.clear();
        if !expander.expand(&tables) || round == 3 {
            break;
        }
    }
    if !inner_diags.is_empty() {
        return Err(ResolveError { map: map.clone(), all_text: all_text.clone(), needs_std, diags: inner_diags });
    }
    // Associated fn visibility, keyed by the self type's def now that
    // imports have settled (an impl may name an imported type).
    for w in works.iter() {
        collect_assoc_vis(&w.ast, &w.ast.items, w.module, interner, &mut tables);
    }

    // ---- Rewrite paths to flat names, checking visibility.
    let mut rw = Rewrite { tables: &tables, interner, list_module, diags: Vec::new() };
    for (fi, w) in works.iter_mut().enumerate() {
        let module = w.module;
        rw.file_items(&mut w.ast, fi, module, &[]);
    }
    if !rw.diags.is_empty() {
        return Err(ResolveError { map: map.clone(), all_text: all_text.clone(), needs_std, diags: rw.diags });
    }

    // ---- Flatten: inline module bodies splice into top-level items;
    // mod, use, and extern crate items drop.
    let mut fn_module_map: FxMap<Sym, ModuleId> = FxMap::default();
    for info in tables.def_info.values() {
        if info.kind == ResKind::Fn {
            fn_module_map.insert(info.flat, info.module);
        }
    }
    let mut chunks = Vec::new();
    for mut w in works {
        let mut flat_items = Vec::new();
        flatten_items(std::mem::take(&mut w.ast.items), &mut flat_items);
        w.ast.items = flat_items;
        chunks.push(w.ast);
    }
    let ast = Ast::concat(chunks);
    // Per-fn lines and body hashes, in the flattened order collect uses.
    let mut fn_lines = Vec::new();
    let mut body_hashes = Vec::new();
    let mut fn_module = Vec::new();
    for item in &ast.items {
        let mut push = |def: &FnDef| {
            fn_lines.push(map.line_col(def.name_span).0);
            let text = map.text(def.name_span.file).unwrap_or("");
            let body_span = def.body.map(|b| ast.block(b).span).unwrap_or(def.name_span);
            let slice = text.get(body_span.lo as usize..body_span.hi as usize).unwrap_or("");
            body_hashes.push(hash_str(slice));
            fn_module.push(fn_module_map.get(&def.name).copied().unwrap_or(ROOT_MODULE));
        };
        match &item.kind {
            ItemKind::Fn(d) => push(d),
            ItemKind::Impl(imp) => {
                for d in &imp.fns {
                    push(d);
                }
            }
            _ => {}
        }
    }
    tables.fn_module = fn_module;
    Ok(ResolvedCrate { ast, map, tables, fn_lines, body_hashes, all_text, needs_std })
}

/// Adds one extern crate to the prelude tables.
fn push_extern(tables: &mut ResolvedTables, input: &CrateInput, name: &str, is_std_lib: bool) {
    let hash = def::item_hash(crate::def::StableCrateHash(hash_str(name) | 1), &[], def::DefKind::Module, name, 0);
    tables.externs.push(ExternInfo { name: name.to_string(), def: DefId { krate: input.crate_ids.local, hash }, is_std_lib });
}

/// A macro def's stable hash: module path segments plus the name
/// (section 1.7, the proper form; nothing else computes macro hashes).
fn macro_hash(input: &CrateInput, interner: &Interner, module: ModuleId, tables: &ResolvedTables, name: Sym) -> DefPathHash {
    let path: Vec<&str> = tables.modules[module.0 as usize].path.iter().map(|s| interner.get(*s)).collect();
    def::item_hash(input.crate_ids.stable, &path, def::DefKind::Macro, interner.get(name), 0)
}

/// FxHash of a string, for body hashes and extern ids.
fn hash_str(s: &str) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = crate::intern::FxHasher::default();
    s.hash(&mut h);
    h.finish() | 1
}

/// Records the module of each inline item list in one file's items.
fn collect_inline_modules(items: &[Item], fi: usize, prefix: &[Sym], tables: &ResolvedTables, out: &mut FxMap<ItemListKey, ModuleId>) {
    let parent_path: Vec<Sym> = out.get(&(fi, prefix.to_vec())).map(|m| tables.modules[m.0 as usize].path.clone()).unwrap_or_default();
    for item in items {
        if let ItemKind::Mod(m) = &item.kind {
            let mut key = prefix.to_vec();
            key.push(m.name);
            let mut full = parent_path.clone();
            full.push(m.name);
            if let Some(id) = tables.module_by_path(&full) {
                out.insert((fi, key.clone()), id);
                if let Some(body) = &m.body {
                    collect_inline_modules(body, fi, &key, tables, out);
                }
            }
        }
    }
}

/// True when an attribute list names `name` as its one-segment path.
fn has_attr(attrs: &[Attr], name: &str, interner: &Interner) -> bool {
    attrs.iter().any(|a| a.path.len() == 1 && interner.get(a.path[0].name) == name)
}

/// The `#[path = "..."]` value in an attribute list, when written. The
/// parser stores the `= lit` tail as raw token trees, or as an `Eq`
/// expression for the parenthesized form; both reduce to the string.
fn path_attr_value(attrs: &[Attr], ast: &Ast, interner: &Interner) -> Option<String> {
    for a in attrs {
        if a.path.len() != 1 || interner.get(a.path[0].name) != "path" {
            continue;
        }
        match &a.input {
            AttrInput::Eq(e) => {
                if let Expr::Str(i) = ast.expr(*e) {
                    return ast.strings.get(*i as usize).cloned();
                }
            }
            AttrInput::List(_, trees) => {
                for t in trees {
                    if let crate::lexer::TokenTree::Token(tok) = t
                        && let crate::lexer::Tok::Str(i) = tok.tok
                    {
                        return ast.strings.get(i as usize).cloned();
                    }
                }
            }
            AttrInput::None => {}
        }
    }
    None
}

/// Step 1 of the loop for one file: expand `cfg_attr`, strip cfg'd-out
/// items, fields, variants, and methods, and apply module inner
/// attribute flags (`no_implicit_prelude`, a crate-level cfg). Match
/// arm cfg is handled in the rewrite walk, where arms are visited.
fn strip_file(
    w: &mut FileWork,
    fi: usize,
    input: &CrateInput,
    interner: &Interner,
    list_module: &FxMap<ItemListKey, ModuleId>,
    tables: &mut ResolvedTables,
    diags: &mut Vec<Diag>,
) {
    // Inner attributes ride on the first item (parser behavior).
    let strings = w.ast.strings.clone();
    let inner: Vec<Attr> =
        w.ast.items.first().map(|i| i.attrs.iter().filter(|a| a.style == AttrStyle::Inner).cloned().collect()).unwrap_or_default();
    let module = w.module;
    if has_attr(&inner, "no_implicit_prelude", interner) {
        tables.modules[module.0 as usize].no_prelude = true;
    }
    match cfg::attrs_enabled(&input.env, &inner, &strings, interner) {
        Ok(false) => {
            // A crate- or module-level cfg turned the whole file off.
            w.ast.items.clear();
            return;
        }
        Ok(true) => {}
        Err(d) => diags.push(d),
    }
    let mut items = std::mem::take(&mut w.ast.items);
    strip_items(&mut items, fi, &[], w, input, interner, list_module, tables, diags);
    w.ast.items = items;
}

/// The recursive half of `strip_file` over one item list.
fn strip_items(
    items: &mut Vec<Item>,
    fi: usize,
    prefix: &[Sym],
    w: &FileWork,
    input: &CrateInput,
    interner: &Interner,
    list_module: &FxMap<ItemListKey, ModuleId>,
    tables: &mut ResolvedTables,
    diags: &mut Vec<Diag>,
) {
    let strings = &w.ast.strings;
    let mut keep = Vec::with_capacity(items.len());
    for mut item in items.drain(..) {
        if let Err(d) = cfg::expand_cfg_attr(&input.env, &mut item.attrs, strings, interner) {
            diags.push(d);
        }
        match cfg::attrs_enabled(&input.env, &item.attrs, strings, interner) {
            Ok(true) => {}
            Ok(false) => continue,
            Err(d) => {
                diags.push(d);
                continue;
            }
        }
        match &mut item.kind {
            ItemKind::Struct(s) => {
                if let VariantFields::Struct(fs) | VariantFields::Tuple(fs) = &mut s.fields {
                    strip_fields(fs, input, strings, interner, diags);
                }
            }
            ItemKind::Enum(e) => {
                e.variants.retain_mut(|v| {
                    if let Err(d) = cfg::expand_cfg_attr(&input.env, &mut v.attrs, strings, interner) {
                        diags.push(d);
                    }
                    match cfg::attrs_enabled(&input.env, &v.attrs, strings, interner) {
                        Ok(on) => {
                            if on && let VariantFields::Struct(fs) | VariantFields::Tuple(fs) = &mut v.fields {
                                strip_fields(fs, input, strings, interner, diags);
                            }
                            on
                        }
                        Err(d) => {
                            diags.push(d);
                            false
                        }
                    }
                });
            }
            ItemKind::Impl(imp) => {
                imp.fns.retain_mut(|f| {
                    if let Err(d) = cfg::expand_cfg_attr(&input.env, &mut f.attrs, strings, interner) {
                        diags.push(d);
                    }
                    matches!(cfg::attrs_enabled(&input.env, &f.attrs, strings, interner), Ok(true))
                });
            }
            ItemKind::Mod(m) => {
                // The module's real visibility comes from the AST (the
                // outline could not read a restricted path).
                let mut key = prefix.to_vec();
                key.push(m.name);
                if let Some(&child) = list_module.get(&(fi, key.clone())) {
                    let vis = vis_from_ast(&item.vis, interner);
                    tables.modules[child.0 as usize].vis = vis;
                    if has_attr(&item.attrs, "no_implicit_prelude", interner) {
                        tables.modules[child.0 as usize].no_prelude = true;
                    }
                    if let Some(body) = &mut m.body {
                        strip_items(body, fi, &key, w, input, interner, list_module, tables, diags);
                    }
                } else if m.body.is_some() {
                    // A cfg-stripped inline module (its own cfg ran in
                    // discovery): drop the whole item.
                    continue;
                }
            }
            _ => {}
        }
        keep.push(item);
    }
    *items = keep;
}

/// Strips cfg'd-out fields from one field list.
fn strip_fields(fs: &mut Vec<FieldDef>, input: &CrateInput, strings: &[String], interner: &Interner, diags: &mut Vec<Diag>) {
    fs.retain_mut(|f| {
        if let Err(d) = cfg::expand_cfg_attr(&input.env, &mut f.attrs, strings, interner) {
            diags.push(d);
        }
        match cfg::attrs_enabled(&input.env, &f.attrs, strings, interner) {
            Ok(on) => on,
            Err(d) => {
                diags.push(d);
                false
            }
        }
    });
}

/// The flat name of a def in a module: the plain name at the root, the
/// module path joined with `$` elsewhere.
fn flat_name(tables: &ResolvedTables, module: ModuleId, name: Sym, interner: &Interner) -> Sym {
    if module == ROOT_MODULE {
        return name;
    }
    let path = &tables.modules[module.0 as usize].path;
    let mut s = String::new();
    for seg in path {
        s.push_str(interner.get(*seg));
        s.push('$');
    }
    s.push_str(interner.get(name));
    interner.intern(&s)
}

/// Step 3 input: registers every defined name in one item list, renames
/// defs to their flat names, and collects the module's imports. Module
/// bindings register first (same sweep): a `mod` item's name is a
/// type-namespace binding to the child module.
#[allow(clippy::too_many_arguments)]
fn register_items(
    items: &mut [Item],
    module: ModuleId,
    fi: usize,
    prefix: &[Sym],
    input: &CrateInput,
    interner: &Interner,
    tables: &mut ResolvedTables,
    list_module: &FxMap<ItemListKey, ModuleId>,
    imports: &mut Vec<Import>,
) {
    // Adt disambiguators count same-flat-name Adts in one pass order,
    // matching collect (which counts by name over the whole crate).
    for item in items.iter_mut() {
        let vis = || vis_from_ast(&item.vis, interner);
        let bind = |tables: &mut ResolvedTables, ns: Namespace, name: Sym, target: Target, vis: VisKind| {
            tables.insert(module, ns, name, Bind { target, vis, rank: 2, def_module: module });
        };
        match &mut item.kind {
            ItemKind::Mod(m) => {
                let mut key = prefix.to_vec();
                key.push(m.name);
                if let Some(&child) = list_module.get(&(fi, key.clone())) {
                    tables.module_defs[child.0 as usize] = DefId {
                        krate: input.crate_ids.local,
                        hash: def::item_hash(
                            input.crate_ids.stable,
                            &[],
                            def::DefKind::Module,
                            interner.get(flat_name(tables, module, m.name, interner)),
                            0,
                        ),
                    };
                    bind(tables, Namespace::Type, m.name, Target::Module(child), vis());
                    if let Some(body) = &mut m.body {
                        register_items(body, child, fi, &key, input, interner, tables, list_module, imports);
                    }
                }
            }
            ItemKind::Fn(f) => {
                let flat = flat_name(tables, module, f.name, interner);
                let def = DefId { krate: input.crate_ids.local, hash: def::free_fn_hash(input.crate_ids.stable, &[], interner.get(flat)) };
                bind(tables, Namespace::Value, f.name, Target::Def(def), vis());
                tables.def_info.insert(def, DefInfo { kind: ResKind::Fn, flat, module, vis: vis() });
                tables.flat[ns_index(Namespace::Value)].insert(flat, def);
                f.name = flat;
            }
            ItemKind::Struct(s) => {
                let flat = flat_name(tables, module, s.name, interner);
                let disamb = tables.def_info.values().filter(|i| i.kind == ResKind::Adt && i.flat == flat).count() as u32;
                let def = DefId {
                    krate: input.crate_ids.local,
                    hash: def::item_hash(input.crate_ids.stable, &[], def::DefKind::Adt, interner.get(flat), disamb),
                };
                bind(tables, Namespace::Type, s.name, Target::Def(def), vis());
                bind(tables, Namespace::Value, s.name, Target::Def(def), vis());
                record_adt(tables, def, flat, module, vis(), &s.fields, interner);
                s.name = flat;
            }
            ItemKind::Enum(e) => {
                let flat = flat_name(tables, module, e.name, interner);
                let disamb = tables.def_info.values().filter(|i| i.kind == ResKind::Adt && i.flat == flat).count() as u32;
                let def = DefId {
                    krate: input.crate_ids.local,
                    hash: def::item_hash(input.crate_ids.stable, &[], def::DefKind::Adt, interner.get(flat), disamb),
                };
                bind(tables, Namespace::Type, e.name, Target::Def(def), vis());
                tables.def_info.insert(def, DefInfo { kind: ResKind::Adt, flat, module, vis: vis() });
                tables.variants.insert(def, e.variants.iter().map(|v| v.name).collect());
                tables.flat[ns_index(Namespace::Type)].insert(flat, def);
                for v in &e.variants {
                    if let VariantFields::Struct(fs) = &v.fields {
                        let entry = tables.field_vis.entry(def).or_insert_with(|| (module, FxMap::default()));
                        for f in fs {
                            entry.1.insert(f.name, vis_from_ast(&f.vis, interner));
                        }
                    }
                }
                e.name = flat;
            }
            ItemKind::Const(c) => {
                if let Some(name) = c.name {
                    let flat = flat_name(tables, module, name, interner);
                    let def = DefId {
                        krate: input.crate_ids.local,
                        hash: def::item_hash(input.crate_ids.stable, &[], def::DefKind::Const, interner.get(flat), 0),
                    };
                    bind(tables, Namespace::Value, name, Target::Def(def), vis());
                    tables.def_info.insert(def, DefInfo { kind: ResKind::Const, flat, module, vis: vis() });
                    tables.flat[ns_index(Namespace::Value)].insert(flat, def);
                    c.name = Some(flat);
                }
            }
            ItemKind::Static(s) => {
                let flat = flat_name(tables, module, s.name, interner);
                let def = DefId {
                    krate: input.crate_ids.local,
                    hash: def::item_hash(input.crate_ids.stable, &[], def::DefKind::Static, interner.get(flat), 0),
                };
                bind(tables, Namespace::Value, s.name, Target::Def(def), vis());
                tables.def_info.insert(def, DefInfo { kind: ResKind::Static, flat, module, vis: vis() });
                tables.flat[ns_index(Namespace::Value)].insert(flat, def);
                s.name = flat;
            }
            ItemKind::Type(a) => {
                let flat = flat_name(tables, module, a.name, interner);
                let def = DefId {
                    krate: input.crate_ids.local,
                    hash: def::item_hash(input.crate_ids.stable, &[], def::DefKind::TypeAlias, interner.get(flat), 0),
                };
                bind(tables, Namespace::Type, a.name, Target::Def(def), vis());
                tables.def_info.insert(def, DefInfo { kind: ResKind::Alias, flat, module, vis: vis() });
                tables.flat[ns_index(Namespace::Type)].insert(flat, def);
                a.name = flat;
            }
            ItemKind::Impl(imp) => {
                // Associated fn visibility, once the self type resolves
                // in this module. The rewrite pass resolves the path
                // properly; here a one-segment or resolvable path is
                // enough to key the table.
                let _ = imp;
            }
            ItemKind::Use(u) => {
                flatten_use(&u.tree, module, vis(), imports, interner);
            }
            ItemKind::ExternCrate(e) => {
                let bind_name = e.rename.unwrap_or(e.name);
                if bind_name != interner.intern("_") {
                    let target = if e.name == interner.intern("self") {
                        Some(Target::Module(ROOT_MODULE))
                    } else {
                        tables.extern_by_name(interner.get(e.name)).map(Target::Extern)
                    };
                    if let Some(target) = target {
                        bind(tables, Namespace::Type, bind_name, target, vis());
                    }
                }
            }
            _ => {}
        }
    }
}

/// Records one struct's def info and field visibility.
fn record_adt(
    tables: &mut ResolvedTables,
    def: DefId,
    flat: Sym,
    module: ModuleId,
    vis: VisKind,
    fields: &VariantFields,
    interner: &Interner,
) {
    tables.def_info.insert(def, DefInfo { kind: ResKind::Adt, flat, module, vis });
    tables.flat[ns_index(Namespace::Type)].insert(flat, def);
    tables.flat[ns_index(Namespace::Value)].insert(flat, def);
    if let VariantFields::Struct(fs) = fields {
        let mut map = FxMap::default();
        for f in fs {
            map.insert(f.name, vis_from_ast(&f.vis, interner));
        }
        tables.field_vis.insert(def, (module, map));
    }
}

/// Fills `assoc_vis` from every impl block whose self type resolves.
fn collect_assoc_vis(ast: &Ast, items: &[Item], module: ModuleId, interner: &Interner, tables: &mut ResolvedTables) {
    for item in items {
        match &item.kind {
            ItemKind::Impl(imp) => {
                if let TyExpr::Path(segs) = ast.ty(imp.self_ty) {
                    let names: Vec<Sym> = segs.iter().map(|s| s.name).collect();
                    if let PathRes::Done(Target::Def(def)) =
                        tables.resolve_path(module, &names, Namespace::Type, PathMode::Lexical, false, interner)
                    {
                        let entry = tables.assoc_vis.entry(def).or_default();
                        for f in &imp.fns {
                            entry.insert(f.name, (vis_from_ast(&f.vis, interner), module));
                        }
                    }
                }
            }
            ItemKind::Mod(m) => {
                if let Some(body) = &m.body {
                    // Inline bodies were registered under their module;
                    // the path lookup finds it by name path.
                    let mut full = tables.modules[module.0 as usize].path.clone();
                    full.push(m.name);
                    if let Some(child) = tables.module_by_path(&full) {
                        collect_assoc_vis(ast, body, child, interner, tables);
                    }
                }
            }
            _ => {}
        }
    }
}

// ---------- The rewrite pass ----------
//
// Every written path resolves here, in its module (plus lexical scopes
// in bodies). A proven path becomes its flat name; an ambiguous or
// private one is a diagnostic (L0507, L0510); an unproven one is left
// written, so collect and check report it with their own codes. A path
// into a non-std extern crate is L0505: cross-crate item resolution is
// not supported yet, and a false accept would be worse.

/// One lexical frame in a body walk.
#[derive(Default)]
struct Frame {
    locals: Vec<Sym>,
    /// Function-local imports: (name, namespace index) to target.
    imports: FxMap<(Sym, usize), LocalBind>,
}

#[derive(Clone, Copy)]
enum LocalBind {
    Target(Target),
    Ambiguous,
}

struct Rewrite<'a> {
    tables: &'a ResolvedTables,
    interner: &'a Interner,
    list_module: &'a FxMap<ItemListKey, ModuleId>,
    diags: Vec<Diag>,
}

impl Rewrite<'_> {
    /// Rewrites one file's top-level items (recursing into inline mods).
    fn file_items(&mut self, ast: &mut Ast, fi: usize, module: ModuleId, prefix: &[Sym]) {
        let mut items = std::mem::take(&mut ast.items);
        self.items(ast, &mut items, fi, module, prefix);
        ast.items = items;
    }

    fn items(&mut self, ast: &mut Ast, items: &mut Vec<Item>, fi: usize, module: ModuleId, prefix: &[Sym]) {
        for item in items.iter_mut() {
            match &mut item.kind {
                ItemKind::Fn(f) => {
                    let mut def = std::mem::replace(f, dummy_fn());
                    self.fn_def(ast, &mut def, module);
                    *f = def;
                }
                ItemKind::Struct(s) => {
                    let fields = match &mut s.fields {
                        VariantFields::Struct(fs) | VariantFields::Tuple(fs) => fs.iter_mut().map(|f| f.ty).collect::<Vec<_>>(),
                        VariantFields::Unit => Vec::new(),
                    };
                    for t in fields {
                        self.ty(ast, t, module);
                    }
                }
                ItemKind::Enum(e) => {
                    let mut tys = Vec::new();
                    let mut discs = Vec::new();
                    for v in &mut e.variants {
                        if let VariantFields::Struct(fs) | VariantFields::Tuple(fs) = &v.fields {
                            tys.extend(fs.iter().map(|f| f.ty));
                        }
                        if let Some(d) = v.discriminant {
                            discs.push(d);
                        }
                    }
                    for t in tys {
                        self.ty(ast, t, module);
                    }
                    let mut scopes = vec![Frame::default()];
                    for d in discs {
                        self.expr(ast, d, module, &mut scopes);
                    }
                }
                ItemKind::Impl(imp) => {
                    self.ty(ast, imp.self_ty, module);
                    let mut fns = std::mem::take(&mut imp.fns);
                    for f in &mut fns {
                        self.fn_def(ast, f, module);
                    }
                    imp.fns = fns;
                }
                ItemKind::Const(c) => {
                    self.ty(ast, c.ty, module);
                    if let Some(v) = c.value {
                        let mut scopes = vec![Frame::default()];
                        self.expr(ast, v, module, &mut scopes);
                    }
                }
                ItemKind::Static(s) => {
                    self.ty(ast, s.ty, module);
                    if let Some(v) = s.value {
                        let mut scopes = vec![Frame::default()];
                        self.expr(ast, v, module, &mut scopes);
                    }
                }
                ItemKind::Type(a) => self.ty(ast, a.ty, module),
                ItemKind::Mod(m) => {
                    let mut key = prefix.to_vec();
                    key.push(m.name);
                    if let (Some(body), Some(&child)) = (&mut m.body, self.list_module.get(&(fi, key.clone()))) {
                        self.items(ast, body, fi, child, &key);
                    }
                }
                _ => {}
            }
        }
    }

    /// Rewrites one fn's signature types and body.
    fn fn_def(&mut self, ast: &mut Ast, def: &mut FnDef, module: ModuleId) {
        for p in &def.params {
            let t = p.ty;
            self.ty(ast, t, module);
        }
        if let Some(t) = def.ret {
            self.ty(ast, t, module);
        }
        if let Some(body) = def.body {
            let mut scopes = vec![Frame::default()];
            let mut frame = Frame::default();
            for p in &def.params {
                match p.pat {
                    Some(pat) => self.pat_bindings(ast, pat, &mut frame.locals),
                    None => frame.locals.push(p.name),
                }
            }
            scopes.push(frame);
            self.block(ast, body, module, &mut scopes);
        }
    }

    /// Collects the binding names a pattern introduces.
    fn pat_bindings(&self, ast: &Ast, id: PatId, out: &mut Vec<Sym>) {
        match ast.pat(id) {
            Pat::Binding { name, .. } => out.push(*name),
            Pat::At { name, inner, .. } => {
                out.push(*name);
                self.pat_bindings(ast, *inner, out);
            }
            Pat::TupleStruct { elems, .. } | Pat::Tuple(elems) | Pat::Or(elems) => {
                for e in elems {
                    self.pat_bindings(ast, *e, out);
                }
            }
            Pat::Struct { fields, .. } => {
                for (_, f) in fields {
                    self.pat_bindings(ast, *f, out);
                }
            }
            Pat::Slice { prefix, middle, suffix } => {
                for e in prefix.iter().chain(suffix) {
                    self.pat_bindings(ast, *e, out);
                }
                if let Some(m) = middle {
                    self.pat_bindings(ast, *m, out);
                }
            }
            Pat::Ref { inner, .. } | Pat::Paren(inner) => self.pat_bindings(ast, *inner, out),
            _ => {}
        }
    }

    /// True when `name` is a local in any open frame.
    fn is_local(scopes: &[Frame], name: Sym) -> bool {
        scopes.iter().rev().any(|f| f.locals.contains(&name))
    }

    /// Resolves a path with lexical scopes first. `Done` from a local
    /// variable is reported as Absent with the `local` flag set through
    /// the return: callers leave the path written.
    fn resolve(&self, segs: &[Sym], ns: Namespace, module: ModuleId, scopes: &[Frame]) -> (PathRes, bool) {
        if segs.len() == 1 && ns != Namespace::Type && Self::is_local(scopes, segs[0]) {
            return (PathRes::Absent, true);
        }
        // Function-local imports answer for the first segment.
        if !segs.is_empty() {
            let first = segs[0];
            let plain = self.interner.get(first);
            if !matches!(plain, "crate" | "self" | "super" | "Self") {
                for frame in scopes.iter().rev() {
                    if let Some(b) = frame.imports.get(&(first, ns_index(ns))) {
                        return match b {
                            LocalBind::Ambiguous => (PathRes::Ambiguous, false),
                            LocalBind::Target(t) => {
                                if segs.len() == 1 {
                                    (PathRes::Done(*t), false)
                                } else {
                                    match self.tables.walk_from(module, *t, &segs[1..], ns, self.interner) {
                                        PathRes::Partial(t2, rest) => (PathRes::Partial(t2, rest + 1), false),
                                        other => (other, false),
                                    }
                                }
                            }
                        };
                    }
                }
            }
        }
        (self.tables.resolve_path(module, segs, ns, PathMode::Lexical, false, self.interner), false)
    }

    /// Applies a resolution to a written path in place. `span` is the
    /// path's own span for diagnostics.
    fn apply(&mut self, segs: &mut Vec<PathSeg>, res: PathRes, span: Span, module: ModuleId) {
        match res {
            PathRes::Done(Target::Def(def)) => {
                if let Some(info) = self.tables.def_info.get(&def) {
                    let args = segs.last().map(|s| s.args.clone()).unwrap_or_default();
                    *segs = vec![PathSeg { name: info.flat, args }];
                }
            }
            PathRes::Done(Target::Variant(def, variant)) => {
                if let Some(info) = self.tables.def_info.get(&def) {
                    *segs = vec![PathSeg::plain(info.flat), PathSeg::plain(variant)];
                }
            }
            PathRes::Done(Target::Module(_)) => {
                // A module as a value or type is an error the checker
                // reports; leave the path written.
            }
            PathRes::Done(Target::Extern(i)) => {
                if !self.tables.externs[i as usize].is_std_lib {
                    self.diags.push(crate::diag::not_yet("L0505", span, "items from other crates"));
                }
            }
            PathRes::Partial(Target::Def(def), rest) => {
                if rest + 1 == segs.len() {
                    if let Some(info) = self.tables.def_info.get(&def) {
                        let item_seg = segs[rest].clone();
                        // Associated fn visibility (variants take the
                        // enum's vis, already checked by resolution).
                        if let Some(methods) = self.tables.assoc_vis.get(&def)
                            && let Some((vis, def_mod)) = methods.get(&item_seg.name)
                            && !self.tables.visible(vis, *def_mod, module, self.interner)
                        {
                            self.diags.push(private_diag(self.interner.get(item_seg.name), span));
                        }
                        *segs = vec![PathSeg::plain(info.flat), item_seg];
                    }
                }
            }
            PathRes::Partial(Target::Variant(..), _) => {}
            PathRes::Partial(Target::Extern(i), _) => {
                if !self.tables.externs[i as usize].is_std_lib {
                    self.diags.push(crate::diag::not_yet("L0505", span, "items from other crates"));
                }
            }
            PathRes::Partial(Target::Module(_), _) => {}
            PathRes::Ambiguous => {
                let name = segs.last().map(|s| self.interner.get(s.name).to_string()).unwrap_or_default();
                self.diags.push(ambiguous_diag(&name, span));
            }
            PathRes::Private => {
                let name = segs.last().map(|s| self.interner.get(s.name).to_string()).unwrap_or_default();
                self.diags.push(private_diag(&name, span));
            }
            PathRes::Prelude | PathRes::Absent => {}
        }
    }

    /// Rewrites one written path (segments borrowed out of the arena by
    /// the caller, then put back through `set`).
    fn rewrite_path(&mut self, segs: &mut Vec<PathSeg>, ns: Namespace, span: Span, module: ModuleId, scopes: &[Frame], ast: &mut Ast) {
        // Generic arguments hold types and const exprs of their own.
        let mut tys = Vec::new();
        for s in segs.iter() {
            collect_arg_tys(&s.args, &mut tys);
        }
        for t in tys {
            self.ty(ast, t, module);
        }
        let names: Vec<Sym> = segs.iter().map(|s| s.name).collect();
        // A leading `::` arrives as a marker segment (parser). Resolve
        // through the extern prelude, and drop the marker when the path
        // stays written (std compat reads plain `std::...`).
        if names.first().is_some_and(|n| self.interner.get(*n) == "::") {
            let res = self.tables.resolve_path(module, &names[1..], ns, PathMode::Lexical, true, self.interner);
            match res {
                PathRes::Partial(Target::Extern(i), _) | PathRes::Done(Target::Extern(i)) if self.tables.externs[i as usize].is_std_lib => {
                    segs.remove(0);
                }
                _ => self.apply(segs, res, span, module),
            }
            return;
        }
        let (res, local) = self.resolve(&names, ns, module, scopes);
        if !local {
            // Lexical scope (section 1.3): an unqualified name that only
            // another module defines is not found here, even though the
            // merged flat tables could answer it. Names no module
            // defines (primitives, builtins) fall through as before.
            if res == PathRes::Absent && names.first().is_some_and(|n| self.tables.any_local_named(*n)) {
                let first = self.interner.get(names[0]).to_string();
                self.diags.push(if ns == Namespace::Type {
                    Diag::new(
                        "L0102",
                        span,
                        format!("cannot find type `{first}` in this scope"),
                        "Import it with `use`, or write its module path.",
                    )
                } else {
                    Diag::new(
                        "L0101",
                        span,
                        format!("cannot find value `{first}` in this scope"),
                        "Import it with `use`, or write its module path.",
                    )
                });
                return;
            }
            self.apply(segs, res, span, module);
        }
    }

    /// Rewrites the type at `id`, recursing into compound types.
    fn ty(&mut self, ast: &mut Ast, id: TyId, module: ModuleId) {
        match ast.ty(id) {
            TyExpr::Path(_) => {
                let span = ast.ty_span(id);
                let TyExpr::Path(mut segs) = std::mem::replace(&mut ast.tys[id.0 as usize], TyExpr::Unit) else { return };
                self.rewrite_path(&mut segs, Namespace::Type, span, module, &[], ast);
                ast.tys[id.0 as usize] = TyExpr::Path(segs);
            }
            TyExpr::Ref { inner, .. } => {
                let inner = *inner;
                self.ty(ast, inner, module);
            }
            TyExpr::Tuple(ts) => {
                let ts = ts.clone();
                for t in ts {
                    self.ty(ast, t, module);
                }
            }
            TyExpr::Slice(inner) | TyExpr::Paren(inner) | TyExpr::Ptr { inner, .. } => {
                let inner = *inner;
                self.ty(ast, inner, module);
            }
            TyExpr::Array { inner, len } => {
                let (inner, len) = (*inner, *len);
                self.ty(ast, inner, module);
                let mut scopes = vec![Frame::default()];
                self.expr(ast, len, module, &mut scopes);
            }
            TyExpr::FnPtr { inputs, ret, .. } => {
                let ins: Vec<TyId> = inputs.iter().map(|p| p.ty).collect();
                let ret = *ret;
                for t in ins {
                    self.ty(ast, t, module);
                }
                if let Some(r) = ret {
                    self.ty(ast, r, module);
                }
            }
            _ => {}
        }
    }

    /// Rewrites one block: statements in order, with `let` bindings and
    /// function-local `use` scopes.
    fn block(&mut self, ast: &mut Ast, id: BlockId, module: ModuleId, scopes: &mut Vec<Frame>) {
        scopes.push(Frame::default());
        let stmts = std::mem::take(&mut ast.blocks[id.0 as usize].stmts);
        let mut out = Vec::with_capacity(stmts.len());
        for stmt in stmts {
            match stmt {
                Stmt::Let { pat, ty, init, els, attrs, span } => {
                    if let Some(t) = ty {
                        self.ty(ast, t, module);
                    }
                    if let Some(e) = init {
                        self.expr(ast, e, module, scopes);
                    }
                    self.pat(ast, pat, module, scopes);
                    let mut names = Vec::new();
                    self.pat_bindings(ast, pat, &mut names);
                    if let Some(frame) = scopes.last_mut() {
                        frame.locals.extend(names);
                    }
                    if let Some(b) = els {
                        self.block(ast, b, module, scopes);
                    }
                    out.push(Stmt::Let { pat, ty, init, els, attrs, span });
                }
                Stmt::Expr { expr, semi } => {
                    self.expr(ast, expr, module, scopes);
                    out.push(Stmt::Expr { expr, semi });
                }
                Stmt::Item(idx) => {
                    self.stmt_item(ast, idx, module, scopes);
                    out.push(Stmt::Item(idx));
                }
                Stmt::Macro { call, semi } => out.push(Stmt::Macro { call, semi }),
            }
        }
        ast.blocks[id.0 as usize].stmts = out;
        if let Some(tail) = ast.blocks[id.0 as usize].tail {
            self.expr(ast, tail, module, scopes);
        }
        scopes.pop();
    }

    /// Resolves one statement item. Only `use` reaches here today (the
    /// parser rejects other body items); its bindings scope to the rest
    /// of the block.
    fn stmt_item(&mut self, ast: &mut Ast, idx: u32, module: ModuleId, scopes: &mut Vec<Frame>) {
        let Some(item) = ast.stmt_items.get(idx as usize) else { return };
        let ItemKind::Use(u) = &item.kind else { return };
        let tree = u.tree.clone();
        let span = item.span;
        let mut flat = Vec::new();
        flatten_use(&tree, module, VisKind::Priv, &mut flat, self.interner);
        for imp in flat {
            match imp.kind {
                ImportKind::Single { path, name } => {
                    if path.len() == 1 {
                        continue;
                    }
                    match self.tables.resolve_module_path(module, &path[..path.len() - 1], imp.leading_colon, self.interner) {
                        PathRes::Done(Target::Module(src)) => {
                            let last = *path.last().unwrap();
                            let mut any = false;
                            for ns in [Namespace::Type, Namespace::Value, Namespace::Macro] {
                                match self.tables.lookup(src, ns, last) {
                                    Some(BindState::One(b)) if self.tables.visible(&b.vis, b.def_module, module, self.interner) => {
                                        any = true;
                                        insert_local(scopes, name, ns, LocalBind::Target(b.target), 2);
                                    }
                                    Some(BindState::Ambiguous) => {
                                        any = true;
                                        insert_local(scopes, name, ns, LocalBind::Ambiguous, 2);
                                    }
                                    _ => {}
                                }
                            }
                            if !any {
                                self.diags.push(Diag::new(
                                    "L0506",
                                    span,
                                    format!(
                                        "unresolved import `{}`",
                                        path.iter().map(|s| self.interner.get(*s)).collect::<Vec<_>>().join("::")
                                    ),
                                    "Check the path: every segment must name a module or item that is visible here.",
                                ));
                            }
                        }
                        PathRes::Done(Target::Extern(_)) => {}
                        _ => {
                            self.diags.push(Diag::new(
                                "L0506",
                                span,
                                format!(
                                    "unresolved import `{}`",
                                    path.iter().map(|s| self.interner.get(*s)).collect::<Vec<_>>().join("::")
                                ),
                                "Check the path: every segment must name a module or item that is visible here.",
                            ));
                        }
                    }
                }
                ImportKind::Glob { path } => {
                    if let PathRes::Done(Target::Module(src)) =
                        self.tables.resolve_module_path(module, &path, imp.leading_colon, self.interner)
                    {
                        let mut entries = Vec::new();
                        for ns in [Namespace::Type, Namespace::Value, Namespace::Macro] {
                            for (name, state) in &self.tables.maps[src.0 as usize][ns_index(ns)] {
                                match state {
                                    BindState::One(b) if self.tables.visible(&b.vis, b.def_module, module, self.interner) => {
                                        entries.push((*name, ns, LocalBind::Target(b.target)));
                                    }
                                    BindState::Ambiguous => entries.push((*name, ns, LocalBind::Ambiguous)),
                                    _ => {}
                                }
                            }
                        }
                        for (name, ns, bind) in entries {
                            insert_local(scopes, name, ns, bind, 1);
                        }
                    }
                }
            }
        }
    }

    /// Rewrites one pattern's paths.
    fn pat(&mut self, ast: &mut Ast, id: PatId, module: ModuleId, scopes: &[Frame]) {
        let span = ast.pat_span(id);
        match std::mem::replace(&mut ast.pats[id.0 as usize], Pat::Wild) {
            Pat::Path(mut segs) => {
                self.rewrite_path(&mut segs, Namespace::Value, span, module, scopes, ast);
                ast.pats[id.0 as usize] = Pat::Path(segs);
            }
            Pat::TupleStruct { path: mut s, elems } => {
                self.rewrite_path(&mut s, Namespace::Type, span, module, scopes, ast);
                for e in &elems {
                    self.pat(ast, *e, module, scopes);
                }
                ast.pats[id.0 as usize] = Pat::TupleStruct { path: s, elems };
            }
            Pat::Struct { path: mut s, fields, rest } => {
                self.rewrite_path(&mut s, Namespace::Type, span, module, scopes, ast);
                for (_, f) in &fields {
                    self.pat(ast, *f, module, scopes);
                }
                ast.pats[id.0 as usize] = Pat::Struct { path: s, fields, rest };
            }
            node => {
                // Child patterns and expressions first, then the node
                // goes back unchanged.
                match &node {
                    Pat::Lit(e) => {
                        let e = *e;
                        let mut sc = scopes.to_vec_shallow();
                        self.expr(ast, e, module, &mut sc);
                    }
                    Pat::Or(elems) | Pat::Tuple(elems) => {
                        for e in elems {
                            self.pat(ast, *e, module, scopes);
                        }
                    }
                    Pat::Range { lo, hi, .. } => {
                        let mut sc = scopes.to_vec_shallow();
                        if let Some(e) = lo {
                            self.expr(ast, *e, module, &mut sc);
                        }
                        if let Some(e) = hi {
                            self.expr(ast, *e, module, &mut sc);
                        }
                    }
                    Pat::At { inner, .. } | Pat::Ref { inner, .. } | Pat::Paren(inner) => {
                        let inner = *inner;
                        self.pat(ast, inner, module, scopes);
                    }
                    Pat::Slice { prefix, middle, suffix } => {
                        for e in prefix.iter().chain(suffix) {
                            self.pat(ast, *e, module, scopes);
                        }
                        if let Some(m) = middle {
                            self.pat(ast, *m, module, scopes);
                        }
                    }
                    _ => {}
                }
                ast.pats[id.0 as usize] = node;
            }
        }
    }

    /// Rewrites one expression subtree.
    fn expr(&mut self, ast: &mut Ast, id: ExprId, module: ModuleId, scopes: &mut Vec<Frame>) {
        let span = ast.expr_span(id);
        // Nodes that carry a path are swapped out whole, rewritten, and
        // put back (the path rewrite needs `ast` for generic-arg types).
        if matches!(ast.exprs[id.0 as usize], Expr::Path(_)) {
            let Expr::Path(mut segs) = std::mem::replace(&mut ast.exprs[id.0 as usize], Expr::Unit) else { return };
            self.rewrite_path(&mut segs, Namespace::Value, span, module, scopes, ast);
            ast.exprs[id.0 as usize] = Expr::Path(segs);
            return;
        }
        if matches!(ast.exprs[id.0 as usize], Expr::StructLit { .. }) {
            let Expr::StructLit { path: mut segs, fields, update } = std::mem::replace(&mut ast.exprs[id.0 as usize], Expr::Unit) else {
                return;
            };
            self.rewrite_path(&mut segs, Namespace::Type, span, module, scopes, ast);
            for (_, _, e) in &fields {
                let e = *e;
                self.expr(ast, e, module, scopes);
            }
            if let Some(u) = update {
                self.expr(ast, u, module, scopes);
            }
            ast.exprs[id.0 as usize] = Expr::StructLit { path: segs, fields, update };
            return;
        }
        match ast.exprs[id.0 as usize].kind_children() {
            ExprKids { blocks, exprs, pats_with_scope, ty } => {
                if let Some(t) = ty {
                    self.ty(ast, t, module);
                }
                for e in exprs {
                    self.expr(ast, e, module, scopes);
                }
                for (pat, body) in pats_with_scope {
                    self.pat(ast, pat, module, scopes);
                    let mut frame = Frame::default();
                    self.pat_bindings(ast, pat, &mut frame.locals);
                    scopes.push(frame);
                    match body {
                        ScopeBody::Block(b) => self.block(ast, b, module, scopes),
                        ScopeBody::Expr(e) => self.expr(ast, e, module, scopes),
                        ScopeBody::None => {}
                    }
                    scopes.pop();
                }
                for b in blocks {
                    self.block(ast, b, module, scopes);
                }
            }
        }
    }
}

/// The generic-argument type ids under one segment's args.
fn collect_arg_tys(args: &GenericArgs, out: &mut Vec<TyId>) {
    match args {
        GenericArgs::Angle(args) => {
            for a in args {
                match a {
                    GenericArg::Type(t) => out.push(*t),
                    GenericArg::Binding { kind: BindingKind::EqTy(t), .. } => out.push(*t),
                    _ => {}
                }
            }
        }
        GenericArgs::Parenthesized { inputs, output } => {
            out.extend(inputs.iter().copied());
            out.extend(output.iter().copied());
        }
        GenericArgs::None => {}
    }
}

/// Inserts one function-local import binding with a rank: an explicit
/// import (2) beats a glob (1); two globs with different targets are
/// ambiguous.
fn insert_local(scopes: &mut [Frame], name: Sym, ns: Namespace, bind: LocalBind, rank: u8) {
    let Some(frame) = scopes.last_mut() else { return };
    let key = (name, ns_index(ns));
    match (frame.imports.get(&key), bind) {
        (Some(LocalBind::Target(old)), LocalBind::Target(new)) if *old != new && rank <= 1 => {
            frame.imports.insert(key, LocalBind::Ambiguous);
        }
        (Some(_), _) if rank <= 1 => {}
        _ => {
            frame.imports.insert(key, bind);
        }
    }
}

/// A throwaway FnDef for `mem::replace` during the item walk.
fn dummy_fn() -> FnDef {
    FnDef {
        name: Sym(0),
        name_span: Span::default(),
        is_test: false,
        vis: Vis::Private,
        attrs: Vec::new(),
        qual: Default::default(),
        generics: Default::default(),
        self_param: None,
        params: Vec::new(),
        variadic: false,
        ret: None,
        where_clause: Default::default(),
        body: None,
        exprs: (0, 0),
        pats: (0, 0),
    }
}

/// Shallow copy of the scope stack for sub-walks that must not leak
/// bindings (literal-pattern expressions). Frames are small.
trait ShallowScopes {
    fn to_vec_shallow(&self) -> Vec<Frame>;
}

impl ShallowScopes for [Frame] {
    fn to_vec_shallow(&self) -> Vec<Frame> {
        self.iter().map(|f| Frame { locals: f.locals.clone(), imports: f.imports.clone() }).collect()
    }
}

/// Which child nodes an expression has, grouped by how the walk treats
/// them. Pattern-plus-body pairs get a scope frame from the pattern.
struct ExprKids {
    blocks: Vec<BlockId>,
    exprs: Vec<ExprId>,
    pats_with_scope: Vec<(PatId, ScopeBody)>,
    ty: Option<TyId>,
}

enum ScopeBody {
    Block(BlockId),
    Expr(ExprId),
    None,
}

/// Child enumeration for the rewrite walk, over the expression forms the
/// parser produces. Match arms: the walk needs arms one by one (each
/// arm's guard and body see the arm pattern's bindings), so Match is
/// expanded here into scrutinee plus one scoped pair per arm.
trait KindChildren {
    fn kind_children(&self) -> ExprKids;
}

impl KindChildren for Expr {
    fn kind_children(&self) -> ExprKids {
        let mut k = ExprKids { blocks: Vec::new(), exprs: Vec::new(), pats_with_scope: Vec::new(), ty: None };
        match self {
            Expr::Int(..)
            | Expr::Bool(_)
            | Expr::Str(_)
            | Expr::Char(_)
            | Expr::Unit
            | Expr::SelfValue
            | Expr::Float(_)
            | Expr::Underscore => {}
            Expr::Path(_) | Expr::StructLit { .. } => {}
            Expr::Block(b) | Expr::UnsafeBlock(b) | Expr::ConstBlock(b) => k.blocks.push(*b),
            Expr::LabeledBlock { body, .. } | Expr::AsyncBlock { body, .. } => k.blocks.push(*body),
            Expr::If { cond, then, els } => {
                k.exprs.push(*cond);
                k.blocks.push(*then);
                if let Some(e) = els {
                    k.exprs.push(*e);
                }
            }
            Expr::While { cond, body, .. } => {
                k.exprs.push(*cond);
                k.blocks.push(*body);
            }
            Expr::Loop { body, .. } => k.blocks.push(*body),
            Expr::For { pat, iter, body, .. } => {
                k.exprs.push(*iter);
                k.pats_with_scope.push((*pat, ScopeBody::Block(*body)));
            }
            Expr::Match { scrut, arms } => {
                k.exprs.push(*scrut);
                for a in arms {
                    if let Some(g) = a.guard {
                        k.pats_with_scope.push((a.pat, ScopeBody::Expr(g)));
                    }
                    k.pats_with_scope.push((a.pat, ScopeBody::Expr(a.body)));
                }
            }
            Expr::Call { callee, args } => {
                k.exprs.push(*callee);
                k.exprs.extend(args.iter().copied());
            }
            Expr::MethodCall { recv, args, .. } => {
                k.exprs.push(*recv);
                k.exprs.extend(args.iter().copied());
            }
            Expr::Field { base, .. } | Expr::TupleField { base, .. } => k.exprs.push(*base),
            Expr::Index { base, index } => {
                k.exprs.push(*base);
                k.exprs.push(*index);
            }
            Expr::Binary { lhs, rhs, .. } | Expr::Assign { lhs, rhs } | Expr::AssignOp { lhs, rhs, .. } => {
                k.exprs.push(*lhs);
                k.exprs.push(*rhs);
            }
            Expr::Unary { expr, .. } | Expr::Ref { expr, .. } | Expr::Deref(expr) | Expr::Try(expr) | Expr::Await(expr) => {
                k.exprs.push(*expr)
            }
            Expr::Cast { expr, ty } => {
                k.exprs.push(*expr);
                k.ty = Some(*ty);
            }
            Expr::Range { lo, hi, .. } => {
                if let Some(e) = lo {
                    k.exprs.push(*e);
                }
                if let Some(e) = hi {
                    k.exprs.push(*e);
                }
            }
            Expr::Break { value, .. } => {
                if let Some(e) = value {
                    k.exprs.push(*e);
                }
            }
            Expr::Continue(_) => {}
            Expr::Return(e) => {
                if let Some(e) = e {
                    k.exprs.push(*e);
                }
            }
            Expr::Macro { args, .. } => k.exprs.extend(args.iter().copied()),
            Expr::Tuple(es) | Expr::Array(es) => k.exprs.extend(es.iter().copied()),
            Expr::ArrayRepeat { value, len } => {
                k.exprs.push(*value);
                k.exprs.push(*len);
            }
            Expr::Closure { params, ret, body, .. } => {
                for p in params {
                    if let Some(t) = p.ty {
                        let _ = t;
                    }
                    k.pats_with_scope.push((p.pat, ScopeBody::None));
                }
                if let Some(r) = ret {
                    k.ty = Some(*r);
                }
                k.exprs.push(*body);
            }
            Expr::Let { pat, scrut } => {
                k.exprs.push(*scrut);
                k.pats_with_scope.push((*pat, ScopeBody::None));
            }
            Expr::QPath { .. } | Expr::MacroCall(_) => {}
        }
        k
    }
}

/// Moves inline module bodies into the flat item list, dropping mod,
/// use, and extern crate items (their bindings live in the tables).
fn flatten_items(items: Vec<Item>, out: &mut Vec<Item>) {
    for item in items {
        match item.kind {
            ItemKind::Mod(m) => {
                if let Some(body) = m.body {
                    flatten_items(body, out);
                }
            }
            ItemKind::Use(_) | ItemKind::ExternCrate(_) => {}
            _ => out.push(item),
        }
    }
}
