// The std loader (docs/ARCH.md sections 3.1 and 3.8, serial refactor S5).
//
// Parses and checks the shipped `library/` source files as their own
// crates, resolves the lang item table, and produces the splice text
// the driver appends to a user compile that can mention a source std
// fn. The driver calls `load_std` at most once per session and caches
// the result (std is immutable inside a session, section 3.8); the
// common compile that mentions no source std fn never calls it at all.
//
// Splice model, until multi-crate collect lands (W-RESOLVE): a spliced
// std file rides in the user crate under mangled fn names, in a byte
// range after the user file. The standalone check here runs under the
// shipped crate's own stable hash, so def identity and intrinsic
// privilege are proven in the shipped crate first; the splice range
// then carries the same provenance into the user compile. Only
// non-generic fns route this way (section 9.2 S5).
//
// Every failure here is a compiler installation error (a broken
// `library/`, a registry row with no source fn, a missing required
// lang item), returned as one message string; the driver reports it
// with exit code 3. It is never a user diagnostic.
use crate::ast::{Ast, ItemKind};
use crate::check::collect;
use crate::def::{CrateIds, LOCAL_CRATE, LocalDefId};
use crate::diag::{Diag, FileId};
use crate::intern::{Interner, Known};
use crate::ty::TyIntern;
use crate::ty::lang::{self, LangItems, ShippedCrate, StdFnDef};
use crate::{borrowck, check, lexer, lower, parser};

/// One shipped source file the loader knows: its crate, its module path
/// inside the crate, and its path under `library/`. The built-in text
/// comes from `builtin_text`; `LUST_STD_SRC` overrides the whole tree.
struct SourceFile {
    krate: ShippedCrate,
    module: &'static [&'static str],
    rel: &'static str,
}

const SOURCE_FILES: &[SourceFile] = &[
    SourceFile { krate: ShippedCrate::Core, module: &[], rel: "core/src/lib.rs" },
    SourceFile { krate: ShippedCrate::Core, module: &["intrinsics"], rel: "core/src/intrinsics.rs" },
    SourceFile { krate: ShippedCrate::Alloc, module: &[], rel: "alloc/src/lib.rs" },
    SourceFile { krate: ShippedCrate::Std, module: &[], rel: "std/src/lib.rs" },
    SourceFile { krate: ShippedCrate::Std, module: &["prelude"], rel: "std/src/prelude.rs" },
    SourceFile { krate: ShippedCrate::Std, module: &["process"], rel: "std/src/process.rs" },
];

/// The `library/` text built into the compiler, by relative path.
fn builtin_text(rel: &str) -> Option<&'static str> {
    Some(match rel {
        "core/src/lib.rs" => include_str!("../library/core/src/lib.rs"),
        "core/src/intrinsics.rs" => include_str!("../library/core/src/intrinsics.rs"),
        "alloc/src/lib.rs" => include_str!("../library/alloc/src/lib.rs"),
        "std/src/lib.rs" => include_str!("../library/std/src/lib.rs"),
        "std/src/prelude.rs" => include_str!("../library/std/src/prelude.rs"),
        "std/src/process.rs" => include_str!("../library/std/src/process.rs"),
        "core/src/time.rs" => include_str!("../library/core/src/time.rs"),
        "std/src/time.rs" => include_str!("../library/std/src/time.rs"),
        _ => return None,
    })
}

/// The text of one shipped file: from `$LUST_STD_SRC/<rel>` when the
/// override is set (section 3.8), else the built-in copy.
fn source_text(rel: &str) -> Result<String, String> {
    match std::env::var_os("LUST_STD_SRC") {
        Some(dir) if !dir.is_empty() => {
            let path = std::path::Path::new(&dir).join(rel);
            std::fs::read_to_string(&path)
                .map_err(|e| format!("lust std load failed: cannot read {} from LUST_STD_SRC: {e}", path.display()))
        }
        _ => builtin_text(rel).map(str::to_string).ok_or_else(|| format!("lust std load failed: no built-in text for library/{rel}")),
    }
}

/// One checked shipped file, kept for lang lookup and splice building.
struct CheckedFile {
    krate: ShippedCrate,
    module: &'static [&'static str],
    rel: &'static str,
    /// The source with `#[lust_lang]` lines blanked (same byte length,
    /// so spans into this text stay exact).
    clean: String,
    interner: Interner,
    ast: Ast,
}

/// What a session needs from one std load.
pub struct StdLoad {
    /// The resolved lang items of this load. Read by later waves; S5
    /// only proves that required items resolve.
    #[allow(dead_code)] // First consumers are W-STD and W-MONO; the load guarantee is the S5 gate.
    pub lang: LangItems,
    /// Splice text per shipped crate, in load order. The driver appends
    /// each block after the user file and records its byte range.
    pub splices: Vec<(ShippedCrate, String)>,
    /// The implemented `STD_FNS` rows whose bodies ride in `splices`.
    pub fns: Vec<&'static StdFnDef>,
}

/// Extracts the `#[lust_lang = "<name>"]` marks from shipped source:
/// returns the source with each mark line blanked (offsets preserved)
/// and `(lang name, byte offset of the next line)` per mark. A mark
/// must sit alone on its line until the parser learns the attribute.
/// A line that starts a mark but does not parse as one is an
/// installation error, so a typo cannot silently drop a lang item;
/// plain mentions in comments are fine.
fn scan_lang_attrs(src: &str, rel: &str) -> Result<(String, Vec<(String, u32)>), String> {
    let mut clean = String::with_capacity(src.len());
    let mut marks = Vec::new();
    for line in src.split_inclusive('\n') {
        let body = line.trim_end_matches(['\n', '\r']);
        let at = clean.len() as u32 + line.len() as u32;
        if body.trim_start().starts_with("#[lust_lang") {
            let t = body.trim();
            let inner = t
                .strip_prefix("#[lust_lang")
                .and_then(|r| r.trim().strip_prefix('='))
                .map(str::trim)
                .and_then(|r| r.strip_suffix(']'))
                .map(str::trim)
                .filter(|r| r.len() >= 2 && r.starts_with('"') && r.ends_with('"'))
                .map(|r| r[1..r.len() - 1].to_string());
            let Some(name) = inner.filter(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_lowercase() || b == b'_')) else {
                return Err(format!(
                    "lust std load failed: library/{rel}: bad #[lust_lang] mark (write it alone on its line as #[lust_lang = \"name\"])"
                ));
            };
            marks.push((name, at));
            clean.extend(line.bytes().map(|b| if b == b'\n' { '\n' } else { ' ' }));
        } else {
            clean.push_str(line);
        }
    }
    Ok((clean, marks))
}

/// One diagnostic as one line of an installation error.
fn diag_line(rel: &str, d: &Diag) -> String {
    format!("library/{rel}: {}: {}", d.code, d.message)
}

/// Parses, collects, checks, lowers, and borrow-checks one shipped
/// file as its own crate. Returns the file plus its lang marks.
fn check_file(file: &SourceFile, text: &str) -> Result<(CheckedFile, Vec<(String, u32)>), String> {
    let (clean, marks) = scan_lang_attrs(text, file.rel)?;
    let interner = Interner::default();
    let known = Known::new(&interner);
    let lexed = lexer::lex(&clean, FileId(0), 0, &interner)
        .and_then(|l| {
            let ctx = crate::expand::ExpandCtx::for_file(&interner, &known, std::path::Path::new(file.rel), &clean, false);
            crate::expand::expand_lexed(l, &ctx)
        })
        .map_err(|d| format!("lust std load failed: {}", diag_line(file.rel, &d)))?;
    let ast = parser::parse(&lexed, &interner, &known).map_err(|d| format!("lust std load failed: {}", diag_line(file.rel, &d)))?;
    let ids = CrateIds { local: LOCAL_CRATE, stable: file.krate.stable_hash() };
    let mut program = collect::collect(&ast, &interner, &known, ids)
        .map_err(|ds| format!("lust std load failed: {}", ds.iter().map(|d| diag_line(file.rel, d)).collect::<Vec<_>>().join("; ")))?;
    // The whole file is shipped source: intrinsic calls in it run the
    // privilege test against this file's crate.
    program.shipped_ranges = vec![(0, clean.len() as u32, file.krate)];
    for i in 0..program.fns.len() {
        let f = LocalDefId(i as u32);
        let (checked, errs) = check::check_fn(&program, f);
        if !errs.is_empty() {
            return Err(format!("lust std load failed: {}", errs.iter().map(|d| diag_line(file.rel, d)).collect::<Vec<_>>().join("; ")));
        }
        let body = lower::lower(&program, f, checked);
        let errs = borrowck::borrowck(&program, &body);
        if !errs.is_empty() {
            return Err(format!("lust std load failed: {}", errs.iter().map(|d| diag_line(file.rel, d)).collect::<Vec<_>>().join("; ")));
        }
    }
    Ok((CheckedFile { krate: file.krate, module: file.module, rel: file.rel, clean, interner, ast }, marks))
}

/// Loads and checks the whole shipped library. Called at most once
/// per session (the driver caches the result), and only when a user
/// compile can mention a source std fn.
pub fn load_std() -> Result<StdLoad, String> {
    load_std_from(&mut |rel| source_text(rel))
}

/// `load_std` over a caller-supplied text source, so tests can feed
/// fixture shipped source without touching the real `library/`.
fn load_std_from(read: &mut dyn FnMut(&str) -> Result<String, String>) -> Result<StdLoad, String> {
    let mut files: Vec<CheckedFile> = Vec::new();
    let mut marks: Vec<(usize, String, u32)> = Vec::new(); // (file index, lang name, next-line offset)
    for file in SOURCE_FILES {
        let text = read(file.rel)?;
        let (checked, file_marks) = check_file(file, &text)?;
        let idx = files.len();
        marks.extend(file_marks.into_iter().map(|(n, at)| (idx, n, at)));
        files.push(checked);
    }
    let lang_items = resolve_lang_items(&files, &marks)?;
    let (mut splices, fns) = build_splices(&files)?;
    for m in crate::stdmods::STD_MODULES {
        let text = read(m.rel)?;
        splices.push((m.krate, module_splice(m, &text)?));
    }
    Ok(StdLoad { lang: lang_items, splices, fns })
}

/// The splice text of one std source module (src/stdmods.rs). The file
/// must lex, expand, and parse on its own; its items are checked in the
/// user compile, inside their hidden module, because they use imports
/// and module paths the standalone flat check here does not resolve.
fn module_splice(m: &crate::stdmods::StdModule, text: &str) -> Result<String, String> {
    let (clean, marks) = scan_lang_attrs(text, m.rel)?;
    if !marks.is_empty() {
        return Err(format!("lust std load failed: library/{}: a std source module cannot hold #[lust_lang] marks yet", m.rel));
    }
    let interner = Interner::default();
    let known = Known::new(&interner);
    let lexed = lexer::lex(&clean, FileId(0), 0, &interner)
        .and_then(|l| {
            let ctx = crate::expand::ExpandCtx::for_file(&interner, &known, std::path::Path::new(m.rel), &clean, false);
            crate::expand::expand_lexed(l, &ctx)
        })
        .map_err(|d| format!("lust std load failed: {}", diag_line(m.rel, &d)))?;
    parser::parse(&lexed, &interner, &known).map_err(|d| format!("lust std load failed: {}", diag_line(m.rel, &d)))?;
    Ok(crate::stdmods::splice_text(m, &clean))
}

/// Fills the lang table: builtin defs first, then one def per
/// `#[lust_lang]` mark (the item after the mark). Fails on an unknown
/// or duplicate mark, a mark with no item after it, or a required
/// item with no def.
fn resolve_lang_items(files: &[CheckedFile], marks: &[(usize, String, u32)]) -> Result<LangItems, String> {
    // Any checked file's program carries the same builtin defs (they are
    // stable path hashes); rebuild a throwaway store to read them.
    let builtins = crate::ty::GlobalTys::new().builtins();
    let mut items = LangItems::from_builtins(builtins);
    for &(fi, ref name, at) in marks {
        let file = &files[fi];
        let Some(item) = lang::lang_item_by_name(name) else {
            return Err(format!("lust std load failed: library/{}: unknown lang item `{name}`", file.rel));
        };
        let want_crate = lang::LANG_ITEMS[item as usize].krate;
        if want_crate != file.krate {
            return Err(format!(
                "lust std load failed: library/{}: lang item `{name}` belongs to crate `{}`, not `{}`",
                file.rel,
                want_crate.name(),
                file.krate.name()
            ));
        }
        if items.get(item).is_some() && !matches!(item, lang::LangItem::Option | lang::LangItem::String | lang::LangItem::Vec) {
            return Err(format!("lust std load failed: lang item `{name}` is marked more than once"));
        }
        // The marked item is the first item that starts at or after the
        // mark's next-line offset.
        let found = file.ast.items.iter().filter(|it| it.span.lo >= at).min_by_key(|it| it.span.lo);
        let Some(found) = found else {
            return Err(format!("lust std load failed: library/{}: #[lust_lang = \"{name}\"] has no item after it", file.rel));
        };
        let item_name = match &found.kind {
            ItemKind::Fn(d) => Some(d.name),
            ItemKind::Struct(s) => Some(s.name),
            ItemKind::Enum(e) => Some(e.name),
            _ => None,
        };
        let Some(item_name) = item_name else {
            return Err(format!(
                "lust std load failed: library/{}: #[lust_lang = \"{name}\"] marks an item kind that cannot be a lang item yet",
                file.rel
            ));
        };
        let ids = CrateIds { local: LOCAL_CRATE, stable: file.krate.stable_hash() };
        let known = Known::new(&file.interner);
        let program = collect::collect(&file.ast, &file.interner, &known, ids)
            .map_err(|ds| format!("lust std load failed: {}", ds.iter().map(|d| diag_line(file.rel, d)).collect::<Vec<_>>().join("; ")))?;
        let def = match &found.kind {
            ItemKind::Fn(_) => program.fn_names.get(&item_name).map(|&f| program.def_id(f)),
            _ => program.type_names.get(&item_name).map(|&a| program.def_of_adt(a)),
        };
        let Some(def) = def else {
            return Err(format!("lust std load failed: library/{}: lang item `{name}` def not found after collect", file.rel));
        };
        items.set(item, def);
    }
    let missing = items.required_missing();
    if !missing.is_empty() {
        let names: Vec<&str> = missing.iter().map(|i| lang::LANG_ITEMS[*i as usize].name).collect();
        return Err(format!("lust std load failed: required lang item(s) not resolved: {}", names.join(", ")));
    }
    Ok(items)
}

/// Builds splice text for every implemented `STD_FNS` row: finds the
/// row's fn in its checked shipped file, renames it to the row's
/// mangled name (by its recorded name span, so no other text moves),
/// and rejects a spliced file that defines anything the registry
/// does not name (a stray name could collide with user code).
fn build_splices(files: &[CheckedFile]) -> Result<(Vec<(ShippedCrate, String)>, Vec<&'static StdFnDef>), String> {
    let mut splices: Vec<(ShippedCrate, String)> = Vec::new();
    let mut spliced_files: Vec<&str> = Vec::new();
    let mut routed: Vec<&'static StdFnDef> = Vec::new();
    for def in lang::STD_FNS.iter().filter(|d| d.implemented) {
        let module = &def.path[1..def.path.len() - 1];
        let fname = def.path[def.path.len() - 1];
        let Some(file) = files.iter().find(|f| f.krate == def.krate && f.module == module) else {
            return Err(format!("lust std load failed: registry std fn `{}` has no shipped source file", def.path.join("::")));
        };
        // Every item in a spliced file must be a registry fn of this file.
        let mut renames: Vec<(u32, u32, &'static str)> = Vec::new();
        for it in &file.ast.items {
            let ItemKind::Fn(fd) = &it.kind else {
                return Err(format!(
                    "lust std load failed: library/{}: only registry std fns can ride in a spliced file in S5 (found a non-fn item)",
                    file.rel
                ));
            };
            let n = file.interner.get(fd.name);
            let row = lang::STD_FNS.iter().find(|d| {
                d.implemented && d.krate == file.krate && &d.path[1..d.path.len() - 1] == file.module && d.path[d.path.len() - 1] == n
            });
            let Some(row) = row else {
                return Err(format!("lust std load failed: library/{}: fn `{n}` is not in the STD_FNS registry", file.rel));
            };
            renames.push((fd.name_span.lo, fd.name_span.hi, row.mangled));
        }
        if !renames.iter().any(|(_, _, m)| *m == def.mangled) {
            return Err(format!(
                "lust std load failed: library/{}: registry std fn `{}` (`{fname}`) not found in source",
                file.rel,
                def.path.join("::")
            ));
        }
        routed.push(def);
        if spliced_files.contains(&file.rel) {
            continue; // This file's splice text is already built (same file, several fns).
        }
        spliced_files.push(file.rel);
        let mut text = file.clean.clone();
        renames.sort_by_key(|(lo, _, _)| std::cmp::Reverse(*lo));
        for (lo, hi, mangled) in renames {
            text.replace_range(lo as usize..hi as usize, mangled);
        }
        splices.push((file.krate, text));
    }
    Ok((splices, routed))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A reader over the real built-in library text, hermetic to env.
    fn builtin_reader() -> impl FnMut(&str) -> Result<String, String> {
        |rel| builtin_text(rel).map(str::to_string).ok_or_else(|| format!("no builtin {rel}"))
    }

    /// The shipped library loads: required lang items resolve, the exit
    /// fn is checked and renamed into the std splice.
    #[test]
    fn shipped_library_loads() {
        let load = load_std_from(&mut builtin_reader()).expect("shipped library must load");
        assert!(load.lang.required_missing().is_empty());
        assert_eq!(load.fns.len(), 1);
        assert_eq!(load.fns[0].path, ["std", "process", "exit"]);
        // The process fns, then one hidden module per std source module.
        assert_eq!(load.splices.len(), 1 + crate::stdmods::STD_MODULES.len());
        assert!(load.splices[1].1.starts_with("pub mod __lust_core_time {\n"));
        let (krate, text) = &load.splices[0];
        assert_eq!(*krate, ShippedCrate::Std);
        assert!(text.contains("fn __lust_std_process_exit(code: i32)"), "splice carries the mangled name:\n{text}");
        assert!(!text.contains("fn exit("), "the unmangled name must not ride in the splice");
        assert!(text.contains("core::intrinsics::exit(code)"), "the body still names the intrinsic");
    }

    /// A `#[lust_lang]` mark in shipped source resolves to the next
    /// item's def, and blanking the mark line keeps byte offsets exact.
    #[test]
    fn lang_mark_resolves() {
        let src = "#[lust_lang = \"phantom_data\"]\npub struct PhantomData;\n";
        let (clean, marks) = scan_lang_attrs(src, "core/src/lib.rs").unwrap();
        assert_eq!(clean.len(), src.len());
        assert_eq!(marks, vec![("phantom_data".to_string(), 30)]);
        let mut read = |rel: &str| -> Result<String, String> {
            if rel == "core/src/lib.rs" {
                Ok(src.to_string())
            } else {
                builtin_text(rel).map(str::to_string).ok_or_else(|| format!("no builtin {rel}"))
            }
        };
        let load = load_std_from(&mut read).expect("fixture library must load");
        assert!(load.lang.get(lang::LangItem::PhantomData).is_some(), "mark resolves to a def");
    }

    /// A malformed mark is an installation error, never a silent skip.
    #[test]
    fn bad_lang_mark_fails() {
        let err = scan_lang_attrs("#[lust_lang = \"Nope\"]\nfn f() {}\n", "core/src/lib.rs").unwrap_err();
        assert!(err.contains("bad #[lust_lang]"), "{err}");
    }

    /// Privilege is per registry row, in shipped source too: `std` may
    /// not call the bumpalo-only `arena_alloc` intrinsic.
    #[test]
    fn shipped_source_privilege_is_per_row() {
        let process = "pub fn exit(code: i32) -> ! {\n    core::intrinsics::arena_alloc(0, 1, 1);\n    core::intrinsics::exit(code)\n}\n";
        let mut read = |rel: &str| -> Result<String, String> {
            if rel == "std/src/process.rs" {
                Ok(process.to_string())
            } else {
                builtin_text(rel).map(str::to_string).ok_or_else(|| format!("no builtin {rel}"))
            }
        };
        let err = load_std_from(&mut read).map(|_| ()).unwrap_err();
        assert!(err.contains("L0642"), "want a privilege error, got: {err}");
    }

    /// A registry fn with no source body fails the load (the registry
    /// and the library must agree).
    #[test]
    fn missing_registry_fn_fails() {
        let mut read = |rel: &str| -> Result<String, String> {
            if rel == "std/src/process.rs" {
                Ok("// empty\n".to_string())
            } else {
                builtin_text(rel).map(str::to_string).ok_or_else(|| format!("no builtin {rel}"))
            }
        };
        let err = load_std_from(&mut read).map(|_| ()).unwrap_err();
        assert!(err.contains("std::process::exit"), "error names the missing fn: {err}");
    }
}
