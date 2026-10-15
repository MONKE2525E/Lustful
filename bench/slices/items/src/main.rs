//! slice-items <file.rs>: one line per removable item, `start end depth kind name`.
//! slice-items --tree <root.rs>: every file in the crate's module tree, one per line
//! (cfg is not evaluated: a file that exists is listed).
//! slice-items --bodies <file.rs>: every fn body (free fns, impl and trait methods),
//! `open_line open_col close_line close_col start_line` (1-based columns of the braces).
//!
//! bench/slices/prune.py removes the innermost item that holds a lust or
//! rustc error. Removable units: items at file level and inside inline
//! `mod` blocks, and the items of inherent impls. A trait impl, a trait,
//! and a fn are removed whole. `start` includes the item's attributes and
//! doc comments. Lines are 1-based and inclusive.

use proc_macro2::Span;
use std::path::{Path, PathBuf};
use syn::spanned::Spanned;
use syn::{ImplItem, Item};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() == 3 && args[1] == "--tree" {
        let root = Path::new(&args[2]).to_path_buf();
        let mut out = Vec::new();
        tree(&root, root.parent().unwrap().to_path_buf(), &mut out);
        for p in out {
            println!("{}", p.display());
        }
        return;
    }
    if args.len() == 3 && args[1] == "--bodies" {
        let file = parse(Path::new(&args[2]));
        let mut v = Bodies(String::new());
        syn::visit::visit_file(&mut v, &file);
        print!("{}", v.0);
        return;
    }
    let path = args.get(1).expect("usage: slice-items <file.rs> | --tree <root.rs> | --bodies <file.rs>");
    let file = parse(Path::new(path));
    let mut out = String::new();
    items(&file.items, 0, &mut out);
    print!("{out}");
}

fn parse(path: &Path) -> syn::File {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    match syn::parse_file(&text) {
        Ok(f) => f,
        Err(e) => {
            let at = e.span().start();
            eprintln!("parse error at {}:{}:{}: {e}", path.display(), at.line, at.column + 1);
            std::process::exit(2);
        }
    }
}

/// The `#[path = "..."]` value of a module, if any.
fn path_attr(attrs: &[syn::Attribute]) -> Option<String> {
    attrs.iter().find(|a| a.path().is_ident("path")).and_then(|a| match &a.meta {
        syn::Meta::NameValue(nv) => match &nv.value {
            syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(s), .. }) => Some(s.value()),
            _ => None,
        },
        _ => None,
    })
}

/// Adds `file` and every module file below it. `dir` is where its child `mod x;` files live.
fn tree(file: &Path, dir: PathBuf, out: &mut Vec<PathBuf>) {
    if out.iter().any(|p| p == file) {
        return;
    }
    out.push(file.to_path_buf());
    let parsed = parse(file);
    mods(&parsed.items, file, &dir, false, out);
}

/// `inline`: `list` is the body of an inline `mod m { .. }`. A `#[path]` there is relative to
/// `dir`; outside inline blocks it is relative to the directory of `file` (the Reference rule).
fn mods(list: &[Item], file: &Path, dir: &Path, inline: bool, out: &mut Vec<PathBuf>) {
    for it in list {
        let Item::Mod(m) = it else { continue };
        let name = m.ident.to_string();
        if let Some((_, inner)) = &m.content {
            let sub = match path_attr(&m.attrs) {
                Some(p) => dir.join(p),
                None => dir.join(&name),
            };
            mods(inner, file, &sub, true, out);
            continue;
        }
        if let Some(p) = path_attr(&m.attrs) {
            // A #[path] file owns its directory: its children sit next to it.
            let f = if inline { dir.join(p) } else { file.parent().unwrap().join(p) };
            if f.exists() {
                let d = f.parent().unwrap().to_path_buf();
                tree(&f, d, out);
            }
            continue;
        }
        let flat = dir.join(format!("{name}.rs"));
        let modrs = dir.join(&name).join("mod.rs");
        if flat.exists() {
            tree(&flat, dir.join(&name), out);
        } else if modrs.exists() {
            tree(&modrs, dir.join(&name), out);
        }
    }
}

/// First line of an item: its first attribute (doc comments are attributes) or the item.
fn start(attrs: &[syn::Attribute], item: Span) -> usize {
    attrs.iter().map(|a| a.span().start().line).chain([item.start().line]).min().unwrap()
}

fn emit(out: &mut String, start: usize, end: usize, depth: usize, kind: &str, name: &str) {
    out.push_str(&format!("{start} {end} {depth} {kind} {name}\n"));
}

fn items(list: &[Item], depth: usize, out: &mut String) {
    for it in list {
        let (attrs, kind, name): (&[syn::Attribute], &str, String) = match it {
            Item::Fn(f) => (&f.attrs, "fn", f.sig.ident.to_string()),
            Item::Struct(s) => (&s.attrs, "struct", s.ident.to_string()),
            Item::Enum(e) => (&e.attrs, "enum", e.ident.to_string()),
            Item::Union(u) => (&u.attrs, "union", u.ident.to_string()),
            Item::Trait(t) => (&t.attrs, "trait", t.ident.to_string()),
            Item::TraitAlias(t) => (&t.attrs, "trait", t.ident.to_string()),
            Item::Type(t) => (&t.attrs, "type", t.ident.to_string()),
            Item::Const(c) => (&c.attrs, "const", c.ident.to_string()),
            Item::Static(s) => (&s.attrs, "static", s.ident.to_string()),
            Item::Use(u) => (&u.attrs, "use", "-".into()),
            Item::Mod(m) => (&m.attrs, if m.content.is_some() { "mod" } else { "moddecl" }, m.ident.to_string()),
            Item::Impl(i) => (&i.attrs, if i.trait_.is_some() { "traitimpl" } else { "impl" }, "-".into()),
            Item::Macro(m) => (&m.attrs, "macro", m.ident.as_ref().map(|i| i.to_string()).unwrap_or("-".into())),
            Item::ExternCrate(e) => (&e.attrs, "extern", e.ident.to_string()),
            Item::ForeignMod(f) => (&f.attrs, "foreign", "-".into()),
            _ => (&[], "other", "-".into()),
        };
        let s = start(attrs, it.span());
        emit(out, s, it.span().end().line, depth, kind, &name);
        match it {
            Item::Mod(m) => {
                if let Some((_, inner)) = &m.content {
                    items(inner, depth + 1, out);
                }
            }
            Item::Impl(i) if i.trait_.is_none() => {
                for ii in &i.items {
                    let (attrs, kind, name): (&[syn::Attribute], &str, String) = match ii {
                        ImplItem::Fn(f) => (&f.attrs, "fn", f.sig.ident.to_string()),
                        ImplItem::Const(c) => (&c.attrs, "const", c.ident.to_string()),
                        ImplItem::Type(t) => (&t.attrs, "type", t.ident.to_string()),
                        ImplItem::Macro(m) => (&m.attrs, "macro", "-".into()),
                        _ => (&[], "other", "-".into()),
                    };
                    emit(out, start(attrs, ii.span()), ii.span().end().line, depth + 1, kind, &name);
                }
            }
            _ => {}
        }
    }
}

/// Collects fn bodies for `--bodies`: brace positions, and the fn's first line.
struct Bodies(String);

impl Bodies {
    fn body(&mut self, block: &syn::Block, start: usize) {
        let (o, c) = (block.brace_token.span.open().start(), block.brace_token.span.close().start());
        self.0.push_str(&format!("{} {} {} {} {start}\n", o.line, o.column + 1, c.line, c.column + 1));
    }
}

impl<'a> syn::visit::Visit<'a> for Bodies {
    fn visit_item_fn(&mut self, f: &'a syn::ItemFn) {
        self.body(&f.block, f.sig.span().start().line);
        syn::visit::visit_item_fn(self, f);
    }
    fn visit_impl_item_fn(&mut self, f: &'a syn::ImplItemFn) {
        self.body(&f.block, f.sig.span().start().line);
        syn::visit::visit_impl_item_fn(self, f);
    }
    fn visit_trait_item_fn(&mut self, f: &'a syn::TraitItemFn) {
        if let Some(b) = &f.default {
            self.body(b, f.sig.span().start().line);
        }
        syn::visit::visit_trait_item_fn(self, f);
    }
}
