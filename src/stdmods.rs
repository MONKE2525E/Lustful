// Std source modules (W-STD-C): whole std modules written in lust source
// and spliced into a user compile as hidden inline modules.
//
// A row names one shipped file and the std paths that mean it
// (`std::time` and `core::time` for the time modules). When a compile can
// mention one (`needs`), the driver routes it through the resolver and
// the std loader appends `pub mod <name> { <file text> }` after the user
// text, in the shipped range of the row's crate. The resolver then
// (1) never binds `<name>` in the crate root, so user source cannot name
// it, and (2) walks `std::time` (and the other paths of the row) into
// that module. From there everything is the normal module machinery:
// imports, privacy, impls, generics, const items.
//
// Items in these modules are std items, not the user crate's: check
// treats their types as foreign for the orphan and inherent-impl rules
// and keeps layout queries off them (`Program::std_module_def`).

use crate::ty::lang::ShippedCrate;

/// One std module in source.
pub struct StdModule {
    /// The hidden module name in the splice (`__lust_` prefix). Only a
    /// module the splice defines is hidden; a user module of the same
    /// name stays a normal module.
    pub name: &'static str,
    /// The file under `library/`.
    pub rel: &'static str,
    /// The crate whose privileges the module has (intrinsics).
    pub krate: ShippedCrate,
    /// The std paths that walk into this module: (extern crate, module).
    pub paths: &'static [(&'static str, &'static str)],
    /// True when the module is the whole std module (`std::time`). An
    /// overlay (`std::marker`) holds only some items of a std module
    /// whose other items stay compiler-known: a path walks into it only
    /// when the overlay defines the next segment.
    pub full: bool,
    /// The words whose mention means a compile may need this module.
    pub triggers: &'static [&'static str],
}

/// The std modules in source, in splice order.
pub const STD_MODULES: &[StdModule] = &[
    StdModule {
        name: "__lust_core_time",
        rel: "core/src/time.rs",
        krate: ShippedCrate::Core,
        paths: &[("core", "time")],
        full: true,
        triggers: &["time"],
    },
    StdModule {
        name: "__lust_std_time",
        rel: "std/src/time.rs",
        krate: ShippedCrate::Std,
        paths: &[("std", "time")],
        full: true,
        triggers: &["time"],
    },
    StdModule {
        name: "__lust_core_marker",
        rel: "core/src/marker.rs",
        krate: ShippedCrate::Core,
        paths: &[("core", "marker"), ("std", "marker")],
        full: false,
        triggers: &["PhantomData"],
    },
    StdModule {
        name: "__lust_core_cell",
        rel: "core/src/cell.rs",
        krate: ShippedCrate::Core,
        paths: &[("core", "cell"), ("std", "cell")],
        full: false,
        triggers: &["OnceCell", "LazyCell"],
    },
    StdModule {
        name: "__lust_std_sync",
        rel: "std/src/sync.rs",
        krate: ShippedCrate::Std,
        paths: &[("std", "sync")],
        full: false,
        triggers: &["LazyLock"],
    },
    StdModule {
        name: "__lust_alloc_collections",
        rel: "alloc/src/collections.rs",
        krate: ShippedCrate::Alloc,
        paths: &[("alloc", "collections"), ("std", "collections")],
        full: false,
        triggers: &["BTreeMap", "BTreeSet", "VecDeque", "btree_map", "btree_set", "vec_deque"],
    },
];

/// The words whose mention means a compile may need the std modules.
fn trigger_words() -> impl Iterator<Item = &'static str> {
    STD_MODULES.iter().flat_map(|m| m.triggers.iter().copied())
}

/// True if `src` can mention a std source module: a row's trigger
/// (its module segment, or for an overlay the item names) appears as a
/// whole identifier-like word. A plain byte scan (it runs on every
/// compile); a hit only costs the splice, and a real use always names
/// a trigger.
pub fn needs(src: &str) -> bool {
    let b = src.as_bytes();
    let ident = |c: u8| c.is_ascii_alphanumeric() || c == b'_' || c >= 0x80;
    trigger_words().any(|w| {
        let mut from = 0;
        while let Some(at) = src[from..].find(w) {
            let lo = from + at;
            let hi = lo + w.len();
            if (lo == 0 || !ident(b[lo - 1])) && (hi == b.len() || !ident(b[hi])) {
                return true;
            }
            from = hi;
        }
        false
    })
}

/// The row whose hidden module has this name.
pub fn by_name(name: &str) -> Option<&'static StdModule> {
    STD_MODULES.iter().find(|m| m.name == name)
}

/// The std path (`std::time`) a hidden module stands for, for display.
pub fn display_path(name: &str) -> Option<String> {
    by_name(name).and_then(|m| m.paths.first()).map(|(k, seg)| format!("{k}::{seg}"))
}

/// The splice text of one module file: the file inside its hidden
/// module.
pub fn splice_text(m: &StdModule, text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 64);
    out.push_str("pub mod ");
    out.push_str(m.name);
    out.push_str(" {\n");
    out.push_str(text);
    if !text.ends_with('\n') {
        out.push('\n');
    }
    out.push_str("}\n");
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn needs_matches_whole_words_only() {
        assert!(needs("use std::time::Duration;"));
        assert!(needs("use std::{time};"));
        assert!(needs("fn f() { core::time::Duration::ZERO; }"));
        assert!(!needs("let runtime = 1; let times = 2; let timer = 3;"));
        assert!(!needs("fn main() {}"));
    }

    #[test]
    fn names_carry_the_prefix() {
        for m in STD_MODULES {
            assert!(m.name.starts_with("__lust_"));
            assert!(!m.paths.is_empty());
        }
        assert_eq!(display_path("__lust_std_time").as_deref(), Some("std::time"));
    }
}
