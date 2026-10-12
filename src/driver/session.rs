// Session state for the compile pipeline: everything an edit can reuse (the AST,
// per-function body hashes, generated C, glue, and object files). `lust daemon` keeps
// one session per file alive between requests; a plain `lust check` uses a fresh
// session once. The pipeline itself is in compile.rs.
use crate::ast::Ast;
use crate::cgen::{FnOut, GlueSet};
use crate::diag::SourceMap;
use crate::intern::{FxMap, Interner, Known, Sym};
use crate::lexer::Lexed;
use crate::scan;
use std::path::{Path, PathBuf};

/// Parsed program state. Owned separately from the caches so both can be borrowed at once.
pub(crate) struct Front {
    pub(crate) interner: Interner,
    pub(crate) known: Known,
    pub(crate) ast: Ast,
    /// `None` until the first successful parse.
    pub(crate) env_hash: Option<u64>,
    /// Top-level items of the last parse (to see which items an edit changed).
    pub(crate) items: Vec<scan::ItemScan>,
    /// Where each FnId's definition lives: item index, and index inside an impl block.
    pub(crate) fn_loc: Vec<(usize, Option<usize>)>,
    /// Each FnId's slot. A slot is a function's stable identity across edits (FnIds shift when
    /// functions are added); cached code, objects, and the C function table all use slots.
    pub(crate) fn_slot: Vec<u32>,
    pub(crate) slot_of: FxMap<(Sym, Sym), u32>,
    /// Body hash per slot, at the last parse.
    pub(crate) slot_hash: Vec<u64>,
    /// Lexed and scanned chunks from the last request, reused when their text is unchanged.
    pub(crate) chunks: Vec<Chunk>,
    /// The source text of the last request, to find what an edit changed.
    pub(crate) src: String,
    /// The session's source map: each file's path and line index. One file per session
    /// today, always `FileId(0)`; spans in the AST name it.
    pub(crate) map: SourceMap,
    /// The chunk-boundary mask (see `split_items`). Fixed for the session, so boundaries are too.
    pub(crate) split_mask: Option<u64>,
}

pub(crate) struct Chunk {
    /// Byte range of the chunk in the current source.
    pub(crate) start: usize,
    pub(crate) text: String,
    pub(crate) lexed: Lexed,
    /// The `start` the tokens were lexed at. Token spans are absolute, so they are only exact
    /// while this equals `start`.
    pub(crate) lexed_start: usize,
    pub(crate) scan: scan::ChunkScan,
    /// This chunk's items in `front.ast.items`, or None if it has not been parsed yet.
    pub(crate) items: Option<std::ops::Range<usize>>,
}

/// Per-slot results and build state.
pub(crate) struct Caches {
    /// The last check of this function passed.
    pub(crate) ok: Vec<bool>,
    pub(crate) out: Vec<FnOut>,
    pub(crate) has_out: Vec<bool>,
    pub(crate) glue: GlueSet,
    /// Slots per function unit. Fixed until the next full rebuild, so units stay stable.
    pub(crate) per_unit: usize,
    /// Slot capacity of `lust_fns` in libbase.so, and how many function units it has.
    pub(crate) table_cap: usize,
    pub(crate) base_units: usize,
    /// Bumped on every base rebuild. Each base is a new file (libbase-<n>.so), so an executable
    /// built earlier keeps loading the base it was linked with, even after a later rebuild.
    /// `base_gens` holds the generations still on disk, oldest first. Old generations are
    /// deleted only when no known output file references them any more (see `base_still_used`),
    /// so live binaries keep working and the cache grows only with binaries that still exist.
    pub(crate) base_gen: u64,
    pub(crate) base_gens: std::collections::VecDeque<u64>,
    /// (generation, output file) for every executable linked against a base in this session.
    pub(crate) base_users: Vec<(u64, PathBuf)>,
    pub(crate) obj_dir: PathBuf,
    /// Units compiled into `obj_dir` with the current layout, and with which debug setting.
    pub(crate) objects: Option<bool>,
    /// A daemon session builds against libbase.so; a one-shot session links statically.
    pub(crate) persistent: bool,
    /// Units whose current code is in an overlay object, not in libbase.so.
    pub(crate) overlays: std::collections::BTreeSet<usize>,
}

pub struct Session {
    pub(crate) front: Front,
    pub(crate) caches: Caches,
}

impl Session {
    pub fn new(obj_dir: PathBuf, persistent: bool) -> Session {
        let interner = Interner::default();
        let known = Known::new(&interner);
        Session {
            front: Front {
                interner,
                known,
                ast: Ast::default(),
                env_hash: None,
                items: Vec::new(),
                fn_loc: Vec::new(),
                fn_slot: Vec::new(),
                slot_of: FxMap::default(),
                slot_hash: Vec::new(),
                chunks: Vec::new(),
                src: String::new(),
                map: SourceMap::default(),
                split_mask: None,
            },
            caches: Caches {
                ok: Vec::new(),
                out: Vec::new(),
                has_out: Vec::new(),
                glue: GlueSet::default(),
                per_unit: 16,
                table_cap: 0,
                base_units: 0,
                base_gen: 0,
                base_gens: std::collections::VecDeque::new(),
                base_users: Vec::new(),
                obj_dir,
                objects: None,
                persistent,
                overlays: Default::default(),
            },
        }
    }
    pub fn obj_dir(&self) -> &Path {
        &self.caches.obj_dir
    }
}
