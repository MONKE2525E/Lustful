// Session state for the compile pipeline: everything an edit can reuse (the AST,
// per-function body hashes, generated C, glue, and object files). One session
// serves one crate under one selection: `lust daemon` keeps one session per
// `SessionKey` alive between requests (docs/ARCH.md section 1.8); a plain
// `lust check` uses a fresh session once. The pipeline itself is in compile.rs.
use crate::ast::Ast;
use crate::cgen::{FnOut, GlueSet};
use crate::def::{CrateIds, DiskDefId, LOCAL_CRATE, stable_crate_hash};
use crate::diag::SourceMap;
use crate::intern::{FxMap, Interner, Known};
use crate::lexer::Lexed;
use crate::protocol::SessionKey;
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
    /// Where each LocalDefId's definition lives: item index, and index inside an impl block.
    pub(crate) fn_loc: Vec<(usize, Option<usize>)>,
    /// Each LocalDefId's slot. A slot is a function's place in the final bin's one
    /// table; cached code, objects, and the C function table all use slots. Local
    /// ids shift when functions are added, slots do not: assignment is append-only.
    pub(crate) fn_slot: Vec<u32>,
    /// Slot by stable function identity. The key is the disk pair
    /// `(StableCrateHash, DefPathHash)` (docs/ARCH.md sections 1.7 and 4.2), never
    /// a `Sym` or a local id, so the same source gets the same slots in any
    /// session, in any interning order. `driver::graph::SlotManifest` is the
    /// manifest type over this map (S7); the encode/decode pair below fixes the
    /// persisted byte shape for today's non-generic keys.
    pub(crate) slot_of: FxMap<DiskDefId, u32>,
    /// Canonical def path text per slot key, for hash collision checks
    /// (src/def.rs). A key keeps the path that first claimed it; a different
    /// path under the same key is a collision.
    pub(crate) slot_paths: FxMap<DiskDefId, Box<str>>,
    /// How many `slot_of` entries the disk slot manifest already holds
    /// (loaded at session start, then every store). The manifest is
    /// rewritten only when assignment grows past this count.
    pub(crate) slot_manifest_stored: usize,
    /// Body hash per slot, at the last parse.
    pub(crate) slot_hash: Vec<u64>,
    /// Lexed and scanned chunks from the last request, reused when their text is unchanged.
    pub(crate) chunks: Vec<Chunk>,
    /// The source text of the last request, to find what an edit changed.
    pub(crate) src: String,
    /// The session's source map: each file's path and line index. One crate
    /// root file per session today, always `FileId(0)`; spans in the AST name it.
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
    /// The read set of the slot's last passing check (docs/ARCH.md
    /// section 8.2), stored with the result. On a signature-only edit the
    /// dirty walk (`Program::reads_dirty`) replays these reads against
    /// the new program; a body whose reads all still match is reused
    /// without a recheck. Session-local only (`Sym` and `DefId` keys are
    /// stable inside one session, never written to disk in this form).
    pub(crate) slot_reads: Vec<Option<crate::driver::graph::Reads>>,
    /// Slots each slot's generated C references (itself plus its `Fn` call
    /// targets), collected from the IR at codegen. A unit's used-slots
    /// hash (section 4.2) is computed over the union for its slots.
    pub(crate) slot_used: Vec<Vec<u32>>,
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
    /// The one crate selection this session serves. A request whose key does
    /// not match is a routing bug; compile rejects it instead of mixing state.
    pub(crate) key: SessionKey,
    pub(crate) front: Front,
    pub(crate) caches: Caches,
    /// The checked shipped std (S5), loaded at most once per session:
    /// std is immutable inside a session (docs/ARCH.md section 3.8).
    /// `None` until a request can mention a source std fn, so a session
    /// that never routes one never pays for the load.
    pub(crate) std_cache: Option<Result<std::sync::Arc<crate::stdload::StdLoad>, String>>,
    /// The disk cache (unit objects and the slot manifest), opened on the
    /// first compile. Opening hashes the tcc tree for the compiler id, so
    /// a session pays it once, not per request. `cache_tried` separates
    /// "not opened yet" from "cache is off".
    pub(crate) disk_cache: Option<crate::driver::cache::Cache>,
    pub(crate) cache_tried: bool,
}

impl Session {
    pub fn new(obj_dir: PathBuf, persistent: bool, key: SessionKey) -> Session {
        let interner = Interner::default();
        let known = Known::new(&interner);
        Session {
            key,
            front: Front {
                interner,
                known,
                ast: Ast::default(),
                env_hash: None,
                items: Vec::new(),
                fn_loc: Vec::new(),
                fn_slot: Vec::new(),
                slot_of: FxMap::default(),
                slot_paths: FxMap::default(),
                slot_manifest_stored: 0,
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
                slot_reads: Vec::new(),
                slot_used: Vec::new(),
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
            std_cache: None,
            disk_cache: None,
            cache_tried: false,
        }
    }
    pub fn obj_dir(&self) -> &Path {
        &self.caches.obj_dir
    }

    /// Both crate identities for stable defs: the session-local id (one crate
    /// per session today) and the stable hash over the key's package and
    /// target identity (docs/ARCH.md section 1.7 steps 1 and 2). Features and
    /// the target triple select the session; they are not part of def
    /// identity, matching section 1.8's split of SessionKey from the crate
    /// disambiguator.
    pub(crate) fn crate_ids(&self) -> CrateIds {
        let k = &self.key.krate;
        CrateIds { local: LOCAL_CRATE, stable: stable_crate_hash(&k.package_id, &k.target_kind, &k.target_name, k.test) }
    }
}

/// The slot manifest byte shape: magic, entry count, then one 20-byte
/// entry per slot (`DiskDefId` bytes + slot), sorted by slot. Only stable disk
/// pairs are stored, so a restarted daemon that loads these bytes recovers the
/// same slot assignment in any crate load or discovery order (docs/ARCH.md
/// sections 4.2 and 8.4). The in-memory manifest type is
/// `driver::graph::SlotManifest`; the bytes live in the disk cache
/// (`driver::cache::Cache::load_slot_manifest`).
const SLOT_MANIFEST_MAGIC: &[u8; 4] = b"LSS1";

/// Serializes a slot map. See `SLOT_MANIFEST_MAGIC`.
pub(crate) fn encode_slot_manifest(slot_of: &FxMap<DiskDefId, u32>) -> Vec<u8> {
    let mut entries: Vec<(u32, DiskDefId)> = slot_of.iter().map(|(k, &s)| (s, *k)).collect();
    entries.sort_unstable();
    let mut out = Vec::with_capacity(8 + entries.len() * 20);
    out.extend_from_slice(SLOT_MANIFEST_MAGIC);
    out.extend_from_slice(&(entries.len() as u32).to_le_bytes());
    for (slot, key) in entries {
        out.extend_from_slice(&key.to_bytes());
        out.extend_from_slice(&slot.to_le_bytes());
    }
    out
}

/// Reads bytes written by `encode_slot_manifest`. None on any shape error (bad
/// magic, a truncated or trailing byte, or one slot claimed twice), so a bad
/// file is a cache miss, never a wrong slot.
pub(crate) fn decode_slot_manifest(b: &[u8]) -> Option<FxMap<DiskDefId, u32>> {
    if b.get(..4)? != SLOT_MANIFEST_MAGIC {
        return None;
    }
    let n = u32::from_le_bytes(b.get(4..8)?.try_into().ok()?) as usize;
    if b.len() != 8 + n.checked_mul(20)? {
        return None;
    }
    let mut map = FxMap::default();
    let mut slots: Vec<u32> = Vec::with_capacity(n);
    for i in 0..n {
        let at = 8 + i * 20;
        let key = DiskDefId::from_bytes(&b[at..at + 16])?;
        let slot = u32::from_le_bytes(b[at + 16..at + 20].try_into().ok()?);
        if slots.contains(&slot) || map.insert(key, slot).is_some() {
            return None;
        }
        slots.push(slot);
    }
    Some(map)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::def::{DefPathHash, StableCrateHash};

    fn key(krate: u64, hash: u64) -> DiskDefId {
        DiskDefId { krate: StableCrateHash(krate), hash: DefPathHash(hash) }
    }

    /// The session key's stable crate hash matches the pre-S6 synthetic hash
    /// byte for byte (same package string, `bin` target, stem name, test
    /// flag), so slot identities for single-file programs do not move.
    /// Features select a session without changing def identity (section 1.8).
    #[test]
    fn session_key_keeps_the_synthetic_crate_hash() {
        let dir = PathBuf::from("/tmp/lust-session-test");
        for test in [false, true] {
            let key = SessionKey::synthetic(Path::new("/tmp/x/main.rs"), test);
            let s = Session::new(dir.clone(), false, key.clone());
            assert_eq!(s.crate_ids().stable, crate::def::synthetic_crate_hash("/tmp/x/main.rs", test));
            assert_eq!(s.key, key);
        }
        let mut key = SessionKey::synthetic(Path::new("/tmp/x/main.rs"), false);
        key.features = vec!["alpha".into()];
        let s = Session::new(dir, false, key);
        assert_eq!(s.crate_ids().stable, crate::def::synthetic_crate_hash("/tmp/x/main.rs", false), "features do not rename defs");
    }

    /// Serialize, then read back in a fresh map (a restarted daemon): every
    /// function keeps its slot, dead slots included, whatever order the map
    /// held its entries in.
    #[test]
    fn slot_manifest_round_trips() {
        let mut m = FxMap::default();
        m.insert(key(1, 10), 0);
        m.insert(key(1, 20), 1);
        m.insert(key(1, 30), 5);
        m.insert(key(2, 10), 3);
        let back = decode_slot_manifest(&encode_slot_manifest(&m)).unwrap();
        assert_eq!(back, m);
        let empty: FxMap<DiskDefId, u32> = FxMap::default();
        assert_eq!(decode_slot_manifest(&encode_slot_manifest(&empty)), Some(empty));
    }

    /// A bad manifest never decodes to wrong slots.
    #[test]
    fn slot_manifest_rejects_bad_bytes() {
        let mut m = FxMap::default();
        m.insert(key(1, 10), 0);
        let bytes = encode_slot_manifest(&m);
        assert_eq!(decode_slot_manifest(&bytes[..bytes.len() - 1]), None, "truncated");
        let mut tail = bytes.clone();
        tail.push(0);
        assert_eq!(decode_slot_manifest(&tail), None, "trailing byte");
        let mut wrong = bytes;
        wrong[0] = b'X';
        assert_eq!(decode_slot_manifest(&wrong), None, "magic");
    }
}
