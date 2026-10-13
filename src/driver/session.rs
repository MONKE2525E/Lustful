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
    /// Session-stable Adt and static numbering state, kept across
    /// requests and passed to every `collect` (see
    /// `collect::DefOrder`): a def keeps its session-local index
    /// when other defs are added or reordered, which is what lets
    /// cached outputs that carry those indices (`FnOut::types`,
    /// the glue set) survive such edits.
    pub(crate) def_order: crate::check::collect::DefOrder,
    /// How many `def_order` entries (Adts plus statics) the disk
    /// def-order file already holds. Like the slot manifest, the
    /// order is persisted so a restarted daemon numbers defs as
    /// the previous one did; a fresh numbering would sort added
    /// defs into the middle and move the indices disk objects
    /// were built under.
    pub(crate) def_order_stored: usize,
    /// True while `def_order` came from the disk file and has not
    /// yet been checked against a parsed crate. The first slot
    /// update drops a loaded order that names none of the crate's
    /// current defs (a stale file for a different def set) and
    /// numbers fresh; see `slot_update`.
    pub(crate) def_order_loaded: bool,
    /// The Adt index of every Adt def at the last parse, by def
    /// hash. The slot update compares the next parse's predicted
    /// indices against these: cached output is reusable only when
    /// every old def is still present at the same index.
    pub(crate) prev_adt_ids: FxMap<crate::def::DefPathHash, u32>,
    /// The static index of every top-level static at the last parse.
    pub(crate) prev_static_ids: FxMap<crate::def::DefPathHash, u32>,
    /// True when the last parse had a shape whose derived Adt
    /// indices (generic instances, nested statics) can shift when
    /// a def is added even though the defs in `prev_adt_ids` and
    /// `prev_static_ids` keep theirs. Growth is then not reusable.
    pub(crate) prev_order_fragile: bool,
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
    /// The unit size recorded in the disk slot manifest (loaded at
    /// session start, then every store; 0 = none recorded). A
    /// persistent session adopts it as `Caches::per_unit` so unit
    /// grouping, and therefore unit keys, survive a restart; a
    /// one-shot session only preserves it across its own stores.
    pub(crate) manifest_per_unit: u32,
    /// Body hash per slot, at the last parse.
    pub(crate) slot_hash: Vec<u64>,
    /// Fn head hash per slot (`ast_hash::fn_head_hash`), at the last
    /// parse. A slot whose head changed always rechecks: its body is
    /// checked against that head (parameter names and patterns bind
    /// the locals), which neither the body hash nor the caller-visible
    /// `Sig` fingerprint covers.
    pub(crate) slot_head: Vec<u64>,
    /// Lexed and scanned chunks from the last request, reused when their text is unchanged.
    pub(crate) chunks: Vec<Chunk>,
    /// The source text of the last request, to find what an edit changed.
    pub(crate) src: String,
    /// The session's source map: each file's path and line index. One crate
    /// root file per session today, always `FileId(0)`; spans in the AST name it.
    pub(crate) map: SourceMap,
    /// The chunk-boundary mask (see `split_items`). Fixed for the session, so boundaries are too.
    pub(crate) split_mask: Option<u64>,
    /// True while this session's front state was built by the resolver
    /// (W-RESOLVE): a merged multi-file AST the chunk path must never
    /// try to reuse. Routing itself follows the current text (see
    /// `compile`): when a request no longer routes to the resolver,
    /// the state is dropped and this flag clears with it.
    pub(crate) resolved_crate: bool,
    /// The Cargo-graph crate identity for the in-flight resolver
    /// compile, handed from `resolved_setup` to the shared tail for one
    /// request (taken there, so it never outlives its request).
    pub(crate) resolved_crate_ids: Option<CrateIds>,
    /// Per-file resolver front-end cache (raw and expanded token
    /// streams plus outlines), kept across requests in this crate
    /// session. Unused until the session first takes the resolver path.
    pub(crate) resolve_cache: crate::resolve::worklist::ResolveCache,
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
    /// Outside inputs this chunk's macro expansion read (included files
    /// with content hashes, env values; see `expand::Dep`). The chunk is
    /// dropped instead of reused when one changes (added for W-MACRO).
    pub(crate) expand_deps: Vec<crate::expand::Dep>,
}

/// Per-slot results and build state.
pub(crate) struct Caches {
    /// The last check of this function passed.
    pub(crate) ok: Vec<bool>,
    pub(crate) out: Vec<FnOut>,
    pub(crate) has_out: Vec<bool>,
    /// The read set of the slot's last passing check (docs/ARCH.md
    /// section 8.2), stored with the result. On later edits the dirty
    /// walk (`Program::reads_dirty`) replays these reads against the
    /// new program; a body whose reads all still match is reused
    /// without a recheck. Session-local only (`Sym` and `DefId` keys are
    /// stable inside one session, never written to disk in this form).
    pub(crate) slot_reads: Vec<Option<crate::driver::graph::Reads>>,
    /// Slots each slot's generated C references (itself plus its `Fn` call
    /// targets), collected from the IR at codegen. A unit's used-slots
    /// hash (section 4.2) is computed over the union for its slots.
    pub(crate) slot_used: Vec<Vec<u32>>,
    /// Per-slot instance fingerprint for unit keys: the IR
    /// fingerprint of the slot's lowered body (`ir_cache`), set
    /// exactly when its `FnOut` is. Stable across sessions and slot
    /// assignments (stable def identities, structural types, relative
    /// locations), so a unit's object key needs no C text: a slot
    /// change rekeys through the used-slots hash and the C is
    /// re-emitted from `slot_ir`.
    pub(crate) slot_fp: Vec<u64>,
    /// The cached IR body per slot, in the translatable form of
    /// `ir_cache::CachedBody`. Set when the slot's body is lowered;
    /// read when a slot renumber makes its C stale and the C must be
    /// re-emitted without a front-end redo.
    pub(crate) slot_ir: Vec<Option<super::ir_cache::CachedBody>>,
    pub(crate) glue: GlueSet,
    /// Fingerprint of the statics the last built glue unit was
    /// generated from (`graph::statics_fingerprint`). A build whose
    /// current statics differ must rebuild the glue unit, whatever
    /// edit mode the current request is in: a `check` request consumes
    /// the edit that moved a static's value (slot hashes advance), so
    /// the following `build` request sees no change to react to. This
    /// fingerprint is the built-state record that survives that gap.
    /// Zero means no build yet.
    pub(crate) statics_fp: u64,
    /// A compile since the last build saw a full-mode edit or a const
    /// fn edit, so derived glue text may be stale. Set by any compile
    /// (check requests included), cleared by the build that refreshes
    /// the glue. Same reason as `statics_fp`: the edit and the build
    /// that must react to it are usually different requests.
    pub(crate) glue_stale: bool,
    /// Slots per function unit. Chosen at a full rebuild and fixed
    /// until the next one, so units stay stable; a persistent
    /// session adopts the slot manifest's recorded value instead,
    /// so grouping also stays stable across restarts.
    pub(crate) per_unit: usize,
    /// Slot capacity of `lust_fns` in libbase.so, and how many function units it has.
    pub(crate) table_cap: usize,
    pub(crate) base_units: usize,
    /// Bumped on every base rebuild; used only for the rebuild's temp file name.
    /// Each finished base is renamed to an owner+content name (`libbase-<pid>-<hash>.so`)
    /// in `base_dir`, a persistent directory (the disk cache's `bases/`
    /// subdir), never in `obj_dir`: executables load the base by absolute
    /// rpath at run time, so it must outlive the daemon that built it,
    /// while `obj_dir` is per-daemon temp state the daemon deletes on
    /// exit. `base_files` holds the base file names this session put on
    /// disk, oldest first. Old bases are deleted only when no known
    /// output file references them any more (see `base_still_used` and
    /// the manifest sweep in compile.rs), so live binaries keep working.
    pub(crate) base_gen: u64,
    /// The current base's library name for the linker (`base-<pid>-<hash>`).
    pub(crate) base_name: String,
    /// The resolved persistent directory for base libraries. None until
    /// this session's first base build picks one (see `resolve_base_dir`).
    pub(crate) base_dir: Option<PathBuf>,
    /// True once this session swept dead entries from `base_dir`'s manifest.
    pub(crate) base_swept: bool,
    pub(crate) base_files: std::collections::VecDeque<String>,
    /// (base file name, output file) for every executable linked against a base in this session.
    pub(crate) base_users: Vec<(String, PathBuf)>,
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
                def_order: crate::check::collect::DefOrder::default(),
                def_order_stored: 0,
                def_order_loaded: false,
                prev_adt_ids: FxMap::default(),
                prev_static_ids: FxMap::default(),
                prev_order_fragile: false,
                items: Vec::new(),
                fn_loc: Vec::new(),
                fn_slot: Vec::new(),
                slot_of: FxMap::default(),
                slot_paths: FxMap::default(),
                slot_manifest_stored: 0,
                manifest_per_unit: 0,
                slot_hash: Vec::new(),
                slot_head: Vec::new(),
                chunks: Vec::new(),
                src: String::new(),
                map: SourceMap::default(),
                split_mask: None,
                resolved_crate: false,
                resolved_crate_ids: None,
                resolve_cache: crate::resolve::worklist::ResolveCache::new(),
            },
            caches: Caches {
                ok: Vec::new(),
                out: Vec::new(),
                has_out: Vec::new(),
                slot_reads: Vec::new(),
                slot_used: Vec::new(),
                slot_fp: Vec::new(),
                slot_ir: Vec::new(),
                glue: GlueSet::default(),
                statics_fp: 0,
                glue_stale: false,
                per_unit: 16,
                table_cap: 0,
                base_units: 0,
                base_gen: 0,
                base_name: String::new(),
                base_dir: None,
                base_swept: false,
                base_files: std::collections::VecDeque::new(),
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

    /// The persistent base library directory, once a base was built.
    pub fn base_dir(&self) -> Option<&Path> {
        self.caches.base_dir.as_deref()
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
/// entry per slot (`DiskDefId` bytes + slot), sorted by slot, then the
/// unit size (`Caches::per_unit`) the stored objects were grouped with
/// as a trailing u32 (0 = not recorded; files without the trailer,
/// written before it existed, still decode with 0). Only stable disk
/// pairs are stored, so a restarted daemon that loads these bytes recovers the
/// same slot assignment in any crate load or discovery order (docs/ARCH.md
/// sections 4.2 and 8.4). The unit size rides along because unit keys
/// depend on the grouping: a restarted daemon that regrouped by its
/// own fn count would orphan every stored object. The in-memory manifest type is
/// `driver::graph::SlotManifest`; the bytes live in the disk cache
/// (`driver::cache::Cache::load_slot_manifest`).
const SLOT_MANIFEST_MAGIC: &[u8; 4] = b"LSS1";

/// Serializes a slot map and its unit size. See `SLOT_MANIFEST_MAGIC`.
pub(crate) fn encode_slot_manifest(slot_of: &FxMap<DiskDefId, u32>, per_unit: u32) -> Vec<u8> {
    let mut entries: Vec<(u32, DiskDefId)> = slot_of.iter().map(|(k, &s)| (s, *k)).collect();
    entries.sort_unstable();
    let mut out = Vec::with_capacity(12 + entries.len() * 20);
    out.extend_from_slice(SLOT_MANIFEST_MAGIC);
    out.extend_from_slice(&(entries.len() as u32).to_le_bytes());
    for (slot, key) in entries {
        out.extend_from_slice(&key.to_bytes());
        out.extend_from_slice(&slot.to_le_bytes());
    }
    out.extend_from_slice(&per_unit.to_le_bytes());
    out
}

/// The def-order file byte shape: magic, the stable crate hash the
/// hashes were numbered under, Adt count, static count, then each
/// def hash in order (Adts first). Only stable def hashes are
/// stored (each already mixes in the stable crate hash), so a
/// restarted daemon recovers the same Adt and static numbering
/// (see `collect::DefOrder`). The stored crate hash lets a reader
/// reject a file written for a different crate identity instead of
/// numbering this crate's defs by a foreign order.
const DEF_ORDER_MAGIC: &[u8; 4] = b"LSDO";

/// Serializes a def order. See `DEF_ORDER_MAGIC`.
pub(crate) fn encode_def_order(order: &crate::check::collect::DefOrder, stable: crate::def::StableCrateHash) -> Vec<u8> {
    let mut out = Vec::with_capacity(20 + (order.adts.len() + order.statics.len()) * 8);
    out.extend_from_slice(DEF_ORDER_MAGIC);
    out.extend_from_slice(&stable.0.to_le_bytes());
    out.extend_from_slice(&(order.adts.len() as u32).to_le_bytes());
    out.extend_from_slice(&(order.statics.len() as u32).to_le_bytes());
    for h in order.adts.iter().chain(&order.statics) {
        out.extend_from_slice(&h.0.to_le_bytes());
    }
    out
}

/// Reads bytes written by `encode_def_order`. None on any shape
/// error, on a stable crate hash other than `stable`, or on a hash
/// listed twice (in one list, or as both an Adt and a static), so
/// a bad or stale file is a cache miss and the caller numbers defs
/// fresh, never by a wrong order.
pub(crate) fn decode_def_order(b: &[u8], stable: crate::def::StableCrateHash) -> Option<crate::check::collect::DefOrder> {
    if b.get(..4)? != DEF_ORDER_MAGIC {
        return None;
    }
    if u64::from_le_bytes(b.get(4..12)?.try_into().ok()?) != stable.0 {
        return None;
    }
    let na = u32::from_le_bytes(b.get(12..16)?.try_into().ok()?) as usize;
    let ns = u32::from_le_bytes(b.get(16..20)?.try_into().ok()?) as usize;
    let n = na.checked_add(ns)?;
    if b.len() != n.checked_mul(8)?.checked_add(20)? {
        return None;
    }
    let mut order = crate::check::collect::DefOrder::default();
    for i in 0..n {
        let at = 20 + i * 8;
        let h = crate::def::DefPathHash(u64::from_le_bytes(b[at..at + 8].try_into().ok()?));
        if order.adts.contains(&h) || order.statics.contains(&h) {
            return None;
        }
        if i < na { &mut order.adts } else { &mut order.statics }.push(h);
    }
    Some(order)
}

/// Reads bytes written by `encode_slot_manifest`: the slot map and
/// the stored unit size (0 when the file predates the trailer).
/// None on any shape error (bad magic, a truncated or trailing
/// byte, one slot claimed twice, or an implausible unit size), so
/// a bad file is a cache miss, never a wrong slot.
pub(crate) fn decode_slot_manifest(b: &[u8]) -> Option<(FxMap<DiskDefId, u32>, u32)> {
    if b.get(..4)? != SLOT_MANIFEST_MAGIC {
        return None;
    }
    let n = u32::from_le_bytes(b.get(4..8)?.try_into().ok()?) as usize;
    let body = n.checked_mul(20)?.checked_add(8)?;
    let per_unit = if b.len() == body {
        0
    } else if b.len() == body.checked_add(4)? {
        let pu = u32::from_le_bytes(b[body..body + 4].try_into().ok()?);
        if pu > 4096 {
            return None;
        }
        pu
    } else {
        return None;
    };
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
    Some((map, per_unit))
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
        let back = decode_slot_manifest(&encode_slot_manifest(&m, 18)).unwrap();
        assert_eq!(back, (m.clone(), 18), "slots and unit size round-trip");
        // A pre-trailer file (no unit size recorded) still decodes.
        let mut old = encode_slot_manifest(&m, 18);
        old.truncate(old.len() - 4);
        assert_eq!(decode_slot_manifest(&old), Some((m, 0)), "old shape keeps its slots");
        let empty: FxMap<DiskDefId, u32> = FxMap::default();
        assert_eq!(decode_slot_manifest(&encode_slot_manifest(&empty, 0)), Some((empty, 0)));
    }

    /// The def order round-trips (a restarted daemon numbers defs
    /// as the previous one did), and bad bytes decode to None, so
    /// the caller falls back to a fresh numbering.
    #[test]
    fn def_order_round_trips_and_rejects_bad_bytes() {
        let stable = StableCrateHash(42);
        let mut order = crate::check::collect::DefOrder::default();
        order.adts = vec![DefPathHash(30), DefPathHash(10), DefPathHash(20)];
        order.statics = vec![DefPathHash(7), DefPathHash(9)];
        let bytes = encode_def_order(&order, stable);
        let back = decode_def_order(&bytes, stable).unwrap();
        assert_eq!(back.adts, order.adts);
        assert_eq!(back.statics, order.statics);
        // Every prefix and a trailing byte are shape errors.
        for cut in 0..bytes.len() {
            assert!(decode_def_order(&bytes[..cut], stable).is_none(), "prefix {cut}");
        }
        let mut tail = bytes.clone();
        tail.push(0);
        assert!(decode_def_order(&tail, stable).is_none(), "trailing byte");
        // A file for a different crate identity is not trusted.
        assert!(decode_def_order(&bytes, StableCrateHash(43)).is_none(), "other crate");
        let mut wrong = bytes.clone();
        wrong[0] = b'X';
        assert!(decode_def_order(&wrong, stable).is_none(), "magic");
        // A hash listed twice is bad, in one list or across both.
        let mut dup = encode_def_order(&order, stable);
        dup[20..28].copy_from_slice(&20u64.to_le_bytes());
        assert!(decode_def_order(&dup, stable).is_none(), "duplicate hash");
        order.statics = vec![DefPathHash(30)];
        assert!(decode_def_order(&encode_def_order(&order, stable), stable).is_none(), "hash in both lists");
    }

    /// A bad manifest never decodes to wrong slots.
    #[test]
    fn slot_manifest_rejects_bad_bytes() {
        let mut m = FxMap::default();
        m.insert(key(1, 10), 0);
        let bytes = encode_slot_manifest(&m, 16);
        assert_eq!(decode_slot_manifest(&bytes[..bytes.len() - 1]), None, "truncated");
        let mut tail = bytes.clone();
        tail.push(0);
        assert_eq!(decode_slot_manifest(&tail), None, "trailing byte");
        let mut wrong = bytes;
        wrong[0] = b'X';
        assert_eq!(decode_slot_manifest(&wrong), None, "magic");
    }
}
