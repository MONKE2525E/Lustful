// Release C names (`LUST_RELEASE_C=1` one-shot builds, driver/release_c.rs): the C a
// unit gets depends only on its own fns, so a content-keyed object cache can reuse it
// across commits, machines and CI runs. Dev builds and the daemon never set the context
// and print numbered names, as before:
//   fn bodies     f<slot>               -> f_<id>, extern, called directly
//   trampolines   tramp<slot>           -> tramp_<id>, extern
//   table calls   (CAST lust_fns[slot]) -> (CAST f_<id>), with the callee's prototype
//   fn pointers   lust_tramps[slot]     -> tramp_<id>
//   Adts          A<id> (rank by hash)  -> A<def hash> or A<instance key hash>
//   panic sites   slot << 40 | ...      -> lust_so_<id> << 40 | ..., the slot from the
//                                          location unit's side table
//   vtables       vt<slot>_<vtable id>  -> vt_<id>_<n>, n counted in the fn
// `<id>` is 16 hex digits of a hash of the fn's `DiskDefId` (def path plus instance
// args). Every name that leaves its fn (a callee, a fn pointer, a location slot) is
// recorded as an extern declaration the unit prints (`FnOut::externs`).
use super::*;
use std::cell::RefCell;
use std::sync::Arc;

/// The stable names of one program's release C.
pub struct Names {
    /// By slot: the fn's id (16 hex digits), None for a slot with no fn.
    pub fns: Vec<Option<String>>,
    /// By Adt id: the name after `A`/`N` (`d<def hash>` or `i<instance key hash>`).
    pub adts: Vec<String>,
    /// The slot of each fn id, built on first use (`slot_of_id`).
    pub by_id: std::sync::OnceLock<crate::intern::FxMap<String, u32>>,
}

/// The slot whose fn has id `id` (16 hex digits), in release C.
pub(crate) fn slot_of_id(id: &str) -> Option<u32> {
    CUR.with(|c| {
        let n = c.borrow();
        let n = n.as_ref()?;
        let map = n.by_id.get_or_init(|| n.fns.iter().enumerate().filter_map(|(s, id)| Some((id.clone()?, s as u32))).collect());
        map.get(id).copied()
    })
}

thread_local! {
    static CUR: RefCell<Option<Arc<Names>>> = const { RefCell::new(None) };
}

/// Runs `f` with `names` as this thread's naming context (None: numbered names).
pub fn with<R>(names: Option<&Arc<Names>>, f: impl FnOnce() -> R) -> R {
    let old = CUR.with(|c| c.replace(names.cloned()));
    let r = f();
    CUR.with(|c| *c.borrow_mut() = old);
    r
}

/// True while this thread emits release C.
pub(crate) fn release() -> bool {
    CUR.with(|c| c.borrow().is_some())
}

fn fn_id(slot: u32) -> Option<String> {
    CUR.with(|c| c.borrow().as_ref().map(|n| n.fns.get(slot as usize).cloned().flatten().unwrap_or_else(|| format!("dead{slot}"))))
}

/// `A<id>` for Adt `a`.
pub(crate) fn adt(a: AdtId) -> String {
    CUR.with(|c| match c.borrow().as_ref() {
        Some(n) => format!("A{}", n.adts.get(a.0 as usize).map_or("x", String::as_str)),
        None => format!("A{}", a.0),
    })
}

/// `N<id>` for the unsized Adt `a`.
pub(crate) fn unsized_adt(a: AdtId) -> String {
    CUR.with(|c| match c.borrow().as_ref() {
        Some(n) => format!("N{}", n.adts.get(a.0 as usize).map_or("x", String::as_str)),
        None => format!("N{}", a.0),
    })
}

/// The C name of the body of the fn in `slot`.
pub(crate) fn body(slot: u32) -> String {
    fn_id(slot).map_or_else(|| format!("f{slot}"), |id| format!("f_{id}"))
}

/// The fn id of `slot` in release C (None: numbered names or no fn). The slot's own
/// entry decides: an id is 16 hex digits and may start with `dead` like `fn_id`'s
/// placeholder for an empty slot.
pub(crate) fn fn_tag_opt(slot: u32) -> Option<String> {
    CUR.with(|c| c.borrow().as_ref().and_then(|n| n.fns.get(slot as usize).cloned().flatten()))
}

/// The C name of the trampoline of the fn in `slot`.
pub(crate) fn tramp(slot: u32) -> String {
    fn_id(slot).map_or_else(|| format!("tramp{slot}"), |id| format!("tramp_{id}"))
}

/// The part of a per-fn C name that names the fn in `slot`: the slot number, or its id
/// in release C (`lust_splitp_<tag>_<n>`, `stramp<tag>`, `vt<tag>_<n>`).
pub(crate) fn fn_tag(slot: u32) -> String {
    fn_id(slot).unwrap_or_else(|| slot.to_string())
}

/// The callee text for a call of fn `f` (in `slot`) through `cast` (`fn_ptr_cast`):
/// `(CAST lust_fns[slot])` numbered, `(CAST f_<id>)` in release C, which records the
/// callee's prototype in `externs`.
pub(crate) fn callee(p: &Program, f: LocalDefId, slot: u32, externs: &mut BTreeSet<String>) -> String {
    let cast = fn_ptr_cast(p, f);
    match fn_id(slot) {
        None => format!("({cast}lust_fns[{slot}])"),
        Some(id) => {
            externs.insert(format!("{};\n", fn_sig_named(p, f, &format!("f_{id}"))));
            format!("({cast}f_{id})")
        }
    }
}

/// A fn pointer value for fn `f`: `lust_tramps[slot]` numbered, its trampoline in release
/// C (prototype recorded in `externs`).
pub(crate) fn fn_value(p: &Program, f: LocalDefId, slot: u32, externs: &mut BTreeSet<String>) -> String {
    match fn_id(slot) {
        None => format!("lust_tramps[{slot}]"),
        Some(id) => {
            let t = trampoline(p, f, slot);
            if let Some(head) = t.split(" {").next() {
                externs.insert(format!("{};\n", head.strip_prefix("static ").unwrap_or(head)));
            }
            format!("(lust_fnptr)tramp_{id}")
        }
    }
}

/// A panic location of the fn in `slot`: the packed number numbered; in release C the
/// slot comes from the location unit's `lust_so_<id>` (recorded in `externs`), so the
/// text holds only the line within the fn and the column.
pub(crate) fn loc(slot: u32, rel: u64, col: u64, externs: &mut BTreeSet<String>) -> String {
    match fn_id(slot) {
        None => format!("{}u", ((slot as u64) << 40) | (rel << 20) | col),
        Some(id) => {
            externs.insert(format!("extern const uint32_t lust_so_{id};\n"));
            format!("(((uint64_t)lust_so_{id} << 40) | {}ull)", (rel << 20) | col)
        }
    }
}

/// The location unit of release C: `loc_unit`'s line and file tables plus a
/// `lust_so_<id>` per live fn (the slot its panic sites pack). The tables are indexed
/// canonically, a live fn by its rank by id and a file by its rank by path, so the unit
/// is a function of the program: the slot numbers and file ids a disk cache or a front
/// image carried over from earlier builds do not reach the binary.
pub(crate) fn loc_unit(live: &[u32], files: &SlotFiles, slot_lines: &[u32]) -> String {
    let mut fns: Vec<(String, u32)> = live.iter().filter_map(|&s| fn_id(s).map(|id| (id, s))).collect();
    fns.sort_unstable();
    let file_of = |s: u32| files.of_slot.get(s as usize).copied().unwrap_or(0) as usize;
    let mut paths: Vec<&str> = fns.iter().map(|&(_, s)| files.paths.get(file_of(s)).copied().unwrap_or("")).collect();
    paths.sort_unstable();
    paths.dedup();
    let of_slot: Vec<u32> = fns
        .iter()
        .map(|&(_, s)| paths.binary_search(&files.paths.get(file_of(s)).copied().unwrap_or("")).unwrap_or(0) as u32)
        .collect();
    let lines: Vec<u32> = fns.iter().map(|&(_, s)| slot_lines.get(s as usize).copied().unwrap_or(0)).collect();
    let mut c = super::loc_unit(&SlotFiles { paths: &paths, of_slot: &of_slot }, &lines);
    for (k, (id, _)) in fns.iter().enumerate() {
        c.push_str(&format!("const uint32_t lust_so_{id} = {k};\n"));
    }
    c
}

/// Release C glue: every glue definition lives in exactly one shard, and fn units hold
/// only prototypes (`GlueSet::shared` holds every key). Shards are content-defined
/// chunks of the keys in prototype order, cut by each key's prototype and definition size
/// (`cut_after`), so new glue changes only the shard it lands in. Each shard declares the
/// types (`Decls::OneStep`), prototypes (its keys' and their callees') and externs its
/// definitions need. Only the keys the fns in `out` reach (a dead slot's `FnOut` is empty),
/// as a cold build has them: a session's set also keeps keys no fn reaches now (stale since
/// a refresh, or left by a removed fn).
pub fn glue_shards(p: &Program, g: &GlueSet, out: &[FnOut], target: usize) -> Vec<String> {
    let live = g.closure(out.iter().flat_map(|o| o.glue.iter()));
    let mut keys: Vec<&(Glue, CTy)> = live.into_iter().filter(|k| g.def_map.contains_key(*k)).collect();
    keys.sort_by(|a, b| g.protos[*a].cmp(&g.protos[*b]));
    let mut shards: Vec<Vec<&(Glue, CTy)>> = Vec::new();
    let mut cur = Vec::new();
    for k in keys {
        cur.push(k);
        if cut_after(&g.protos[k], g.def_map[k].len(), target.max(1) as u64) {
            shards.push(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() {
        shards.push(cur);
    }
    // Each shard is its own unit: built in parallel (in order), each worker
    // under this thread's naming context, in one layout phase (the program is
    // frozen: a worker keeps its `c_layout` answers across its shards).
    let names = CUR.with(|c| c.borrow().clone());
    let tag = super::layout_phase();
    crate::pool::par_map(&shards, |keys| {
        super::in_layout_phase(tag, || with(names.as_ref(), || {
            let mut c = unit_header();
            if p.unwind_tables {
                c.push_str(noreturn_decls());
            }
            let mut types = HashSet::new();
            let mut protos: BTreeSet<&str> = BTreeSet::new();
            let mut externs: BTreeSet<&str> = BTreeSet::new();
            for k in keys {
                g.def_types(k, &mut types);
                protos.insert(&g.protos[*k]);
                for d in g.deps.get(*k).into_iter().flatten() {
                    collect_types(&d.1, &mut types);
                    protos.insert(&g.protos[d]);
                }
                externs.extend(g.externs.get(*k).into_iter().flatten().map(String::as_str));
            }
            type_decls_with(p, &mut c, &types, &HashSet::new(), Decls::OneStep, &HashSet::new());
            externs.into_iter().for_each(|e| c.push_str(e));
            protos.into_iter().for_each(|x| c.push_str(x));
            for k in keys {
                c.push_str(&g.def_map[*k]);
            }
            c
        }))
    })
}

/// Release C statics: the data of every static, with the types it names (the glue lives
/// in `glue_shards`).
pub fn statics_unit(p: &Program, g: &GlueSet) -> String {
    let mut c = unit_header();
    // Defined: what the data holds by value, and the promoted values it points at (each
    // has its own definition here). Another static, a fn or glue it points at needs only
    // a forward typedef, so the unit does not change when a type behind a pointer does.
    let mut held = Vec::new();
    let mut types = HashSet::new();
    let mut pointed = HashSet::new();
    let mut fns = Vec::new();
    for (_, st) in p.statics.iter().enumerate().filter(|&(i, _)| p.static_live(i)) {
        let t = cty(&p.tys, st.ty);
        by_value_deps(&t, &mut held);
        collect_types(&t, &mut pointed);
        collect_promoted(p, &st.value, &t, &mut types);
        const_fns(&st.value, &mut fns);
    }
    types.extend(held);
    // The data's fn pointers point at this unit's own copies of their trampolines
    // (`const_init`), which take and return the fns' values by value.
    for f in fns {
        let info = p.fn_info(LocalDefId(f));
        for &t in info.params.iter().chain([&info.ret]) {
            collect_types(&cty(&p.tys, t), &mut types);
        }
    }
    let data = static_defs(p, &g.slots);
    // Only the glue the data names (a vtable's drop entry, say): the unit must not
    // change when unrelated glue comes or goes.
    let named: HashSet<&str> = data.split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_')).collect();
    let mut protos: Vec<&String> = Vec::new();
    for (k, proto) in &g.protos {
        let name = proto.split('(').next().and_then(|h| h.rsplit(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_')).next()).unwrap_or("");
        if named.contains(name) {
            collect_types(&k.1, &mut pointed);
            protos.push(proto);
        }
    }
    protos.sort();
    pointed.retain(|t| !types.contains(t));
    type_decls_with(p, &mut c, &types, &pointed, Decls::ByValue, &HashSet::new());
    protos.into_iter().for_each(|x| c.push_str(x));
    c.push_str(&data);
    c
}

/// The fns whose pointers the constant `v` holds.
fn const_fns(v: &crate::ty::consteval::ConstValue, out: &mut Vec<u32>) {
    use crate::ty::consteval::ConstValue as CV;
    match v {
        CV::FnPtr(f) => out.push(*f),
        CV::Aggregate(vs) | CV::Variant(_, vs) => vs.iter().for_each(|x| const_fns(x, out)),
        CV::Repeat(x, _) | CV::Ref(x) => const_fns(x, out),
        _ => {}
    }
}

/// Whether a release C unit (or glue shard) ends after the fn (glue key) `id` of `size`
/// bytes: with odds size / `target`, so a unit holds about `target` bytes, decided by the
/// id and its own size only. A cut test that followed the program's mean size moved every
/// cut when glue or code anywhere moved the mean across a step.
pub fn cut_after(id: &str, size: usize, target: u64) -> bool {
    hash64(id) % target < size as u64
}

fn hash64(s: &str) -> u64 {
    let mut x = crate::intern::FxHasher::default();
    std::hash::Hash::hash(s, &mut x);
    std::hash::Hasher::finish(&x)
}
