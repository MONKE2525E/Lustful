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

/// The fn id of `slot` in release C (None: numbered names or no fn).
pub(crate) fn fn_tag_opt(slot: u32) -> Option<String> {
    fn_id(slot).filter(|id| !id.starts_with("dead"))
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

/// The location unit's slot table for release C: `lust_so_<id>` per live fn.
pub(crate) fn slot_table(live: impl Iterator<Item = u32>) -> String {
    let mut defs: Vec<String> = live.filter_map(|s| fn_id(s).map(|id| format!("const uint32_t lust_so_{id} = {s};\n"))).collect();
    defs.sort();
    defs.concat()
}

/// Release C glue: every glue definition lives in exactly one shard, and fn units hold
/// only prototypes (`GlueSet::shared` holds every key). Shards are content-defined
/// chunks of the keys in prototype order: a cut after each key whose prototype hash
/// hits 1 in (`target` bytes / mean definition bytes), so new glue changes only the
/// shard it lands in. Each shard declares the types (`Decls::OneStep`), prototypes (its
/// keys' and their callees') and externs its definitions need.
pub fn glue_shards(p: &Program, g: &GlueSet, target: usize) -> Vec<String> {
    let mut keys: Vec<&(Glue, CTy)> = g.def_map.keys().collect();
    keys.sort_by(|a, b| g.protos[*a].cmp(&g.protos[*b]));
    let mean = (keys.iter().map(|k| g.def_map[*k].len()).sum::<usize>() / keys.len().max(1)).max(1);
    let cut_every = (target / mean).max(1) as u64;
    let mut shards: Vec<Vec<&(Glue, CTy)>> = Vec::new();
    let mut cur = Vec::new();
    for k in keys {
        cur.push(k);
        if hash64(&g.protos[k]).is_multiple_of(cut_every) {
            shards.push(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() {
        shards.push(cur);
    }
    // Each shard is its own unit: built in parallel (in order), each worker
    // under this thread's naming context.
    let names = CUR.with(|c| c.borrow().clone());
    crate::pool::par_map(&shards, |keys| {
        with(names.as_ref(), || {
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
            type_decls_with(p, &mut c, &types, &HashSet::new(), Decls::OneStep);
            externs.into_iter().for_each(|e| c.push_str(e));
            protos.into_iter().for_each(|x| c.push_str(x));
            for k in keys {
                c.push_str(&g.def_map[*k]);
            }
            c
        })
    })
}

/// Release C statics: the data of every static, with the types it names (the glue lives
/// in `glue_shards`).
pub fn statics_unit(p: &Program, g: &GlueSet) -> String {
    let mut c = unit_header();
    let mut types = HashSet::new();
    for st in &p.statics {
        let t = cty(&p.tys, st.ty);
        collect_types(&t, &mut types);
        collect_promoted(p, &st.value, &t, &mut types);
    }
    let data = static_defs(p, &g.slots);
    // Only the glue the data names (a vtable's drop entry, say): the unit must not
    // change when unrelated glue comes or goes.
    let named: HashSet<&str> = data.split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_')).collect();
    let mut protos: Vec<&String> = Vec::new();
    for (k, proto) in &g.protos {
        let name = proto.split('(').next().and_then(|h| h.rsplit(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_')).next()).unwrap_or("");
        if named.contains(name) {
            collect_types(&k.1, &mut types);
            protos.push(proto);
        }
    }
    protos.sort();
    type_decls(p, &mut c, &types);
    protos.into_iter().for_each(|x| c.push_str(x));
    c.push_str(&data);
    c
}

fn hash64(s: &str) -> u64 {
    let mut x = crate::intern::FxHasher::default();
    std::hash::Hash::hash(s, &mut x);
    std::hash::Hasher::finish(&x)
}
