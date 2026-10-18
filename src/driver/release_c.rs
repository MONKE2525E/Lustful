// Release C (`LUST_RELEASE_C=1`, `lust build`): C whose units depend only on their own
// fns, so a content-keyed object cache (key = a unit's C text plus the C compiler, its
// flags and the target) reuses every unit a commit did not touch, across commits,
// machines and CI runs. A one-shot build writes it, and so does a persistent session (a
// front image, src/image.rs) for the release driver: its units are a one-shot build's,
// byte for byte, as every name and unit follows from identities and content (the
// location unit numbers fns by id, `names::loc_unit`, and the glue shards hold what the
// live fns reach, `names::glue_shards`). Dev builds through tcc in a persistent session (the
// daemon) keep numbered names and byte groups (their overlays need the fn table).
//   names      cgen/names.rs: content-addressed fn, Adt and vtable names, direct calls,
//              panic locations through the location unit's slot table
//   partition  `groups`: a fn's unit follows from its own identity: its source file
//              (an instance: its generic fn's file), and inside a big file a
//              content-defined chunk: fns in source order, a cut after each fn whose id
//              hash hits 1 in (target bytes / mean fn bytes). Adding a fn moves no other
//              fn; a cut moves only when the fn that makes it goes.
use crate::cgen::{self, FnOut};
use crate::check::collect::{LocalDefId, Program};
use std::sync::Arc;

/// True when a build writes release C: `LUST_RELEASE_C` set, for a one-shot build or
/// a release driver build (`cc`) of a persistent session.
pub fn on(persistent: bool, cc: bool) -> bool {
    (!persistent || cc) && std::env::var_os("LUST_RELEASE_C").is_some_and(|v| !v.is_empty() && v != "0")
}

/// What decides a slot's C besides its program: release C or not, debug info, unwind
/// tables, and the switches of the release backends and of drop elaboration
/// (`LUST_DROPFLAGS`). A persistent session makes every slot's C again when it moves.
pub fn codegen_key(release: bool, debug: bool, unwind_tables: bool) -> u64 {
    let mut vars: Vec<(String, String)> = std::env::vars()
        .filter(|(k, _)| k.starts_with("LUST_RELEASE_") || k.starts_with("LUST_LL_") || k == "LUST_DROPFLAGS")
        .collect();
    vars.sort();
    let mut x = crate::intern::FxHasher::default();
    std::hash::Hash::hash(&(release, debug, unwind_tables, vars), &mut x);
    std::hash::Hasher::finish(&x)
}

fn hash64(s: &str) -> u64 {
    let mut x = crate::intern::FxHasher::default();
    std::hash::Hash::hash(s, &mut x);
    std::hash::Hasher::finish(&x)
}

/// The stable names of `program`'s release C: each slot's fn by a hash of its
/// `DiskDefId`, each Adt by its def hash (`d`) or instance key hash (`i`).
pub fn names(program: &Program, fn_slot: &[u32], n_slots: usize, inst_adts: &[(u32, u64)]) -> Arc<cgen::names::Names> {
    let mut fns = vec![None; n_slots];
    for (i, &slot) in fn_slot.iter().enumerate().take(program.fns.len()) {
        let d = program.disk_id(LocalDefId(i as u32));
        if let Some(x) = fns.get_mut(slot as usize) {
            *x = Some(format!("{:016x}", hash64(&format!("{:016x}{:016x}", d.krate.0, d.hash.0))));
        }
    }
    let inst: crate::intern::FxMap<u32, u64> = inst_adts.iter().copied().collect();
    let adts = (0..program.adts.len())
        .map(|a| match (inst.get(&(a as u32)), program.defs.def_of_adt(crate::ty::AdtId(a as u32))) {
            (Some(k), _) => format!("i{k:016x}"),
            (None, Some(d)) => format!("d{:016x}", d.hash.0),
            (None, None) => format!("x{a}"),
        })
        .collect();
    Arc::new(cgen::names::Names { fns, adts, by_id: Default::default() })
}

/// The release fn units: (registration fn name, slots in unit order), in a stable
/// order. `file` and `line` give each slot's source file and line (an instance: its
/// generic fn's). Chunks aim at `unit_bytes` of fn code.
/// The target size of a release C unit in bytes of fn or glue code (`LUST_RELEASE_UNIT_KB`,
/// default 128).
pub fn unit_bytes() -> usize {
    std::env::var("LUST_RELEASE_UNIT_KB").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(128) * 1024
}

pub fn groups(out: &[FnOut], names: &cgen::names::Names, file: &[String], line: &[u32]) -> Vec<(String, Vec<usize>)> {
    let live: Vec<usize> = (0..out.len()).filter(|&s| !out[s].code.is_empty()).collect();
    // A fn's size: its C; with the LLVM backend its statement count (`FnOut::ll_cost`) at
    // 200 bytes each, which no lowering, fact or ABI choice moves, so every such variant
    // gets the same units (and about as many as C).
    let llvm = live.iter().any(|&s| !out[s].ll.is_empty());
    let size = |s: usize| if llvm { out[s].ll_cost as usize * 200 } else { out[s].code.len() };
    let target = unit_bytes().max(1) as u64;
    let id = |s: usize| names.fns.get(s).and_then(|x| x.clone()).unwrap_or_else(|| format!("dead{s}"));
    let mut by_file: std::collections::BTreeMap<&str, Vec<(u32, String, usize)>> = Default::default();
    for &s in &live {
        by_file.entry(file.get(s).map_or("", String::as_str)).or_default().push((line.get(s).copied().unwrap_or(0), id(s), s));
    }
    let mut groups: Vec<Vec<(String, usize)>> = Vec::new();
    for (_, mut fns) in by_file {
        // Source order: an edit in one region of a file touches few chunks.
        fns.sort();
        let mut cur: Vec<(String, usize)> = Vec::new();
        for (_, n, s) in fns {
            let cut = cgen::names::cut_after(&n, size(s), target);
            cur.push((n, s));
            if cut {
                groups.push(std::mem::take(&mut cur));
            }
        }
        if !cur.is_empty() {
            groups.push(cur);
        }
    }
    groups
        .into_iter()
        .map(|g| {
            let ids: Vec<&str> = g.iter().map(|(n, _)| n.as_str()).collect();
            (format!("lust_register_g{:016x}", hash64(&ids.join(","))), g.into_iter().map(|(_, s)| s).collect())
        })
        .collect()
}

/// The table unit of release C: the fn tables stay declared (the runtime header names
/// them) but hold nothing, and `lust_base_init` runs each unit's registration (only
/// main's unit sets anything).
pub fn table_unit(registers: &[String]) -> String {
    let mut c = cgen::unit_header();
    c.push_str("lust_fnptr lust_fns[1];\nlust_fnptr lust_tramps[1];\nint (*lust_main_entry_p)(void);\n");
    let mut regs: Vec<&String> = registers.iter().collect();
    regs.sort();
    for r in &regs {
        c.push_str(&format!("void {r}(void);\n"));
    }
    c.push_str("void lust_base_init(void) {\n");
    for r in &regs {
        c.push_str(&format!("  {r}();\n"));
    }
    c.push_str("}\n");
    c
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `n` fns in one file, slot `s` on line `10 * s` with `size` bytes of code each.
    fn program(n: usize, size: usize) -> (Vec<FnOut>, cgen::names::Names, Vec<String>, Vec<u32>) {
        let out = (0..n).map(|_| FnOut { code: "x".repeat(size), ..Default::default() }).collect();
        let names = cgen::names::Names {
            fns: (0..n).map(|s| Some(format!("{:016x}", hash64(&format!("fn{s}"))))).collect(),
            adts: Vec::new(),
            by_id: Default::default(),
        };
        (out, names, vec!["src/a.rs".to_string(); n], (0..n as u32).map(|s| 10 * s).collect())
    }

    /// The units as sets of fn ids, so two programs with other slot numbers compare.
    fn unit_ids(out: &[FnOut], names: &cgen::names::Names, file: &[String], line: &[u32]) -> Vec<Vec<String>> {
        groups(out, names, file, line).into_iter().map(|(_, g)| g.into_iter().map(|s| names.fns[s].clone().unwrap()).collect()).collect()
    }

    /// A fn's unit follows from its own identity, size and source order: inserting a fn
    /// (here 12x the others' size) in the middle of a file changes only the unit it joins,
    /// and every other unit keeps its fns (and so its registration name).
    #[test]
    fn inserting_a_fn_moves_no_other_unit() {
        let (out, names, file, line) = program(400, 4096);
        let before = unit_ids(&out, &names, &file, &line);
        assert!(before.len() > 4, "a 1.6 MB file splits into several units: {}", before.len());
        // A new fn (slot 400) on line 1995, between slots 199 and 200.
        let (mut out2, mut names2, mut file2, mut line2) = (out, names, file, line);
        out2.push(FnOut { code: "y".repeat(50_000), ..Default::default() });
        names2.fns.push(Some(format!("{:016x}", hash64("new fn"))));
        file2.push("src/a.rs".to_string());
        line2.push(1995);
        let after = unit_ids(&out2, &names2, &file2, &line2);
        let lost = before.iter().filter(|u| !after.contains(u)).count();
        let new = after.iter().filter(|u| !before.contains(u)).count();
        assert_eq!(lost, 1, "only the unit the fn joins changes");
        assert!(new <= 2, "it comes back as one unit, or two when the new fn makes a cut: {new}");
    }
}
