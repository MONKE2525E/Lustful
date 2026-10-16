// What a fn signature delta does with each table of a kept `Program`
// (docs: /home/theo/lust-scratch/sigedit/PLAN.md, P2). The delta takes a
// collected program, swaps one fn's signature in with `install_fn`, and
// reruns the checks that read it; the result must equal a fresh collect
// of the edited Ast. Each field below names its rule:
//
// - same: no fn header can change it while the item outline stands
//   (names, types, impls, traits, consts other than `init_names`).
// - replace: `install_fn` rewrites the edited fn's entry in it.
// - rerun: a check or pass that reads it runs again for the edited fn.
// - refuse: an edit that could change it falls back to a full collect.
// - item: the item patch owns it (Ast, resolver tables).
//
// Completeness: `Program` and `GenTables` are destructured with no `..`,
// so a new field fails to compile here until it states its rule. The
// digest hashes the fields a signature delta writes or reads, so a cold
// collect before and after a refactor (LUST_PROGRAM_DIGEST) and a warm
// delta against a cold collect can be compared field by field.
use super::collect::Program;
use super::generics::GenTables;
use std::fmt::Write as _;
use std::hash::Hasher;

/// Feeds `Debug` text into a hasher without building the string.
struct HashWriter(std::collections::hash_map::DefaultHasher);

impl std::fmt::Write for HashWriter {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.0.write(s.as_bytes());
        Ok(())
    }
}

fn h(x: &dyn std::fmt::Debug) -> u64 {
    let mut w = HashWriter(Default::default());
    let _ = write!(w, "{x:?}");
    w.0.finish()
}

/// One hash per signature-relevant table of `p`, by field name. Type
/// ids are hashed as ids: two programs agree only when they interned
/// the same types in the same order (the bar for a cold refactor).
pub fn digest(p: &Program) -> Vec<(&'static str, u64)> {
    let Program {
        ast: _,                      // item
        interner: _,                 // item (append-only)
        known: _,                    // same
        tys: _,                      // append-only store; ids in the tables below
        defs,                        // replace (the fn's generics and sig)
        adts: _,                     // same
        fns,                         // replace
        consts: _,                   // refuse: a fn in `init_names` falls back
        const_names: _,              // same
        const_defs: _,               // same
        static_defs: _,              // same
        assoc_const_names: _,        // same
        impl_assoc_consts: _,        // same
        trait_assoc_const_values: _, // same
        statics: _,                  // refuse (`init_names`)
        static_names: _,             // same
        body_items,                  // same (nested fns are body edits)
        body_type_items: _,          // same
        item_blocks: _,              // same (spans move with prog_shift)
        body_consts: _,              // refuse (`init_names`)
        const_values,                // refuse (`init_names`)
        scope_of_stmt: _,            // same
        fn_siblings: _,              // same
        type_names: _,               // same
        drop_adts: _,                // same
        aliases: _,                  // same
        fn_names,                    // same (outline)
        methods,                     // same (outline)
        main,                        // refuse: main is never patched
        krate: _,                    // same
        stable_crate: _,             // same
        fn_defs,                     // same (the fn's hash stands)
        def_by_hash,                 // same
        std_fns: _,                  // same (std splice edits refuse)
        shipped_ranges: _,           // same
        resolved: _,                 // item
        gx,
        record_reads: _, // same
        unwind: _,       // same
        regions,         // replace (`fns`, `opaque_sigs`); rerun (outlives)
        fp_memo: _,      // the driver clears it
        impl_parents,    // same (impl headers stand)
    } = p;
    let fn_defs_data: Vec<_> = fn_defs.iter().map(|&d| defs.get(d)).collect();
    let mut out = vec![
        ("fns", h(fns)),
        ("fn_defs", h(fn_defs)),
        ("defs", h(&fn_defs_data)),
        ("def_by_hash", h(def_by_hash)),
        ("fn_names", h(fn_names)),
        ("methods", h(methods)),
        ("main", h(main)),
        ("body_items", h(body_items)),
        ("const_values", h(const_values)),
        ("impl_parents", h(&sorted(impl_parents.iter().map(|(k, v)| (*k, (&v.generics, &v.scope, v.impl_item)))))),
        ("region_fns", h(&sorted(regions.fns.iter()))),
        ("region_opaque_sigs", h(&sorted(regions.opaque_sigs.iter()))),
    ];
    gen_digest(gx, &mut out);
    out
}

/// A map's entries in a fixed order (by the key's `Debug` text), so the
/// hash does not depend on the map's insertion history.
fn sorted<K: std::fmt::Debug, V>(it: impl Iterator<Item = (K, V)>) -> Vec<(K, V)> {
    let mut v: Vec<(String, (K, V))> = it.map(|e| (format!("{:?}", e.0), e)).collect();
    v.sort_by(|a, b| a.0.cmp(&b.0));
    v.into_iter().map(|e| e.1).collect()
}

fn gen_digest(gx: &GenTables, out: &mut Vec<(&'static str, u64)>) {
    let GenTables {
        lang: _,                  // same
        index: _,                 // same: impl records do not hold fn sigs
        trait_names: _,           // same
        trait_scopes: _,          // same
        trait_methods: _,         // refuse: trait method decls are never patched
        lang_method_sigs: _,      // refuse: lang methods are never patched
        trait_assoc_defaults: _,  // same
        trait_unsafe: _,          // same
        trait_assoc_consts: _,    // same
        wf_headers: _,            // same (impl headers)
        adt_info: _,              // same
        adt_lifetimes: _,         // same
        generic_aliases: _,       // same
        adt_generics: _,          // same
        adt_envs: _,              // same
        adt_scopes: _,            // same
        adt_instance_of: _,       // rerun (materialize)
        fn_templates,             // replace
        fn_scopes,                // replace
        fn_class,                 // replace; the class must stand
        instances,                // rerun (materialize)
        closures: _,              // rerun (body checks)
        closure_fns: _,           // rerun (body checks)
        template_closures: _,     // rerun (template checks)
        template_calls: _,        // rerun (template checks)
        instance_by_key,          // rerun (materialize)
        inherent_methods,         // same (outline)
        prim_inherent_methods: _, // same (std splice)
        inherent_self_pats,       // same (impl headers)
        inherent_impl_self: _,    // same
        inherent_const_self: _,   // same
        assoc_const_tmpls: _,     // same
        traits_by_method: _,      // same
        drop_methods: _,          // same (trait impl methods refuse)
        glue_methods: _,          // same
        clone_from_methods: _,    // same
        pcmp_methods: _,          // same
        fmt_methods: _,           // same
        deferred_debug_fields: _, // same
        hasher_methods: _,        // same
        build_hashers: _,         // same
        iter_methods: _,          // same
        written_hash: _,          // same
        hash_impls: _,            // same
        borrow_impls: _,          // same
        has_generics,             // refuse: the fn class stands
        user_generics,            // refuse: the fn class stands
        cow_fns: _,               // refuse (the whole-Ast Cow scan)
        mono_counts,              // rerun (materialize)
        template_checks,          // rerun (materialize)
        trait_picks: _,           // rerun (body checks)
        trait_method_stubs: _,    // same
        walk_instances: _,        // same
        reuse: _,                 // the driver's cache
        dyn_infos: _,             // same (traits)
        vtables: _,               // rerun (materialize)
        vtable_by_key: _,         // rerun (materialize)
        dyn_inherent,             // same (impl headers)
        dyn_impl_sites: _,        // same
        static_dyn_impls: _,      // same
        static_dyn_fns,           // same (impl headers)
        mono_done: _,             // rerun
        inst_order: _,            // the driver's order
        template_rows: _,         // rerun
        adt_created: _,           // rerun (materialize)
        item_index: _,            // same
        param_defaults: _,        // same
        opaques,                  // replace
        opaque_ret_of,            // rerun (reveal)
        opaque_hidden,            // rerun (reveal)
    } = gx;
    out.extend([
        ("fn_templates", h(fn_templates)),
        ("fn_scopes", h(fn_scopes)),
        ("fn_class", h(fn_class)),
        ("instances", h(&sorted(instances.iter()))),
        ("instance_by_key", h(&sorted(instance_by_key.iter()))),
        ("inherent_methods", h(&sorted(inherent_methods.iter()))),
        ("inherent_self_pats", h(&sorted(inherent_self_pats.iter()))),
        ("has_generics", h(&(has_generics, user_generics))),
        ("mono_counts", h(mono_counts)),
        ("template_checks", h(&sorted(template_checks.iter()))),
        ("dyn_inherent", h(&sorted(dyn_inherent.iter()))),
        ("static_dyn_fns", h(static_dyn_fns)),
        ("opaques", h(&sorted(opaques.iter()))),
        ("opaque_ret_of", h(&sorted(opaque_ret_of.iter()))),
        ("opaque_hidden", h(&sorted(opaque_hidden.iter()))),
    ]);
}

/// Appends `p`'s digest to the file `LUST_PROGRAM_DIGEST` names, one
/// line per collect, when the variable is set (a test hook; see the
/// module docs).
pub fn dump_if_asked(p: &Program, errors: usize) {
    static PATH: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    let Some(path) = PATH.get_or_init(|| std::env::var("LUST_PROGRAM_DIGEST").ok()) else { return };
    let mut line = format!("errors={errors}");
    for (k, v) in digest(p) {
        let _ = write!(line, " {k}={v:016x}");
    }
    line.push('\n');
    use std::io::Write as _;
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
        let _ = f.write_all(line.as_bytes());
    }
}
