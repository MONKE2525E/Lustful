// Which const fns a const evaluation may run (W-PATCH-MISS2). A const fn
// body edit moves nothing outside the fn's own check unless an evaluator
// runs that body: collect's (const and static values, array lengths,
// discriminants, const generic arguments) or a body check's (`const`
// blocks, array repeat lengths, const generic arguments in a body). Every
// evaluator starts from one of those expressions and runs a const fn only
// through a call that names it, so a closure over names bounds what it can
// reach: start from every identifier in those places
// (`ast_hash::const_idents`), then add the body identifiers of each const
// fn whose name is in the set, until nothing changes. A const fn whose name
// is not in the set runs in no evaluator, so an edit of its body is a plain
// body edit (`patch::apply`). Names, not defs: a collision only costs the
// fast path. No evaluator runs a method with a `self` parameter (each
// answers it as outside the bound), so those never count as reached.
//
// The set lives in the patch base and only grows: each patch adds what its
// new nodes and its edited const fns can reach, and never removes what an
// old body could (a superset stays sound). A full resolve drops it with the
// base. The one evaluator start outside these places, a `thread_local!`
// `const { .. }` initializer (its block is a plain fn's body), records a
// `Checked` read; the driver finds those readers by their reads.
use super::compile::fn_def_at;
use super::session::Front;
use crate::intern::{FxHasher, Sym};
use std::collections::HashSet;
use std::hash::BuildHasherDefault;

type FxSet<T> = HashSet<T, BuildHasherDefault<FxHasher>>;

pub(crate) struct ConstReach {
    names: FxSet<Sym>,
    /// Expression, type, and pattern arena lengths already scanned.
    seen: (usize, usize, usize),
    /// The const fns (`Front::fn_loc` index, name), and whether each one's
    /// body identifiers joined `names`.
    consts: Vec<(usize, Sym)>,
    expanded: Vec<bool>,
}

impl ConstReach {
    /// The set for the front's current Ast.
    pub(crate) fn build(front: &Front) -> ConstReach {
        let mut idents = Vec::new();
        super::ast_hash::const_idents(&front.ast, (0, 0, 0), true, &mut idents);
        let consts: Vec<(usize, Sym)> = front
            .fn_loc
            .iter()
            .enumerate()
            .filter_map(|(i, &(item, sub))| {
                let def = fn_def_at(&front.ast, item, sub);
                (def.qual.is_const && def.self_param.is_none()).then_some((i, def.name))
            })
            .collect();
        let mut r = ConstReach { names: FxSet::default(), seen: (0, 0, 0), expanded: vec![false; consts.len()], consts };
        r.names.extend(idents);
        r.seen = arena_lens(front);
        r.close(front);
        r
    }

    /// Adds what a patch can make reachable: identifiers in the appended
    /// nodes, and the new bodies of the edited fns (`Front::fn_loc`
    /// indexes) that are reachable const fns.
    pub(crate) fn update(&mut self, front: &Front, edited: &[usize]) {
        let mut idents = Vec::new();
        super::ast_hash::const_idents(&front.ast, self.seen, false, &mut idents);
        self.names.extend(idents);
        self.seen = arena_lens(front);
        for (k, (i, _)) in self.consts.iter().enumerate() {
            if edited.contains(i) {
                self.expanded[k] = false;
            }
        }
        self.close(front);
    }

    /// True when an evaluator may run the body of fn `i` (a
    /// `Front::fn_loc` index).
    pub(crate) fn reaches(&self, front: &Front, i: usize) -> bool {
        let (item, sub) = front.fn_loc[i];
        let def = fn_def_at(&front.ast, item, sub);
        def.self_param.is_none() && self.names.contains(&def.name)
    }

    /// Adds the body identifiers of every const fn whose name is in the
    /// set, until nothing changes.
    fn close(&mut self, front: &Front) {
        let idents = &front.chunks[0].scan.body_idents;
        loop {
            let mut grew = false;
            for (k, &(i, name)) in self.consts.iter().enumerate() {
                if !self.expanded[k] && self.names.contains(&name) {
                    self.expanded[k] = true;
                    self.names.extend(idents.get(i).into_iter().flatten().copied());
                    grew = true;
                }
            }
            if !grew {
                return;
            }
        }
    }
}

fn arena_lens(front: &Front) -> (usize, usize, usize) {
    (front.ast.exprs.len(), front.ast.tys.len(), front.ast.pats.len())
}
