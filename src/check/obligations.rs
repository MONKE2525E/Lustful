// The trait obligation queue of one body (docs/ARCH.md sections 2.4 and 2.12).
//
// The checker (`check/mod.rs`) drives this queue at the fixed run
// points S3a planted: before a structural resolution (2.12), at
// coercion sites, and at body end to a fixpoint. This module owns
// the queue data; selection itself is `traits::solve`, run by the
// checker over its own inference context (`SolveCx` in
// `check/mod.rs`), because probes must bind and roll back the
// body's inference variables.
//
// Most obligations are trait refs from bounds at call sites. An
// `AssocEq` obligation comes from a selected impl's predicates
// and from bindings written at a use (`T: Iterator<Item = u8>`):
// it is proved by normalizing the projection, never by search.
use crate::diag::Span;
use crate::intern::FxMap;
use crate::traits::ImplId;
use crate::ty::{AssocEqData, GenericArg, TraitRef, Ty};

/// One pending obligation plus the span that needs it.
#[derive(Clone, Copy, Debug)]
pub enum Obligation {
    Trait { trait_ref: TraitRef, span: Span, depth: u16 },
    AssocEq { eq: AssocEqData, span: Span },
    /// A use that needs a dyn value's object lifetime to be `'static`
    /// (`check::object`); decided once at body end.
    DynStatic { span: Span },
    /// A `'static` bound (`X: 'static`) on an instantiated type;
    /// decided once at body end (`Ctx::static_bound_err`).
    TypeStatic { ty: Ty, span: Span },
}

/// The per-body work queue. Runs happen in `check/mod.rs`; see
/// the file header.
#[derive(Default)]
pub struct Obligations {
    queue: Vec<Obligation>,
    /// The impl and args each re-queued trait obligation (trait
    /// ref, span, depth) was last selected with; see `note_requeued`.
    requeued: FxMap<(TraitRef, Span, u16), (ImplId, Vec<GenericArg>)>,
}

impl Obligations {
    /// An empty queue for one body.
    pub fn new() -> Obligations {
        Obligations::default()
    }

    /// Records one obligation for a later run point.
    pub fn push(&mut self, obligation: Obligation) {
        self.queue.push(obligation);
    }

    /// Records one trait obligation at a nested depth.
    pub fn push_trait_at(&mut self, trait_ref: TraitRef, span: Span, depth: u16) {
        self.queue.push(Obligation::Trait { trait_ref, span, depth });
    }

    /// True while nothing waits.
    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    /// Takes the whole queue for one run. Obligations a run
    /// cannot finish are pushed back by the caller.
    pub fn take(&mut self) -> Vec<Obligation> {
        std::mem::take(&mut self.queue)
    }

    /// The waiting obligations, in queue order. Closure signature
    /// deduction (ARCH 2.9) reads the `Fn` bounds on an expected type
    /// variable from here.
    pub fn pending(&self) -> &[Obligation] {
        &self.queue
    }

    /// How many obligations wait, for probe rollback.
    pub fn len(&self) -> usize {
        self.queue.len()
    }

    /// Drops obligations queued since a `len` snapshot (a failed
    /// method probe).
    pub fn truncate(&mut self, len: usize) {
        self.queue.truncate(len);
    }

    /// Records the impl selection of a trait obligation that goes
    /// back on the queue because an impl parameter is still an
    /// inference variable. False when its last selection had the
    /// same impl and args: the nested predicates of that selection
    /// are queued, so this one repeats them and settles nothing.
    /// A selection with other args (a variable got bound) is new.
    pub fn note_requeued(&mut self, trait_ref: TraitRef, span: Span, depth: u16, id: ImplId, args: &[GenericArg]) -> bool {
        match self.requeued.get_mut(&(trait_ref, span, depth)) {
            Some(last) if last.0 == id && last.1 == args => false,
            Some(last) => {
                *last = (id, args.to_vec());
                true
            }
            None => {
                self.requeued.insert((trait_ref, span, depth), (id, args.to_vec()));
                true
            }
        }
    }
}
