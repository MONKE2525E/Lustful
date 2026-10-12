// The trait obligation queue of one body (docs/ARCH.md sections 2.4 and 2.12).
//
// S3a puts the hook calls in place and leaves this queue empty: lust has no user
// traits yet, so no code pushes an obligation and every run is a no-op. W-TRAITS-CORE
// owns this file from wave A and fills the runs with the selection algorithm of
// ARCH 2.4 (whole-trait-ref matching, probes, the provably-false clause filter,
// deferral, and the depth cap). It must not add run points: the queue runs only
// where the checker already calls in, because running it after every expression
// that binds a variable can go quadratic in large bodies.
//
// Fixed run points, all in `check/mod.rs`:
// - `run_before_structural`: just before each point where a type must have a known
//   head (ARCH 2.12): a method call receiver, a field access base, an index base,
//   a deref operand, a binary operator's left operand, and a match scrutinee.
//   The `?` operand and closure-param points join this list when those syntax
//   forms land; they call the same hook.
// - `run_at_coercion`: at every coercion site (`coerce_at`).
// - `run_at_body_end`: once at the end of a body, to a fixpoint. Anything left is
//   an annotation error, never a silent default, except integer and
//   float literal fallback, which the checker keeps.
use crate::diag::Span;
use crate::ty::TraitRef;

/// One pending trait obligation: the whole trait ref (with its bindings) plus the
/// span that needs it. Selection matches the whole ref, never Self alone (2.4).
#[allow(dead_code)] // First pushed by W-TRAITS-CORE when trait bounds collect.
#[derive(Clone, Copy, Debug)]
pub struct Obligation {
    pub trait_ref: TraitRef,
    pub span: Span,
}

/// The per-body work queue. See the file header for when it runs.
#[derive(Default)]
pub struct Obligations {
    queue: Vec<Obligation>,
}

impl Obligations {
    /// An empty queue for one body.
    pub fn new() -> Obligations {
        Obligations::default()
    }

    /// Records one obligation for a later run point.
    #[allow(dead_code)] // First callers arrive with W-TRAITS-CORE.
    pub fn push(&mut self, obligation: Obligation) {
        self.queue.push(obligation);
    }

    /// True while nothing waits. Always true until obligations can be formed.
    #[allow(dead_code)] // Read by the selection code that lands with W-TRAITS-CORE.
    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    /// ARCH 2.4 run point: before a structural resolution (2.12). No-op while empty.
    pub fn run_before_structural(&mut self) {
        debug_assert!(self.queue.is_empty(), "obligations exist before selection lands");
    }

    /// ARCH 2.4 run point: at a coercion site. No-op while empty.
    pub fn run_at_coercion(&mut self) {
        debug_assert!(self.queue.is_empty(), "obligations exist before selection lands");
    }

    /// ARCH 2.4 run point: at body end, to a fixpoint. No-op while empty.
    pub fn run_at_body_end(&mut self) {
        debug_assert!(self.queue.is_empty(), "obligations exist before selection lands");
    }
}
