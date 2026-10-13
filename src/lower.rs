// Lowering: checked AST to IR. Makes evaluation order, temporaries, moves, borrows, and drops explicit.
use crate::ast::{self, BinOp, Expr, ExprId, FmtKind, FmtPiece, FmtSpec, MacroKind, Pat, PatId, Stmt};
use crate::check::collect::*;
use crate::check::{Autoref, BindMode, Builtin, Checked, Coerce, PatRes, PrimCmpKind, PrimOpKind, Res};
use crate::diag::Span;
use crate::ir::*;
use crate::ty::*;

mod closure;

struct LoopInfo {
    break_bb: Bb,
    continue_bb: Bb,
    dest: Option<Place>,
    depth: usize,
    label: Option<(crate::intern::Sym, crate::diag::Span)>,
    is_block: bool,
}

struct Lower<'p, 'a> {
    p: &'p Program<'a>,
    ck: Checked<'p>,
    body: Body<'p>,
    cur: Bb,
    /// Each scope lists its locals in declaration order. They drop in reverse at scope exit.
    scopes: Vec<Vec<Local>>,
    loops: Vec<LoopInfo>,
    local_map: Vec<Local>,
    /// Depth of mutable place evaluation (see `place_for_mut`).
    mut_index: u32,
    /// `needs_drop` answers per body type: every scope exit asks for each of
    /// its locals, and the answer walks Adt fields.
    drop_ty: crate::intern::FxMap<Ty, bool>,
    /// Set while lowering a closure body fn (see `lower::closure`).
    upvars: Option<closure::Upvars>,
    /// While a match guard lowers, the place each of the arm's
    /// pattern bindings reads through (see `bind_pat_guard`):
    /// parallel to the checker's locals, `None` outside a guard.
    /// `place` consults it before `local_map`.
    guard_places: Vec<Option<Place>>,
}

/// Lowers one checked function body to IR.
pub fn lower<'p, 'a>(p: &'p Program<'a>, fid: LocalDefId, mut ck: Checked<'p>) -> Body<'p> {
    if p.gx.closure_fns.contains_key(&fid) {
        return closure::lower_closure(p, fid, ck);
    }
    let f = p.fn_info(fid);
    // The owned type store lift (ARCH 2.1): the checked body's types move into the
    // lowered body through this boundary. Identity today; see `ty::lift_to_owned`.
    let tys = lift_to_owned(std::mem::replace(&mut ck.tys, Tys::new(&p.tys)));
    let reads = std::mem::take(&mut ck.reads);
    let entry = BlockData { stmts: Vec::new(), term: Terminator::Unreachable, term_span: Span::default() };
    let body = Body { fn_id: fid, tys, locals: Vec::new(), blocks: vec![entry], arg_count: f.params.len(), reads, lower_errs: Vec::new() };
    let mut lw = Lower {
        p,
        ck,
        body,
        cur: Bb(0),
        scopes: vec![Vec::new()],
        loops: Vec::new(),
        local_map: Vec::new(),
        mut_index: 0,
        drop_ty: Default::default(),
        upvars: None,
        guard_places: Vec::new(),
    };
    lw.new_local(f.ret, true, None);
    lw.local_map = vec![u32::MAX; lw.ck.locals.len()];
    lw.guard_places = vec![None; lw.ck.locals.len()];
    for i in 0..lw.ck.param_locals.len() {
        let cl = lw.ck.param_locals[i];
        let info = &lw.ck.locals[cl as usize];
        let (ty, m, name) = (info.ty, info.mutable, p.name(info.name).to_string());
        let l = lw.new_local(ty, m, Some(name));
        lw.local_map[cl as usize] = l;
        lw.scopes[0].push(l);
    }
    // The parser only builds fns with bodies today; a declaration shape
    // lowers to an empty return so this can never panic.
    let (span, body) = match f.def.body {
        Some(b) => (p.ast.block(b).span, Some(b)),
        None => (Span::default(), None),
    };
    if let Some(b) = body {
        lw.block_into(b, Some(&Place::local(0)));
    }
    let root = lw.scopes.pop().unwrap();
    lw.emit_drops(&root, span);
    lw.terminate(Terminator::Return, span);
    lw.body
}

impl<'p, 'a> Lower<'p, 'a> {
    // ---------- Building blocks ----------

    fn new_local(&mut self, ty: Ty, mutable: bool, name: Option<String>) -> Local {
        self.body.locals.push(LocalDecl { ty, mutable, name });
        self.body.locals.len() as Local - 1
    }
    /// A temporary, owned by the innermost scope.
    fn temp(&mut self, ty: Ty) -> Local {
        let l = self.new_local(ty, true, None);
        self.scopes.last_mut().unwrap().push(l);
        l
    }
    fn new_block(&mut self) -> Bb {
        self.body.blocks.push(BlockData { stmts: Vec::new(), term: Terminator::Unreachable, term_span: Span::default() });
        Bb(self.body.blocks.len() as u32 - 1)
    }
    fn push(&mut self, kind: StmtKind, span: Span) {
        self.body.blocks[self.cur.0 as usize].stmts.push(crate::ir::Stmt { kind, span });
    }
    fn assign(&mut self, place: Place, rv: Rvalue, span: Span) {
        self.push(StmtKind::Assign(place, rv), span);
    }
    /// The mono instance for a call whose checked resolution
    /// names a template, through the zonked generic args the
    /// checker recorded for this expression (W-TRAITS-CORE through
    /// the lower owner). Plain fns answer themselves.
    fn resolve_generic_fn(&self, e: ExprId, f: LocalDefId) -> LocalDefId {
        if self.p.gx.fn_templates.get(f.0 as usize).is_none_or(|t| t.is_none()) {
            return f;
        }
        let ei = (e.0 - self.ck.expr_base) as usize;
        let Some(args) = self.ck.generic_args.get(ei) else { return f };
        if args.is_empty() {
            return f;
        }
        crate::check::generics::instance_for(self.p, &self.body.tys, f, args).unwrap_or(f)
    }
    /// Emits a call terminator that writes its result to `dest` and continues
    /// in a fresh block. The unwind successor is a cleanup block chain: one
    /// block per enclosing scope, innermost first, each dropping that
    /// scope's locals through the same `emit_drops` pass scope exit uses,
    /// then propagating to the next outer scope (docs/ARCH.md section 7.2).
    /// The innermost cleanup ends in `Unreachable`, where the wave C
    /// runtime resumes the exception.
    fn call_into(&mut self, target: CallTarget, args: Vec<Operand>, dest: Place, span: Span) {
        let next = self.new_block();
        // Build the cleanup chain outside-in first so each block can name
        // its successor, then fill the blocks innermost first.
        let depth = self.scopes.len();
        let mut chain: Vec<Bb> = (0..depth).map(|_| self.new_block()).collect();
        chain.reverse();
        let unwind = chain.first().copied();
        let b = &mut self.body.blocks[self.cur.0 as usize];
        b.term = Terminator::Call { target, args, dest, next, unwind };
        b.term_span = span;
        for (i, &cb) in chain.iter().enumerate() {
            self.cur = cb;
            let scope_idx = depth - 1 - i;
            let locals = self.scopes[scope_idx].clone();
            self.emit_drops(&locals, span);
            match chain.get(i + 1) {
                Some(&outer) => self.goto(outer, span),
                None => self.terminate(Terminator::Unreachable, span),
            }
        }
        self.cur = next;
    }
    /// The place a call result goes: the given destination, or a throwaway
    /// temporary for a call in statement position.
    fn call_dest(&mut self, dest: Option<&Place>, ty: Ty) -> Place {
        match dest {
            Some(d) => d.clone(),
            None => Place::local(self.temp(ty)),
        }
    }
    /// Ends the current block. Later code goes into a fresh block (unreachable if nothing jumps there).
    fn terminate(&mut self, term: Terminator, span: Span) {
        let b = &mut self.body.blocks[self.cur.0 as usize];
        b.term = term;
        b.term_span = span;
        self.cur = self.new_block();
    }
    fn goto(&mut self, target: Bb, span: Span) {
        let b = &mut self.body.blocks[self.cur.0 as usize];
        b.term = Terminator::Goto(target);
        b.term_span = span;
        self.cur = target;
    }
    fn emit_drops(&mut self, locals: &[Local], span: Span) {
        for &l in locals.iter().rev() {
            let ty = self.body.locals[l as usize].ty;
            let drops = match self.drop_ty.get(&ty) {
                Some(&d) => d,
                None => {
                    let d = needs_drop(self.p, &self.body.tys, ty);
                    self.drop_ty.insert(ty, d);
                    d
                }
            };
            if drops {
                self.push(StmtKind::Drop(l), span);
            }
            self.push(StmtKind::StorageDead(l), span);
        }
    }
    fn pop_scope(&mut self, span: Span) {
        let s = self.scopes.pop().unwrap();
        self.emit_drops(&s, span);
    }
    /// Emits drops for every scope deeper than `depth`, without popping them (for break/return).
    fn exit_to(&mut self, depth: usize, span: Span) {
        for i in (depth..self.scopes.len()).rev() {
            let ls = self.scopes[i].clone();
            self.emit_drops(&ls, span);
        }
    }

    fn span(&self, e: ExprId) -> Span {
        self.p.ast.expr_span(e)
    }
    fn ty(&self, e: ExprId) -> Ty {
        self.ck.ty(e)
    }
    fn kind(&self, t: Ty) -> TyKind {
        self.body.tys.kind(t)
    }
    fn ref_ty(&mut self, m: bool, t: Ty) -> Ty {
        self.body.tys.mk_ref(m, t)
    }
    fn peel(&self, mut t: Ty, n: u8) -> Ty {
        for _ in 0..n {
            if let TyKind::Ref(_, _, inner) = self.kind(t) {
                t = inner;
            } else if let Some(inner) = self.body.tys.smart_elem(t) {
                t = inner;
            }
        }
        t
    }
    fn operand_from(&self, place: Place, ty: Ty) -> Operand {
        if is_copy(self.p, &self.body.tys, ty) { Operand::Copy(place) } else { Operand::Move(place) }
    }
    fn derefs(place: Place, n: u8) -> Place {
        let mut p = place;
        for _ in 0..n {
            p = p.deref();
        }
        p
    }

    // ---------- Places and operands ----------

    fn is_place_expr(&self, e: ExprId) -> bool {
        match self.p.ast.expr(e) {
            Expr::Path(_) | Expr::SelfValue => matches!(self.ck.res(e), Res::Local(_)),
            Expr::Field { .. } | Expr::TupleField { .. } | Expr::Index { .. } | Expr::Deref(_) => true,
            _ => false,
        }
    }

    /// True when the place chain of `e` is rooted in a local variable:
    /// the parts of it a pattern does not move stay in that variable
    /// and drop with it. A chain rooted in a value (`make().pair`,
    /// `*make_box()`) holds the value in a temporary instead, and the
    /// temporary drops after the pattern's moves, as a match
    /// scrutinee temporary does in rustc.
    fn place_root_owned(&self, e: ExprId) -> bool {
        match self.p.ast.expr(e) {
            Expr::Path(_) | Expr::SelfValue => matches!(self.ck.res(e), Res::Local(_)),
            Expr::Field { base, .. } | Expr::TupleField { base, .. } | Expr::Index { base, .. } => self.place_root_owned(*base),
            Expr::Deref(inner) => self.place_root_owned(*inner),
            _ => false,
        }
    }

    /// True for a bare `..` element of an assignment target
    /// (`[a, .., b]`, `(a, ..)`, `Pair(a, ..)`). The parser reads it
    /// as an open range expression.
    fn is_rest_elem(&self, e: ExprId) -> bool {
        matches!(self.p.ast.expr(e), Expr::Range { lo: None, hi: None, inclusive: false })
    }

    /// Maps target elements to source indices, skipping the elements
    /// a `..` rest covers. The checker reports a bad count, so a
    /// mapping that does not fit just keeps the indices in range.
    fn map_assign_elems(&self, elems: &[ExprId], n: usize) -> Vec<(usize, ExprId)> {
        match elems.iter().position(|&e| self.is_rest_elem(e)) {
            None => elems.iter().enumerate().filter(|(i, _)| *i < n).map(|(i, &e)| (i, e)).collect(),
            Some(r) => {
                let suffix = elems.len() - r - 1;
                let mut out: Vec<(usize, ExprId)> = elems[..r].iter().enumerate().filter(|(i, _)| *i < n).map(|(i, &e)| (i, e)).collect();
                for (j, &e) in elems[r + 1..].iter().enumerate() {
                    if !self.is_rest_elem(e) && n >= suffix {
                        out.push((n - suffix + j, e));
                    }
                }
                out
            }
        }
    }

    /// True when `lhs` is a destructuring assignment target: a tuple,
    /// array, struct, or tuple-struct form, a `_` or `()` discard, or
    /// a unit variant path.
    fn is_destr_assign(&self, lhs: ExprId) -> bool {
        match self.p.ast.expr(lhs) {
            Expr::Tuple(_) | Expr::Array(_) | Expr::Underscore | Expr::StructLit { .. } | Expr::Unit => true,
            Expr::Call { .. } => matches!(self.ck.res(lhs), Res::Variant(..)),
            Expr::Path(_) => matches!(self.ck.res(lhs), Res::Variant(..)),
            _ => false,
        }
    }

    /// Evaluates `e` to a place that will be written or mutably borrowed. A `Vec` index in
    /// such a place is an `IndexMut` borrow in Rust: the mutable borrow of the container
    /// starts before the index expression runs, so `v[v.len()] = 1` and `&mut v[v.len()]`
    /// are errors. The `Index` case in `place` models that while `mut_index` is set: it
    /// takes a `&mut` temporary of the container first and indexes through it.
    fn place_for_mut(&mut self, e: ExprId) -> Place {
        self.mut_index += 1;
        let p = self.place(e);
        self.mut_index -= 1;
        p
    }

    /// Evaluates `e` to a place. A value expression goes into a new temporary.
    fn place(&mut self, e: ExprId) -> Place {
        match (self.p.ast.expr(e), self.ck.res(e)) {
            (Expr::Path(_) | Expr::SelfValue, Res::Local(l)) => match &self.guard_places[l as usize] {
                // A match guard reads its arm's bindings through a
                // shared reference (see `bind_pat_guard`).
                Some(p) => p.clone(),
                None => Place::local(self.local_map[l as usize]),
            },
            (Expr::Field { base, .. }, Res::Field { derefs, index }) => {
                let b = self.place(*base);
                Self::derefs(b, derefs).project(Proj::Field(index))
            }
            (Expr::TupleField { base, .. }, Res::Field { derefs, index }) => {
                let b = self.place(*base);
                Self::derefs(b, derefs).project(Proj::Field(index))
            }
            (Expr::Index { base, index }, Res::SliceIndex { derefs }) => {
                let b = self.place(*base);
                let b = Self::derefs(b, derefs);
                let (lo_e, hi_e, inclusive) = match self.p.ast.expr(*index) {
                    Expr::Range { lo, hi, inclusive } => (*lo, *hi, *inclusive),
                    _ => (None, None, false),
                };
                let bound = |this: &mut Self, e: Option<ExprId>| -> Option<Operand> {
                    e.map(|e| {
                        let t = this.temp(USIZE);
                        this.expr_into(e, Some(&Place::local(t)));
                        Operand::Copy(Place::local(t))
                    })
                };
                let lo = bound(self, lo_e).unwrap_or(Operand::Const(Const::Int(0, IntTy::Usize)));
                let hi = bound(self, hi_e);
                // The temporary holds the slice place itself (bare `[T]`
                // or `str` type, a fat value in codegen).
                let slice = match self.kind(self.ty(e)) {
                    TyKind::Slice(el) => self.body.tys.intern(TyKind::Slice(el)),
                    TyKind::Str => STR,
                    _ => ERROR,
                };
                let t = self.temp(slice);
                let span = self.span(e);
                let mutable = self.mut_index > 0;
                self.assign(Place::local(t), Rvalue::Subslice { base: b, lo, hi, inclusive, mutable }, span);
                Place::local(t)
            }
            (Expr::Index { base, index }, Res::Index { derefs }) => {
                let b = self.place(*base);
                let b = Self::derefs(b, derefs);
                // Mutable use: borrow the container before the index expression runs
                // (see `place_for_mut`), and index through that borrow.
                let b = if self.mut_index > 0 {
                    let bt = self.peel(self.ty(*base), derefs);
                    let rt = self.ref_ty(true, bt);
                    let t = self.temp(rt);
                    let span = self.span(e);
                    self.assign(Place::local(t), Rvalue::Ref(true, b), span);
                    Place::local(t).deref()
                } else {
                    b
                };
                let i = self.temp(USIZE);
                self.expr_into(*index, Some(&Place::local(i)));
                b.project(Proj::Index(i))
            }
            (Expr::Deref(inner), _) => self.place(*inner).deref(),
            // A field, index, or deref the checker could not resolve (its base
            // type is an error type, so no `Res` was recorded): evaluating it
            // through `expr_into` would call `place` on this same expression
            // forever. The checker or borrow checker already reports the real
            // error; give lowering a dummy place and move on.
            (Expr::Field { .. } | Expr::TupleField { .. } | Expr::Index { .. }, _) => {
                let t = self.temp(self.ty(e));
                Place::local(t)
            }
            _ => {
                let t = self.temp(self.ty(e));
                self.expr_into(e, Some(&Place::local(t)));
                Place::local(t)
            }
        }
    }

    /// Evaluates `e` to an operand, applying the coercion recorded by the checker.
    fn operand(&mut self, e: ExprId) -> Operand {
        let op = self.operand_raw(e);
        let span = self.span(e);
        let ty = self.ty(e);
        match self.ck.coerce(e) {
            Coerce::None => op,
            Coerce::StrFromString => {
                // `&String` (possibly `&&String`, or through a
                // `Box<String>`, whose value is already the
                // `&String` the builtin wants) to `&str`.
                let mut place = self.op_place(op, ty, span);
                let mut t = ty;
                while let TyKind::Ref(_, _, inner) = self.kind(t) {
                    if self.body.tys.is_string_ty(inner) {
                        break;
                    }
                    place = place.deref();
                    t = inner;
                }
                // Through an `Rc<String>` the builtin still wants
                // the `&String`: form it from the pointee place.
                if let Some(elem) = self.body.tys.rc_elem(t) {
                    let sp = place.deref();
                    let rt = self.ref_ty(false, elem);
                    let sr = self.temp(rt);
                    self.assign(Place::local(sr), Rvalue::Ref(false, sp), span);
                    place = Place::local(sr);
                }
                let tmp = self.temp(REF_STR);
                self.call_into(CallTarget::Builtin(Builtin::StringAsStr), vec![Operand::Copy(place)], Place::local(tmp), span);
                Operand::Copy(Place::local(tmp))
            }
            Coerce::BoxToRef(n, m) => {
                let place = self.op_place(op, ty, span);
                let place = Self::derefs(place, n);
                let elem = self.peel(ty, n);
                let rt = self.ref_ty(m, elem);
                let tmp = self.temp(rt);
                self.assign(Place::local(tmp), Rvalue::Ref(m, place), span);
                if m { Operand::Move(Place::local(tmp)) } else { Operand::Copy(Place::local(tmp)) }
            }
            Coerce::Deref(n) => {
                let place = self.op_place(op, ty, span);
                Operand::Copy(Self::derefs(place, n))
            }
            Coerce::SliceFromArray(m) | Coerce::SliceFromVec(m) => {
                let place = self.op_place(op, ty, span);
                let mut inner = self.peel(ty, 1);
                let mut place = place.deref();
                // `&Box<Vec<T>>` and `&Rc<Vec<T>>` slice through
                // the smart pointer as well.
                if let Some(b) = self.body.tys.smart_elem(inner) {
                    place = place.deref();
                    inner = b;
                }
                let elem = match self.kind(inner) {
                    TyKind::Array(e, _) => e,
                    _ => self.body.tys.vec_elem(inner).unwrap_or(ERROR),
                };
                let slice = self.body.tys.intern(TyKind::Slice(elem));
                let rt = self.ref_ty(m, slice);
                let tmp = self.temp(rt);
                self.assign(Place::local(tmp), Rvalue::SliceOf(place), span);
                if m { Operand::Move(Place::local(tmp)) } else { Operand::Copy(Place::local(tmp)) }
            }
            Coerce::MutToShared | Coerce::Reborrow => {
                let m = self.ck.coerce(e) == Coerce::Reborrow;
                let place = self.op_place(op, ty, span);
                let inner = self.peel(ty, 1);
                let rt = self.ref_ty(m, inner);
                let tmp = self.temp(rt);
                self.assign(Place::local(tmp), Rvalue::Ref(m, place.deref()), span);
                if m { Operand::Move(Place::local(tmp)) } else { Operand::Copy(Place::local(tmp)) }
            }
            Coerce::Unsize(target) => self.unsize(op, ty, target, span),
        }
    }

    /// The type of `e` after its recorded coercion, for temporaries
    /// that hold the coerced operand.
    fn coerced_ty(&self, e: ExprId) -> Ty {
        match self.ck.coerce(e) {
            Coerce::StrFromString => REF_STR,
            Coerce::Unsize(t) => t,
            _ => self.ty(e),
        }
    }

    /// Lowers an unsizing coercion (ARCH 2.8) of the reference `op` (of
    /// type `found`) to `target`, a dyn reference: a reborrow of the
    /// source at the target's mutability (so a `&mut` source stays
    /// usable after, as in rustc), then a new fat pointer for a thin
    /// source, or an upcast (or a plain copy, when only auto traits
    /// drop) for a dyn source.
    fn unsize(&mut self, op: Operand, found: Ty, target: Ty, span: Span) -> Operand {
        use crate::check::object;
        let TyKind::Ref(_, tm, dyn_ty) = self.kind(target) else { unreachable!() };
        let m = tm.is_mut();
        let place = self.op_place(op, found, span);
        let src = self.peel(found, 1);
        let rt = self.ref_ty(m, src);
        let r = self.temp(rt);
        self.assign(Place::local(r), Rvalue::Ref(m, place.deref()), span);
        let ptr = if m { Operand::Move(Place::local(r)) } else { Operand::Copy(Place::local(r)) };
        let rv = match (object::principal_of(&self.body.tys, src), object::principal_of(&self.body.tys, dyn_ty)) {
            (Some(from), Some(to)) => {
                let path = object::upcast_path(self.p, &mut self.body.tys, from, to).unwrap_or_default();
                if path.is_empty() { Rvalue::Use(ptr) } else { Rvalue::DynUpcast { ptr, path } }
            }
            _ => Rvalue::MakeDyn { ptr, src, dyn_ty },
        };
        let out = self.temp(target);
        self.assign(Place::local(out), rv, span);
        if m { Operand::Move(Place::local(out)) } else { Operand::Copy(Place::local(out)) }
    }

    /// Points a dyn method call's receiver at the vtable of the trait
    /// that declares the method: unchanged for a principal method, an
    /// upcast along the super slots for a supertrait method.
    #[allow(clippy::too_many_arguments)]
    fn dyn_receiver(
        &mut self,
        recv: Operand,
        recv_dyn: Ty,
        mutable: bool,
        owner: DefId,
        cand: u8,
        name: crate::intern::Sym,
        span: Span,
    ) -> Operand {
        use crate::check::object;
        let Some(principal) = object::principal_of(&self.body.tys, recv_dyn) else { return recv };
        if principal.def == owner {
            return recv;
        }
        let cands = object::object_cands(self.p, &mut self.body.tys, principal, name);
        // Check resolved the call to this candidate, so the supertrait
        // and its slot path exist; a miss here would call the wrong
        // vtable.
        let Some(c) = cands.into_iter().nth(cand as usize).filter(|c| c.owner.def == owner) else { unreachable!() };
        let Some(path) = object::upcast_path(self.p, &mut self.body.tys, principal, c.owner) else { unreachable!() };
        let bounds = self.body.tys.intern_dyn_bounds(DynBounds {
            principal: Some(Binder::plain(c.owner)),
            supertraits: Box::new([]),
            auto: AutoTraits::default(),
        });
        let owner_dyn = self.body.tys.intern(TyKind::Dyn(bounds, Region::Erased));
        let rt = self.ref_ty(mutable, owner_dyn);
        let t = self.temp(rt);
        self.assign(Place::local(t), Rvalue::DynUpcast { ptr: recv, path }, span);
        if mutable { Operand::Move(Place::local(t)) } else { Operand::Copy(Place::local(t)) }
    }

    fn op_place(&mut self, op: Operand, ty: Ty, span: Span) -> Place {
        match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            Operand::Const(c) => {
                let t = self.temp(ty);
                self.assign(Place::local(t), Rvalue::Use(Operand::Const(c)), span);
                Place::local(t)
            }
        }
    }

    fn operand_raw(&mut self, e: ExprId) -> Operand {
        let ty = self.ty(e);
        match self.p.ast.expr(e) {
            Expr::Int(v, _) => match self.kind(ty) {
                TyKind::Int(it) => Operand::Const(Const::Int(*v, it)),
                _ => Operand::Const(Const::Int(*v, IntTy::I32)),
            },
            Expr::Float(i) => {
                let text = &self.p.ast.strings[*i as usize];
                let ft = match self.kind(ty) {
                    TyKind::Float(f) => f,
                    _ => FloatTy::F64,
                };
                // Parse straight to the literal's type: one rounding.
                match crate::check::collect::parse_float_literal_as(text, ft) {
                    Some(bits) => Operand::Const(Const::Float(bits, ft)),
                    None => Operand::Const(Const::Unit),
                }
            }
            Expr::Bool(b) => Operand::Const(Const::Bool(*b)),
            Expr::Char(c) => Operand::Const(Const::Char(*c)),
            Expr::Str(s) => Operand::Const(Const::Str(*s)),
            Expr::Unit => Operand::Const(Const::Unit),
            _ if self.is_place_expr(e) => {
                let p = self.place(e);
                // An index expression reads through the `Index` trait in
                // Rust, so moving its (non-Copy) value out, or a field
                // below it, is moving out of a reference and an error
                // (E0507/E0508). Route the read through a shared borrow
                // temporary so the borrow checker reports exactly that.
                // Pattern bindings project indexes directly and are not
                // affected (they do not come through here).
                if p.proj.iter().any(|x| matches!(x, Proj::Index(_))) && !is_copy(self.p, &self.body.tys, ty) {
                    let span = self.span(e);
                    let rt = self.ref_ty(false, ty);
                    let tmp = self.temp(rt);
                    self.assign(Place::local(tmp), Rvalue::Ref(false, p), span);
                    return self.operand_from(Place::local(tmp).deref(), ty);
                }
                self.operand_from(p, ty)
            }
            _ => {
                let t = self.temp(ty);
                self.expr_into_raw(e, Some(&Place::local(t)));
                Operand::Move(Place::local(t))
            }
        }
    }

    /// An operand for `e` after `n` implicit derefs.
    fn operand_derefs(&mut self, e: ExprId, n: u8) -> Operand {
        if n == 0 {
            return self.operand(e);
        }
        let p = self.place(e);
        let t = self.peel(self.ty(e), n);
        self.operand_from(Self::derefs(p, n), t)
    }

    /// A shared reference to the value of `e` (after `n` derefs). Used for format arguments and `==`.
    fn borrow_of(&mut self, e: ExprId, n: u8) -> (Operand, Ty) {
        let span = self.span(e);
        let p = self.place(e);
        let p = Self::derefs(p, n);
        let t = self.peel(self.ty(e), n);
        let rt = self.ref_ty(false, t);
        let tmp = self.temp(rt);
        self.assign(Place::local(tmp), Rvalue::Ref(false, p), span);
        (Operand::Copy(Place::local(tmp)), t)
    }

    // ---------- Expressions ----------

    /// Evaluates `e` and stores the result in `dest` (or drops it when `dest` is None).
    fn expr_into(&mut self, e: ExprId, dest: Option<&Place>) {
        if self.ck.coerce(e) != Coerce::None {
            let op = self.operand(e);
            if let Some(d) = dest {
                self.assign(d.clone(), Rvalue::Use(op), self.span(e));
            }
            return;
        }
        self.expr_into_raw(e, dest);
    }

    fn expr_into_raw(&mut self, e: ExprId, dest: Option<&Place>) {
        let span = self.span(e);
        let p = self.p;
        let ty = self.ty(e);
        // A value the checker const-evaluated materializes directly.
        if let Some(cv) = self.ck.const_value(e).cloned() {
            if let Some(d) = dest {
                self.const_into(&cv, ty, d, span);
            }
            return;
        }
        match p.ast.expr(e) {
            Expr::Int(..) | Expr::Float(_) | Expr::Bool(_) | Expr::Char(_) | Expr::Str(_) | Expr::Unit => {
                if let Some(d) = dest {
                    let op = self.operand_raw(e);
                    self.assign(d.clone(), Rvalue::Use(op), span);
                }
            }
            Expr::Path(_) | Expr::SelfValue => match self.ck.res(e) {
                Res::Local(_) => {
                    if let Some(d) = dest {
                        let pl = self.place(e);
                        let op = self.operand_from(pl, ty);
                        self.assign(d.clone(), Rvalue::Use(op), span);
                    }
                }
                Res::Variant(a, v) => {
                    if matches!(self.kind(ty), TyKind::FnDef(..)) {
                        // A constructor used as a value: the value itself
                        // is zero-sized; calls through it decode the
                        // constructor from the type.
                        self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Unit)), ty, span)
                    } else {
                        self.set_or_temp(dest, Rvalue::Aggregate(a, v, Vec::new()), ty, span)
                    }
                }
                Res::Fn(f) => {
                    // A fn item used as a value: zero-sized at its FnDef
                    // type, the slot trampoline where a fn pointer goes.
                    let want = match dest {
                        Some(d) if d.proj.is_empty() => {
                            let dt = self.body.locals[d.local as usize].ty;
                            if matches!(self.kind(dt), TyKind::FnPtr(_)) { dt } else { ty }
                        }
                        _ => ty,
                    };
                    self.set_or_temp(dest, Rvalue::FnValue(f, want), ty, span)
                }
                Res::Static(idx) => self.set_or_temp(dest, Rvalue::StaticLoad(idx), ty, span),
                Res::OptNone => self.set_or_temp(dest, Rvalue::Opt(ty, None), ty, span),
                _ => {}
            },
            Expr::Field { .. } | Expr::TupleField { .. } | Expr::Index { .. } | Expr::Deref(_) => {
                let pl = self.place(e);
                if let Some(d) = dest {
                    // Index reads go through the `Index` trait (see
                    // `operand_raw`): a non-Copy move out of a place
                    // below one is a move out of a reference.
                    let op = if pl.proj.iter().any(|x| matches!(x, Proj::Index(_))) && !is_copy(self.p, &self.body.tys, ty) {
                        let rt = self.ref_ty(false, ty);
                        let tmp = self.temp(rt);
                        self.assign(Place::local(tmp), Rvalue::Ref(false, pl), span);
                        self.operand_from(Place::local(tmp).deref(), ty)
                    } else {
                        self.operand_from(pl, ty)
                    };
                    self.assign(d.clone(), Rvalue::Use(op), span);
                }
            }
            Expr::Block(b) => self.block_into(*b, dest),
            Expr::If { cond, then, els } if self.is_let_chain(*cond) => {
                let (eb, end) = (self.new_block(), self.new_block());
                self.scopes.push(Vec::new());
                self.cond_chain(*cond, eb, span);
                self.block_into(*then, dest);
                self.pop_scope(span);
                self.goto(end, span);
                self.cur = eb;
                if let Some(els) = els {
                    self.expr_into(*els, dest);
                } else if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Use(Operand::Const(Const::Unit)), span);
                }
                self.goto(end, span);
                self.cur = end;
            }
            Expr::If { cond, then, els } => {
                let cl = self.cond(*cond, span);
                let (tb, eb, end) = (self.new_block(), self.new_block(), self.new_block());
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::If(Operand::Copy(Place::local(cl)), tb, eb);
                b.term_span = span;
                self.cur = tb;
                self.block_into(*then, dest);
                self.goto(end, span);
                self.cur = eb;
                if let Some(els) = els {
                    self.expr_into(*els, dest);
                } else if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Use(Operand::Const(Const::Unit)), span);
                }
                self.goto(end, span);
            }
            Expr::While { label, cond, body } if self.is_let_chain(*cond) => {
                let (head, exit) = (self.new_block(), self.new_block());
                self.goto(head, span);
                self.scopes.push(Vec::new());
                self.cond_chain(*cond, exit, span);
                self.loops.push(LoopInfo {
                    break_bb: exit,
                    continue_bb: head,
                    dest: None,
                    depth: self.scopes.len() - 1,
                    label: label.map(|l| (l.name, l.span)),
                    is_block: false,
                });
                self.block_into(*body, None);
                self.loops.pop();
                self.pop_scope(span);
                self.goto(head, span);
                self.cur = exit;
                if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Use(Operand::Const(Const::Unit)), span);
                }
            }
            Expr::While { label, cond, body } => {
                let (head, bodyb, exit) = (self.new_block(), self.new_block(), self.new_block());
                self.goto(head, span);
                let cl = self.cond(*cond, span);
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::If(Operand::Copy(Place::local(cl)), bodyb, exit);
                b.term_span = span;
                self.cur = bodyb;
                self.loops.push(LoopInfo {
                    break_bb: exit,
                    continue_bb: head,
                    dest: None,
                    depth: self.scopes.len(),
                    label: label.map(|l| (l.name, l.span)),
                    is_block: false,
                });
                self.block_into(*body, None);
                self.loops.pop();
                self.goto(head, span);
                self.cur = exit;
                if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Use(Operand::Const(Const::Unit)), span);
                }
            }
            Expr::Loop { label, body } => {
                let (head, exit) = (self.new_block(), self.new_block());
                self.goto(head, span);
                self.loops.push(LoopInfo {
                    break_bb: exit,
                    continue_bb: head,
                    dest: dest.cloned(),
                    depth: self.scopes.len(),
                    label: label.map(|l| (l.name, l.span)),
                    is_block: false,
                });
                self.block_into(*body, None);
                self.loops.pop();
                self.goto(head, span);
                self.cur = exit;
            }
            Expr::For { label, pat, iter, body } => self.for_loop(e, *label, *pat, *iter, *body, span, dest),
            Expr::Match { scrut, arms } => self.match_into(*scrut, arms, dest, span),
            Expr::Call { callee, args } => {
                let res = self.ck.res(e);
                // A call through an Fn-family bound of a type parameter
                // (template checks): a method call of the bound's trait
                // with the callee as its receiver.
                if let Res::Method { .. } = res {
                    self.method_into(e, *callee, args, dest, span);
                    return;
                }
                if let Res::ClosureCall { kind, derefs } = res {
                    self.closure_call(e, *callee, args, kind, derefs, dest, span);
                    return;
                }
                // An indirect call reads the callee value before the
                // arguments run, as Rust evaluates the callee first.
                let indirect_local = if res == Res::Indirect {
                    let ct = self.ty(*callee);
                    let op = self.operand(*callee);
                    match op {
                        Operand::Copy(pl) | Operand::Move(pl) if pl.proj.is_empty() && !matches!(self.kind(ct), TyKind::Ref(..)) => {
                            Some(pl.local)
                        }
                        Operand::Copy(pl) | Operand::Move(pl) => {
                            // A callee behind a reference loads through
                            // it first, so the call local holds the fn
                            // pointer itself.
                            let (vt, pl) = match self.kind(ct) {
                                TyKind::Ref(_, _, inner) => (inner, pl.deref()),
                                _ => (ct, pl),
                            };
                            let t = self.temp(vt);
                            let op2 = self.operand_from(pl, vt);
                            self.assign(Place::local(t), Rvalue::Use(op2), span);
                            Some(t)
                        }
                        Operand::Const(_) => None,
                    }
                } else {
                    None
                };
                let ops: Vec<Operand> = args.iter().map(|&a| self.operand(a)).collect();
                match res {
                    Res::Fn(f) => {
                        let f = self.resolve_generic_fn(e, f);
                        let d = self.call_dest(dest, ty);
                        self.call_into(CallTarget::Fn(f), ops, d, span);
                    }
                    Res::Intrinsic(id) => {
                        let d = self.call_dest(dest, ty);
                        self.call_into(CallTarget::Intrinsic(id), ops, d, span);
                    }
                    Res::Builtin(Builtin::VecNew) => {
                        self.set_or_temp(dest, Rvalue::VecLit(self.peel_vec(ty), Vec::new()), ty, span)
                    }
                    Res::Builtin(Builtin::VecWithCapacity) => {
                        // An empty Vec in a temporary, an exact
                        // reserve on it, then a move to the dest:
                        // the requested capacity is observable
                        // through `capacity()`, so it cannot be
                        // dropped, and the dest place itself need
                        // not be mutable.
                        let tv = self.temp(ty);
                        self.assign(Place::local(tv), Rvalue::VecLit(self.peel_vec(ty), Vec::new()), span);
                        let rt = self.ref_ty(true, ty);
                        let r = self.temp(rt);
                        self.assign(Place::local(r), Rvalue::Ref(true, Place::local(tv)), span);
                        let u = self.temp(UNIT);
                        self.call_into(
                            CallTarget::Builtin(Builtin::VecReserveExact),
                            vec![Operand::Move(Place::local(r)), ops.into_iter().next().unwrap()],
                            Place::local(u),
                            span,
                        );
                        self.set_or_temp(dest, Rvalue::Use(Operand::Move(Place::local(tv))), ty, span);
                    }
                    Res::Builtin(b) => {
                        let d = self.call_dest(dest, ty);
                        self.call_into(CallTarget::Builtin(b), ops, d, span);
                    }
                    Res::Variant(a, v) => self.set_or_temp(dest, Rvalue::Aggregate(a, v, ops), ty, span),
                    Res::ConstUsize(v) => {
                        self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Int(v as u128, IntTy::Usize))), ty, span)
                    }
                    Res::SizeOfVal { len, elem } => {
                        if elem == 1 {
                            let d = self.call_dest(dest, ty);
                            self.call_into(CallTarget::Builtin(len), ops, d, span);
                        } else {
                            let t = self.temp(ty);
                            self.call_into(CallTarget::Builtin(len), ops, Place::local(t), span);
                            self.set_or_temp(
                                dest,
                                Rvalue::Bin(BinOp::Mul, Operand::Copy(Place::local(t)), Operand::Const(Const::Int(elem as u128, IntTy::Usize))),
                                ty,
                                span,
                            );
                        }
                    }
                    // Only reads the vtable, so a `&mut dyn` argument is
                    // reborrowed, not moved, as rustc's `&mut` to `&` is.
                    Res::DynMeta(word) => {
                        let ptr = match ops.into_iter().next().unwrap() {
                            Operand::Move(pl) => Operand::Copy(pl),
                            o => o,
                        };
                        self.set_or_temp(dest, Rvalue::DynMeta { ptr, word }, ty, span)
                    }
                    Res::FromCast => self.set_or_temp(dest, Rvalue::Cast(ops.into_iter().next().unwrap(), ty), ty, span),
                    Res::DefaultVal => {
                        let zero = match self.kind(ty) {
                            TyKind::Int(it) => Const::Int(0, it),
                            TyKind::Bool => Const::Bool(false),
                            TyKind::Char => Const::Char('\0'),
                            _ => Const::Unit,
                        };
                        self.set_or_temp(dest, Rvalue::Use(Operand::Const(zero)), ty, span)
                    }
                    Res::OptSome => self.set_or_temp(dest, Rvalue::Opt(ty, ops.into_iter().next()), ty, span),
                    Res::Indirect => {
                        if let Some(l) = indirect_local {
                            let d = self.call_dest(dest, ty);
                            self.call_into(CallTarget::Indirect(l), ops, d, span);
                        }
                    }
                    Res::ResOk => {
                        let op = ops.into_iter().next().unwrap_or(Operand::Const(crate::ir::Const::Unit));
                        self.set_or_temp(dest, Rvalue::Res(ty, true, op), ty, span)
                    }
                    Res::ResErr => {
                        let op = ops.into_iter().next().unwrap_or(Operand::Const(crate::ir::Const::Unit));
                        self.set_or_temp(dest, Rvalue::Res(ty, false, op), ty, span)
                    }
                    // `<dyn P as Tr>::m(d, ..)`, `<dyn P>::m(d, ..)`, and
                    // `Tr::m(d, ..)`: the receiver is the first argument,
                    // already a dyn reference.
                    Res::DynMethod { owner, cand, slot, .. } => {
                        let Expr::Call { callee, .. } = p.ast.expr(e) else { unreachable!() };
                        let name = match p.ast.expr(*callee) {
                            Expr::QPath { segs, .. } | Expr::Path(segs) => segs[segs.len() - 1].name,
                            _ => unreachable!(),
                        };
                        let mut ops = ops;
                        let recv_ty = self.coerced_ty(args[0]);
                        let (m, recv_dyn) = match self.kind(recv_ty) {
                            TyKind::Ref(_, m, inner) => (m.is_mut(), inner),
                            _ => unreachable!(),
                        };
                        let r = ops.remove(0);
                        let r = self.dyn_receiver(r, recv_dyn, m, owner, cand, name, span);
                        ops.insert(0, r);
                        let t = self.temp(ty);
                        self.call_into(CallTarget::Dyn(slot), ops, Place::local(t), span);
                        if let Some(d) = dest {
                            let o = self.operand_from(Place::local(t), ty);
                            self.assign(d.clone(), Rvalue::Use(o), span);
                        }
                    }
                    _ => return,
                }
            }
            Expr::MethodCall { recv, args, .. } => self.method_into(e, *recv, args, dest, span),
            Expr::Binary { op, lhs, rhs } => self.binary_into(e, *op, *lhs, *rhs, dest, span),
            Expr::Unary { op, expr } => {
                // A negated integer literal is one literal, not a runtime negate:
                // folding it is what makes `-128i8` (and the other MIN values) work.
                if *op == crate::ast::UnOp::Neg
                    && let Expr::Int(v, _) = p.ast.expr(*expr)
                    && let TyKind::Int(it) = self.kind(ty)
                {
                    if let Some(d) = dest {
                        self.assign(d.clone(), Rvalue::Use(Operand::Const(Const::Int(v.wrapping_neg(), it))), span);
                    }
                    return;
                }
                if let Res::TraitBin { f, ld, .. } = self.ck.res(e) {
                    let f = self.resolve_generic_fn(e, f);
                    let o = self.operand_derefs(*expr, ld);
                    let d = self.call_dest(dest, ty);
                    self.call_into(CallTarget::Fn(f), vec![o], d, span);
                    return;
                }
                let ld = match self.ck.res(e) {
                    Res::Bin { ld, .. } => ld,
                    _ => 0,
                };
                let o = self.operand_derefs(*expr, ld);
                if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Un(*op, o), span);
                } else {
                    let t = self.temp(ty);
                    self.assign(Place::local(t), Rvalue::Un(*op, o), span);
                }
            }
            Expr::Cast { expr, .. } => {
                let o = self.operand(*expr);
                if let Some(d) = dest {
                    // A cast to a fn pointer already holds the pointer
                    // value (the coercion on the inner expression made
                    // the trampoline, or it was a fn pointer already).
                    // A reference cast is the same: the coercion on the
                    // inner expression already built the target value.
                    if matches!(self.kind(ty), TyKind::FnPtr(_) | TyKind::Ref(..)) {
                        self.assign(d.clone(), Rvalue::Use(o), span);
                    } else {
                        self.assign(d.clone(), Rvalue::Cast(o, ty), span);
                    }
                }
            }
            Expr::Ref { mutable, expr, .. } => {
                if let Res::Static(idx) = self.ck.res(*expr) {
                    if let Some(d) = dest {
                        self.assign(d.clone(), Rvalue::StaticRef(idx), span);
                    }
                    return;
                }
                if matches!(self.ck.res(*expr), Res::SliceIndex { .. }) {
                    // A slice place is already a fat value in a temporary;
                    // taking its reference moves that value (with its loan),
                    // it does not borrow the temporary.
                    let pl = if *mutable { self.place_for_mut(*expr) } else { self.place(*expr) };
                    if let Some(d) = dest {
                        let op = self.operand_from(pl, ty);
                        self.assign(d.clone(), Rvalue::Use(op), span);
                    }
                    return;
                }
                let pl = if *mutable { self.place_for_mut(*expr) } else { self.place(*expr) };
                if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Ref(*mutable, pl), span);
                }
            }
            Expr::Assign { lhs, rhs } => {
                if self.is_destr_assign(*lhs) {
                    // Destructuring assignment, in rustc's desugared
                    // order: evaluate the right-hand side once, move
                    // each written element into a binding temporary in
                    // target order, drop what remains of a temporary
                    // scrutinee, then write each target in order (its
                    // place evaluates just before its own write, so a
                    // swap reads both old values). A scrutinee that is
                    // a place rooted in a local binds out of that place
                    // as in a `let`: elements the target discards stay
                    // in it and drop with its owner, they do not drop
                    // here. Any other scrutinee (a value, or a place
                    // rooted in a value such as `make().pair`) holds
                    // its storage in a temporary local, and dropping
                    // that root after the moves drops exactly the
                    // discarded and rest elements, plus any ancestors
                    // outside the matched projection, before the first
                    // target place evaluates.
                    let rt = self.ty(*rhs);
                    let owned = self.ck.coerce(*rhs) == Coerce::None && self.is_place_expr(*rhs) && self.place_root_owned(*rhs);
                    let src = if self.ck.coerce(*rhs) == Coerce::None {
                        let pl = self.place(*rhs);
                        self.assign_pattern_place(pl, rt, *lhs, span)
                    } else {
                        let tmp = Place::local(self.temp(rt));
                        self.expr_into(*rhs, Some(&tmp));
                        tmp
                    };
                    let mut writes = Vec::new();
                    self.collect_assign_pattern(*lhs, src.clone(), rt, span, &mut writes);
                    if !owned {
                        let root_ty = self.body.locals[src.local as usize].ty;
                        if needs_drop(self.p, &self.body.tys, root_ty) {
                            self.push(StmtKind::Drop(src.local), span);
                        }
                    }
                    for (target, src, ety) in writes {
                        let pl = self.place_for_mut(target);
                        let op = self.operand_from(src, ety);
                        self.assign(pl, Rvalue::Use(op), span);
                    }
                    self.unit(dest, span);
                    return;
                }
                let o = self.operand(*rhs);
                let pl = self.place_for_mut(*lhs);
                self.assign(pl, Rvalue::Use(o), span);
                self.unit(dest, span);
            }
            Expr::AssignOp { op, lhs, rhs } => {
                let lt = self.ty(*lhs);
                if let Res::TraitBin { f, rd, .. } = self.ck.res(e) {
                    // Through the assignment trait: `add_assign(&mut place, rhs)`.
                    let f = self.resolve_generic_fn(e, f);
                    let r = self.operand_derefs(*rhs, rd);
                    let pl = self.place_for_mut(*lhs);
                    let mt = self.ref_ty(true, lt);
                    let t = self.temp(mt);
                    self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
                    let u = self.temp(UNIT);
                    self.call_into(CallTarget::Fn(f), vec![Operand::Move(Place::local(t)), r], Place::local(u), span);
                    self.unit(dest, span);
                    return;
                }
                if self.body.tys.is_string_ty(lt) {
                    let pl = self.place_for_mut(*lhs);
                    let r = self.operand(*rhs);
                    let mt = self.ref_ty(true, STRING);
                    let t = self.temp(mt);
                    self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
                    let u = self.temp(UNIT);
                    self.call_into(
                        CallTarget::Builtin(Builtin::StringPushStr),
                        vec![Operand::Move(Place::local(t)), r],
                        Place::local(u),
                        span,
                    );
                } else {
                    let rd = match self.ck.res(e) {
                        Res::Bin { rd, .. } => rd,
                        _ => 0,
                    };
                    let r = self.operand_derefs(*rhs, rd);
                    let pl = self.place_for_mut(*lhs);
                    self.assign(pl.clone(), Rvalue::Bin(*op, Operand::Copy(pl), r), span);
                }
                self.unit(dest, span);
            }
            Expr::StructLit { fields, update, .. } => {
                let Res::Variant(a, v) = self.ck.res(e) else { return };
                let n = p.adt(a).variants[v as usize].fields.len();
                let mut ops: Vec<Option<Operand>> = vec![None; n];
                for &(fname, _, fe) in fields {
                    let i = p.adt(a).variants[v as usize].fields.iter().position(|f| f.name == fname).unwrap();
                    // Field values are evaluated in written order, then moved into the struct.
                    let o = self.operand(fe);
                    let fresh_temp =
                        matches!(&o, Operand::Move(p) if p.proj.is_empty() && self.body.locals[p.local as usize].name.is_none());
                    let o = match o {
                        Operand::Const(_) => o,
                        _ if fresh_temp => o,
                        _ => {
                            let ft = self.coerced_ty(fe);
                            let t = self.temp(ft);
                            self.assign(Place::local(t), Rvalue::Use(o), span);
                            self.operand_from(Place::local(t), ft)
                        }
                    };
                    ops[i] = Some(o);
                }
                if let Some(u) = update {
                    // The base is evaluated after the written fields, and the
                    // fields not written move out of it.
                    let base = self.place(*u);
                    for (i, slot) in ops.iter_mut().enumerate() {
                        if slot.is_none() {
                            let ft = p.adt(a).variants[v as usize].fields[i].ty;
                            *slot = Some(self.operand_from(base.project(Proj::Field(i as u32)), ft));
                        }
                    }
                }
                let ops = ops.into_iter().map(|o| o.unwrap()).collect();
                self.set_or_temp(dest, Rvalue::Aggregate(a, v, ops), ty, span);
            }
            Expr::Range { .. } => {}
            Expr::Break { label, value: val } => {
                let ti = match label {
                    None => self.loops.len() - 1,
                    Some(l) => self
                        .loops
                        .iter()
                        .rposition(|lp| lp.label.is_some_and(|(n, bs)| n == l.name && crate::diag::ctxt_can_see_local(l.span.ctxt, bs)))
                        .unwrap_or(self.loops.len() - 1),
                };
                let li = &self.loops[ti];
                let (bb, depth, ld) = (li.break_bb, li.depth, li.dest.clone());
                if let Some(v) = val {
                    self.expr_into(*v, ld.as_ref());
                }
                self.exit_to(depth, span);
                self.terminate(Terminator::Goto(bb), span);
            }
            Expr::Continue(label) => {
                let ti = match label {
                    None => self.loops.iter().rposition(|lp| !lp.is_block).unwrap_or(self.loops.len() - 1),
                    Some(l) => self
                        .loops
                        .iter()
                        .rposition(|lp| lp.label.is_some_and(|(n, bs)| n == l.name && crate::diag::ctxt_can_see_local(l.span.ctxt, bs)))
                        .unwrap_or(self.loops.len() - 1),
                };
                let li = &self.loops[ti];
                let (bb, depth) = (li.continue_bb, li.depth);
                self.exit_to(depth, span);
                self.terminate(Terminator::Goto(bb), span);
            }
            Expr::Return(val) => {
                match val {
                    Some(v) => self.expr_into(*v, Some(&Place::local(0))),
                    None => self.assign(Place::local(0), Rvalue::Use(Operand::Const(Const::Unit)), span),
                }
                self.exit_to(0, span);
                self.terminate(Terminator::Return, span);
            }
            Expr::LabeledBlock { label, body } => {
                let exit = self.new_block();
                self.loops.push(LoopInfo {
                    break_bb: exit,
                    continue_bb: exit,
                    dest: dest.cloned(),
                    depth: self.scopes.len(),
                    label: Some((label.name, label.span)),
                    is_block: true,
                });
                self.block_into(*body, dest);
                self.loops.pop();
                self.goto(exit, span);
            }
            Expr::Macro { kind, args, fmt, repeat } => self.macro_into(e, *kind, args, fmt, *repeat, dest, ty, span),
            Expr::Tuple(elems) => {
                let ops: Vec<Operand> = elems.iter().map(|&el| self.operand(el)).collect();
                self.set_or_temp(dest, Rvalue::TupleAgg(ty, ops), ty, span);
            }
            Expr::Array(elems) => {
                let ops: Vec<Operand> = elems.iter().map(|&el| self.operand(el)).collect();
                self.set_or_temp(dest, Rvalue::ArrayAgg(ty, ops), ty, span);
            }
            Expr::ArrayRepeat { value, .. } => {
                let n = match self.kind(ty) {
                    TyKind::Array(_, c) => match self.body.tys.const_kind(c) {
                        ConstKind::Int(n) => n as u64,
                        _ => 0,
                    },
                    _ => 0,
                };
                if let Some(cv) = self.ck.const_value(*value).cloned() {
                    // A const element (`[const { .. }; n]`) materializes per slot.
                    let rv = crate::ty::consteval::ConstValue::Repeat(Box::new(cv), n);
                    match dest {
                        Some(d) => self.const_into(&rv, ty, d, span),
                        None => {
                            let t = self.temp(ty);
                            self.const_into(&rv, ty, &Place::local(t), span);
                        }
                    }
                    return;
                }
                if n == 0 {
                    // Rust does not evaluate the element for a zero repeat.
                    self.set_or_temp(dest, Rvalue::ArrayAgg(ty, Vec::new()), ty, span);
                } else if n == 1 {
                    let o = self.operand(*value);
                    self.set_or_temp(dest, Rvalue::ArrayAgg(ty, vec![o]), ty, span);
                } else {
                    let o = self.operand(*value);
                    self.set_or_temp(dest, Rvalue::ArrayRepeat(ty, o, n), ty, span);
                }
            }
            Expr::OffsetOf { .. } => {
                if let Res::ConstUsize(v) = self.ck.res(e) {
                    self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Int(v as u128, IntTy::Usize))), ty, span);
                }
            }
            Expr::Closure { .. } => self.closure_value(e, dest, span),
            Expr::Try(inner) => self.try_into(e, *inner, dest, ty, span),
            // AST v2 expression forms the parser still rejects.
            Expr::Float(_)
            | Expr::Await(_)
            | Expr::AsyncBlock { .. }
            | Expr::UnsafeBlock(_)
            | Expr::Let { .. }
            | Expr::QPath { .. }
            | Expr::ConstBlock(_)
            | Expr::Underscore
            | Expr::MacroCall(_) => {}
        }
    }

    /// `expr?`: evaluate the scrutinee into a temporary, branch on
    /// its discriminant, move the success payload to `dest` on the
    /// good side, and on the empty side build the enclosing return
    /// value (converting the error as the checker recorded) and
    /// return it through the normal return path, drops included.
    fn try_into(&mut self, e: ExprId, inner: ExprId, dest: Option<&Place>, ty: Ty, span: Span) {
        let ity = self.ty(inner);
        let t = self.temp(ity);
        self.expr_into(inner, Some(&Place::local(t)));
        let tp = Place::local(t);
        let dsc = self.temp(int(IntTy::U32));
        self.assign(Place::local(dsc), Rvalue::Discriminant(tp.clone()), span);
        let is_result = self.body.tys.result_args(ity).is_some();
        // Variant index of the valued side: Ok is 0, Some is 1.
        let good: u32 = if is_result { 0 } else { 1 };
        let ok_bb = self.new_block();
        let err_bb = self.new_block();
        {
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(dsc)), vec![(good, ok_bb)], err_bb);
            b.term_span = span;
        }
        self.cur = err_bb;
        let ret_ty = self.body.locals[0].ty;
        if let Some((_, err_ty)) = self.body.tys.result_args(ity) {
            let payload = tp.clone().project(Proj::Downcast(1)).project(Proj::Field(0));
            let ret_err = self.body.tys.result_args(ret_ty).map(|(_, e2)| e2).unwrap_or(err_ty);
            let err_op = match self.ck.res(e) {
                Res::TryCast => {
                    let ct = self.temp(ret_err);
                    let op = self.operand_from(payload, err_ty);
                    self.assign(Place::local(ct), Rvalue::Cast(op, ret_err), span);
                    Operand::Move(Place::local(ct))
                }
                Res::TryFrom(f) if f.0 != u32::MAX => {
                    let f = self.resolve_generic_fn(e, f);
                    let ct = self.temp(ret_err);
                    let op = self.operand_from(payload, err_ty);
                    self.call_into(CallTarget::Fn(f), vec![op], Place::local(ct), span);
                    Operand::Move(Place::local(ct))
                }
                Res::TryStringFrom => {
                    let mut op = self.operand_from(payload, err_ty);
                    // `From<&String>` first views the String as `&str`.
                    if matches!(self.body.tys.kind(err_ty), TyKind::Ref(_, _, i) if i == STRING) {
                        let st = self.temp(REF_STR);
                        self.call_into(CallTarget::Builtin(Builtin::StringAsStr), vec![op], Place::local(st), span);
                        op = Operand::Move(Place::local(st));
                    }
                    let ct = self.temp(ret_err);
                    self.call_into(CallTarget::Builtin(Builtin::StringFrom), vec![op], Place::local(ct), span);
                    Operand::Move(Place::local(ct))
                }
                _ => self.operand_from(payload, err_ty),
            };
            self.assign(Place::local(0), Rvalue::Res(ret_ty, false, err_op), span);
        } else {
            self.assign(Place::local(0), Rvalue::Opt(ret_ty, None), span);
        }
        self.exit_to(0, span);
        self.terminate(Terminator::Return, span);
        self.cur = ok_bb;
        let payload = tp.project(Proj::Downcast(good)).project(Proj::Field(0));
        let op = self.operand_from(payload, ty);
        self.set_or_temp(dest, Rvalue::Use(op), ty, span);
    }

    /// The `&&` elements of a condition, left to right.
    fn split_and(&self, e: ExprId, out: &mut Vec<ExprId>) {
        match self.p.ast.expr(e) {
            Expr::Binary { op: BinOp::And, lhs, rhs } => {
                self.split_and(*lhs, out);
                self.split_and(*rhs, out);
            }
            _ => out.push(e),
        }
    }

    fn is_let_chain(&self, cond: ExprId) -> bool {
        let mut elems = Vec::new();
        self.split_and(cond, &mut elems);
        elems.iter().any(|&e| matches!(self.p.ast.expr(e), Expr::Let { .. }))
    }

    /// Lowers a let-chain condition in the current (chain) scope: falls
    /// through on success; each failing element drops what the chain has
    /// bound so far and jumps to `els_bb`.
    fn cond_chain(&mut self, cond: ExprId, els_bb: Bb, span: Span) {
        let mut elems = Vec::new();
        self.split_and(cond, &mut elems);
        for el in elems {
            match self.p.ast.expr(el) {
                Expr::Let { pat, scrut } => {
                    let (pat, scrut) = (*pat, *scrut);
                    let es = self.span(el);
                    let sp = self.place(scrut);
                    let sp = self.pattern_place(sp, self.ty(scrut), &[pat], es);
                    let fail = self.new_block();
                    let live = self.scopes.last().cloned().unwrap_or_default();
                    self.test_pat(pat, sp.clone(), fail);
                    let cont = self.cur;
                    self.cur = fail;
                    self.emit_drops(&live, es);
                    self.goto(els_bb, es);
                    self.cur = cont;
                    self.bind_pat(pat, sp);
                }
                _ => {
                    let cl = self.cond(el, span);
                    let next = self.new_block();
                    let fail = self.new_block();
                    let live = self.scopes.last().cloned().unwrap_or_default();
                    let b = &mut self.body.blocks[self.cur.0 as usize];
                    b.term = Terminator::If(Operand::Copy(Place::local(cl)), next, fail);
                    b.term_span = span;
                    self.cur = fail;
                    self.emit_drops(&live, span);
                    self.goto(els_bb, span);
                    self.cur = next;
                }
            }
        }
    }

    /// Evaluates a condition into a fresh bool local. Its temporaries drop before the branch.
    fn cond(&mut self, cond: ExprId, span: Span) -> Local {
        let cl = self.new_local(BOOL, true, None);
        self.scopes.push(Vec::new());
        self.expr_into(cond, Some(&Place::local(cl)));
        self.pop_scope(span);
        cl
    }

    fn unit(&mut self, dest: Option<&Place>, span: Span) {
        if let Some(d) = dest {
            self.assign(d.clone(), Rvalue::Use(Operand::Const(Const::Unit)), span);
        }
    }

    fn peel_vec(&self, t: Ty) -> Ty {
        self.body.tys.vec_elem(t).unwrap_or(ERROR)
    }

    // ---------- Blocks ----------

    fn block_into(&mut self, b: ast::BlockId, dest: Option<&Place>) {
        let block = self.p.ast.block(b);
        self.scopes.push(Vec::new());
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let { pat, init, els, span, .. } => match els {
                    Some(els_b) => self.let_else_stmt(*pat, *init, *els_b, *span),
                    None => self.let_stmt(*pat, *init, *span),
                },
                // Body items and statement macros are rejected by the parser today.
                Stmt::Item(_) | Stmt::Macro { .. } => {}
                Stmt::Expr { expr, .. } => {
                    let span = self.span(*expr);
                    self.scopes.push(Vec::new());
                    self.expr_into(*expr, None);
                    self.pop_scope(span);
                }
            }
        }
        match block.tail {
            Some(tail) => {
                // Edition 2024: temporaries in a block's tail drop before the block's locals.
                let span = self.span(tail);
                self.scopes.push(Vec::new());
                self.expr_into(tail, dest);
                self.pop_scope(span);
            }
            None => self.unit(dest, block.span),
        }
        self.pop_scope(block.span);
    }

    fn let_stmt(&mut self, pat: PatId, init: Option<ExprId>, span: Span) {
        let p = self.p;
        match (p.ast.pat(pat), self.ck.pat_res(pat)) {
            (Pat::Binding { .. }, PatRes::Binding { local, mode }) => {
                let info = &self.ck.locals[local as usize];
                let (ty, m, name) = (info.ty, info.mutable, p.name(info.name).to_string());
                let l = self.new_local(ty, m, Some(name));
                self.local_map[local as usize] = l;
                if let Some(init) = init {
                    self.scopes.push(Vec::new());
                    match mode {
                        BindMode::Move => {
                            // `let x = &temp();` extends the temporary to the enclosing block.
                            if let Expr::Ref { mutable, expr, .. } = p.ast.expr(init)
                                && matches!(
                                    self.ck.coerce(init),
                                    Coerce::None | Coerce::SliceFromArray(_) | Coerce::SliceFromVec(_) | Coerce::Unsize(_)
                                )
                                && !self.is_place_expr(*expr)
                            {
                                let t = self.ty(*expr);
                                let tmp = self.new_local(t, true, None);
                                let n = self.scopes.len();
                                self.scopes[n - 2].push(tmp);
                                self.expr_into(*expr, Some(&Place::local(tmp)));
                                if self.ck.coerce(init) == Coerce::None {
                                    self.assign(Place::local(l), Rvalue::Ref(*mutable, Place::local(tmp)), span);
                                } else if let Coerce::Unsize(target) = self.ck.coerce(init) {
                                    // `let d: &dyn Tr = &S::new();` extends the
                                    // temporary too, then unsizes the borrow.
                                    let rt = self.ref_ty(*mutable, t);
                                    let r = self.temp(rt);
                                    self.assign(Place::local(r), Rvalue::Ref(*mutable, Place::local(tmp)), span);
                                    let op = if *mutable { Operand::Move(Place::local(r)) } else { Operand::Copy(Place::local(r)) };
                                    let o = self.unsize(op, rt, target, span);
                                    self.assign(Place::local(l), Rvalue::Use(o), span);
                                } else {
                                    self.assign(Place::local(l), Rvalue::SliceOf(Place::local(tmp)), span);
                                }
                                self.pop_scope(span);
                                self.scopes.last_mut().unwrap().push(l);
                                return;
                            }
                            self.expr_into(init, Some(&Place::local(l)));
                        }
                        BindMode::Ref(m) => {
                            let pl = if m { self.place_for_mut(init) } else { self.place(init) };
                            self.assign(Place::local(l), Rvalue::Ref(m, pl), span);
                        }
                    }
                    self.pop_scope(span);
                }
                self.scopes.last_mut().unwrap().push(l);
            }
            (Pat::Wild, _) => {
                if let Some(init) = init {
                    // `let _ = place;` does not move the place. A `Copy` place is still
                    // read, so a borrow stored in it stays live until this point: emit
                    // the read into a throwaway temporary.
                    self.scopes.push(Vec::new());
                    if self.is_place_expr(init) {
                        let pl = self.place(init);
                        let ty = self.ty(init);
                        if is_copy(self.p, &self.body.tys, ty) {
                            let t = self.temp(ty);
                            self.assign(Place::local(t), Rvalue::Use(Operand::Copy(pl)), span);
                        }
                    } else {
                        self.expr_into(init, None);
                    }
                    self.pop_scope(span);
                }
            }
            _ => {
                // A destructuring `let` binds directly out of a place
                // initializer, as in rustc: a binding that moves a part
                // is a partial move of that place, and the parts the
                // pattern does not move stay in it and drop with it
                // (codegen elaborates the drop, `cgen::FnGen::elab_drop`).
                // Any other initializer goes through a temporary: it
                // moves there once, stays in scope before the bindings,
                // and parts the pattern does not move drop at scope exit.
                if let Some(init) = init {
                    if self.is_place_expr(init) {
                        self.scopes.push(Vec::new());
                        let pl = self.place(init);
                        // Move the place's own temporaries (index values
                        // and the like) into the block scope without
                        // dropping them: the projections name them.
                        let temps = self.scopes.pop().unwrap();
                        self.scopes.last_mut().unwrap().extend(temps);
                        let pl = self.pattern_place(pl, self.ty(init), &[pat], span);
                        self.bind_pat(pat, pl);
                    } else {
                        let tty = self.ty(init);
                        let t = self.new_local(tty, true, None);
                        self.scopes.push(Vec::new());
                        self.expr_into(init, Some(&Place::local(t)));
                        self.pop_scope(span);
                        self.scopes.last_mut().unwrap().push(t);
                        self.bind_pat(pat, Place::local(t));
                    }
                }
            }
        }
    }

    /// `let PAT = init else { ... };`: test the pattern against the
    /// scrutinee place (a place initializer directly, any other
    /// initializer through a block-scope temporary, as in `let_stmt`),
    /// bind on success, and run the diverging else block on failure.
    /// The scrutinee temporary stays in the block scope before the
    /// bindings, so parts the pattern does not move drop at scope
    /// exit on both paths (the else block's own exits drop it through
    /// the usual scope cleanup).
    fn let_else_stmt(&mut self, pat: PatId, init: Option<ExprId>, els: ast::BlockId, span: Span) {
        let Some(init) = init else { return };
        let sp = if self.is_place_expr(init) {
            self.scopes.push(Vec::new());
            let pl = self.place(init);
            let temps = self.scopes.pop().unwrap();
            self.scopes.last_mut().unwrap().extend(temps);
            pl
        } else {
            let tty = self.ty(init);
            let t = self.new_local(tty, true, None);
            self.scopes.push(Vec::new());
            self.expr_into(init, Some(&Place::local(t)));
            self.pop_scope(span);
            self.scopes.last_mut().unwrap().push(t);
            Place::local(t)
        };
        let fail = self.new_block();
        self.test_pat(pat, sp.clone(), fail);
        let cont = self.cur;
        self.cur = fail;
        self.block_into(els, None);
        self.terminate(Terminator::Unreachable, span);
        self.cur = cont;
        self.bind_pat(pat, sp);
    }

    // ---------- Calls ----------

    /// A scalar comparison trait method (`Res::PrimCmp`): the
    /// receiver is borrowed `&self` (so borrowck sees the loan a
    /// method call would make), both sides are read as scalars,
    /// and the result is the scalar comparison, an `Ordering`
    /// value, or an `Option<Ordering>` (`None` only when a float
    /// comparison is unordered).
    fn prim_cmp_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], dest: Option<&Place>, span: Span, kind: PrimCmpKind, derefs: u8) {
        use crate::check::PrimCmpKind as Ck;
        let out_ty = self.ty(e);
        let out = match dest {
            Some(d) => d.clone(),
            None => Place::local(self.temp(out_ty)),
        };
        if args.is_empty() {
            return;
        }
        let recv_ty = self.peel(self.ty(recv), derefs);
        let pl = Self::derefs(self.place(recv), derefs);
        let rt_ty = self.ref_ty(false, recv_ty);
        let rt = self.temp(rt_ty);
        self.assign(Place::local(rt), Rvalue::Ref(false, pl), span);
        let a = Operand::Copy(Place::local(rt).deref());
        let b_ref = self.operand(args[0]);
        let b_pl = self.op_place(b_ref, self.ty(args[0]), span);
        let b = Operand::Copy(b_pl.deref());
        match kind {
            Ck::Op(op) => self.assign(out, Rvalue::Bin(op, a, b), span),
            Ck::Total(adt) | Ck::Partial(adt) => {
                let partial = matches!(kind, Ck::Partial(_));
                let mut cmp = |this: &mut Self, op: BinOp| {
                    let t = this.temp(BOOL);
                    this.assign(Place::local(t), Rvalue::Bin(op, a.clone(), b.clone()), span);
                    t
                };
                let lt = cmp(self, BinOp::Lt);
                let gt = cmp(self, BinOp::Gt);
                let eq = if partial { Some(cmp(self, BinOp::Eq)) } else { None };
                let (ord_ty, ord_pl) = if partial {
                    let t = self.body.tys.option_elem(out_ty).unwrap_or(out_ty);
                    (t, Place::local(self.temp(t)))
                } else {
                    (out_ty, out.clone())
                };
                let _ = ord_ty;
                let (less_b, gt_b, greater_b, eq_b, equal_b, none_b, wrap_b, end) = (
                    self.new_block(),
                    self.new_block(),
                    self.new_block(),
                    self.new_block(),
                    self.new_block(),
                    self.new_block(),
                    self.new_block(),
                    self.new_block(),
                );
                let branch = |this: &mut Self, cond: Local, t: Bb, f: Bb| {
                    let bb = &mut this.body.blocks[this.cur.0 as usize];
                    bb.term = Terminator::If(Operand::Copy(Place::local(cond)), t, f);
                    bb.term_span = span;
                };
                branch(self, lt, less_b, gt_b);
                self.cur = less_b;
                self.assign(ord_pl.clone(), Rvalue::Aggregate(adt, 0, Vec::new()), span);
                self.goto(wrap_b, span);
                self.cur = gt_b;
                branch(self, gt, greater_b, eq_b);
                self.cur = greater_b;
                self.assign(ord_pl.clone(), Rvalue::Aggregate(adt, 2, Vec::new()), span);
                self.goto(wrap_b, span);
                self.cur = eq_b;
                match eq {
                    // `Ord::cmp`: not less and not greater is Equal.
                    None => {
                        self.assign(ord_pl.clone(), Rvalue::Aggregate(adt, 1, Vec::new()), span);
                        self.goto(wrap_b, span);
                    }
                    Some(eq) => branch(self, eq, equal_b, none_b),
                }
                self.cur = equal_b;
                self.assign(ord_pl.clone(), Rvalue::Aggregate(adt, 1, Vec::new()), span);
                self.goto(wrap_b, span);
                self.cur = none_b;
                if partial {
                    self.assign(out.clone(), Rvalue::Opt(out_ty, None), span);
                }
                self.goto(end, span);
                self.cur = wrap_b;
                if partial {
                    self.assign(out, Rvalue::Opt(out_ty, Some(Operand::Copy(ord_pl))), span);
                }
                self.goto(end, span);
                self.cur = end;
            }
        }
    }

    /// A scalar operator trait method (`Res::PrimOp`): the
    /// operation itself on the receiver value (by-value `self`),
    /// a unary operation, or a compound assignment into the
    /// receiver place, exactly as the operators lower.
    fn prim_op_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], dest: Option<&Place>, span: Span, kind: PrimOpKind, derefs: u8) {
        use PrimOpKind as K;
        match kind {
            K::Bin(op) => {
                if args.is_empty() {
                    return;
                }
                let a = self.operand_derefs(recv, derefs);
                let b = self.operand(args[0]);
                let recv_ty = self.peel(self.ty(recv), derefs);
                if op == BinOp::Add && self.body.tys.is_string_ty(recv_ty) {
                    self.set_or_temp(dest, Rvalue::StringAdd(a, b), self.ty(e), span);
                } else {
                    self.set_or_temp(dest, Rvalue::Bin(op, a, b), self.ty(e), span);
                }
            }
            K::Un(op) => {
                let a = self.operand_derefs(recv, derefs);
                self.set_or_temp(dest, Rvalue::Un(op, a), self.ty(e), span);
            }
            K::IntoCast => {
                let a = self.operand_derefs(recv, derefs);
                self.set_or_temp(dest, Rvalue::Cast(a, self.ty(e)), self.ty(e), span);
            }
            K::Assign(op) => {
                if args.is_empty() {
                    return;
                }
                let r = self.operand(args[0]);
                let pl = Self::derefs(self.place_for_mut(recv), derefs);
                self.assign(pl.clone(), Rvalue::Bin(op, Operand::Copy(pl), r), span);
                self.unit(dest, span);
            }
        }
    }

    fn method_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], dest: Option<&Place>, span: Span) {
        if let Res::PrimCmp { kind, derefs } = self.ck.res(e) {
            self.prim_cmp_into(e, recv, args, dest, span, kind, derefs);
            return;
        }
        if let Res::PrimOp { kind, derefs } = self.ck.res(e) {
            self.prim_op_into(e, recv, args, dest, span, kind, derefs);
            return;
        }
        /// What a method call calls once its receiver is in place.
        enum Callee {
            Fn(LocalDefId),
            Builtin(Builtin),
            /// Through the vtable: the declaring trait, its object
            /// candidate index, and the slot.
            Dyn(DefId, u8, u32),
        }
        let (callee, derefs, autoref) = match self.ck.res(e) {
            Res::Method { f, derefs, autoref } => (Callee::Fn(f), derefs, autoref),
            Res::BuiltinMethod { b, derefs, autoref } => (Callee::Builtin(b), derefs, autoref),
            Res::DynMethod { owner, cand, slot, derefs, autoref } => (Callee::Dyn(owner, cand, slot), derefs, autoref),
            _ => return,
        };
        let recv_ty = self.peel(self.ty(recv), derefs);
        let mut ops = Vec::with_capacity(args.len() + 1);
        match autoref {
            Autoref::None => {
                let o = self.operand_derefs(recv, derefs);
                ops.push(o);
                for &a in args {
                    let o = self.operand(a);
                    ops.push(o);
                }
            }
            Autoref::Ref => {
                let pl = self.place(recv);
                let pl = Self::derefs(pl, derefs);
                let rt = self.ref_ty(false, recv_ty);
                let t = self.temp(rt);
                self.assign(Place::local(t), Rvalue::Ref(false, pl), span);
                ops.push(Operand::Copy(Place::local(t)));
                for &a in args {
                    let o = self.operand(a);
                    ops.push(o);
                }
            }
            Autoref::RefMut => {
                let pl = self.place_for_mut(recv);
                let pl = Self::derefs(pl, derefs);
                let mt = self.ref_ty(true, recv_ty);
                if pl.proj.iter().any(|x| matches!(x, Proj::Index(_))) {
                    // The receiver is reached through an `IndexMut` borrow, which is not
                    // two-phase: take the `&mut` before the arguments run, so an argument
                    // that borrows the container again is an error, as in rustc.
                    let t = self.temp(mt);
                    self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
                    ops.push(Operand::Move(Place::local(t)));
                    for &a in args {
                        let o = self.operand(a);
                        // A direct place read in an argument (`v[0][0]`) has no statement
                        // of its own, so the borrow checker would only see it at the call,
                        // after the `&mut` above is dead. Read it into a temporary first.
                        let o = match o {
                            Operand::Copy(pl) if !pl.proj.is_empty() => {
                                let aty = match self.ck.coerce(a) {
                                    Coerce::Deref(n) => self.peel(self.ty(a), n),
                                    Coerce::Unsize(t) => t,
                                    _ => self.ty(a),
                                };
                                let tt = self.temp(aty);
                                self.assign(Place::local(tt), Rvalue::Use(Operand::Copy(pl)), span);
                                self.operand_from(Place::local(tt), aty)
                            }
                            Operand::Move(pl) if !pl.proj.is_empty() => {
                                let aty = self.ty(a);
                                let tt = self.temp(aty);
                                self.assign(Place::local(tt), Rvalue::Use(Operand::Move(pl)), span);
                                self.operand_from(Place::local(tt), aty)
                            }
                            o => o,
                        };
                        ops.push(o);
                    }
                } else {
                    // Two-phase borrow: a shared reservation while the arguments run, then `&mut`.
                    let st = self.ref_ty(false, recv_ty);
                    let reserve = self.temp(st);
                    self.assign(Place::local(reserve), Rvalue::Ref(false, pl.clone()), span);
                    let mut arg_ops = Vec::new();
                    for &a in args {
                        let o = self.operand(a);
                        arg_ops.push(o);
                    }
                    self.push(StmtKind::FakeRead(reserve), span);
                    let t = self.temp(mt);
                    self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
                    ops.push(Operand::Move(Place::local(t)));
                    ops.extend(arg_ops);
                }
            }
        }
        let target = match callee {
            Callee::Fn(f) => CallTarget::Fn(self.resolve_generic_fn(e, f)),
            Callee::Builtin(b) => CallTarget::Builtin(b),
            Callee::Dyn(owner, cand, slot) => {
                let Expr::MethodCall { name, .. } = self.p.ast.expr(e) else { unreachable!() };
                let r = ops.remove(0);
                let r = self.dyn_receiver(r, recv_ty, autoref == Autoref::RefMut, owner, cand, *name, span);
                ops.insert(0, r);
                // The call writes a temporary of the method's own return
                // type: codegen reads the vtable entry's C signature from
                // its destination, and a `!` method's destination may
                // have any type.
                let rt = self.ty(e);
                let t = self.temp(rt);
                self.call_into(CallTarget::Dyn(slot), ops, Place::local(t), span);
                if let Some(d) = dest {
                    let o = self.operand_from(Place::local(t), rt);
                    self.assign(d.clone(), Rvalue::Use(o), span);
                }
                return;
            }
        };
        let d = self.call_dest(dest, self.ty(e));
        self.call_into(target, ops, d, span);
    }

    fn binary_into(&mut self, e: ExprId, op: BinOp, lhs: ExprId, rhs: ExprId, dest: Option<&Place>, span: Span) {
        let ty = self.ty(e);
        let out = match dest {
            Some(d) => d.clone(),
            None => Place::local(self.temp(ty)),
        };
        if let Res::TraitBin { f, ld, rd } = self.ck.res(e) {
            let f = self.resolve_generic_fn(e, f);
            let a = self.operand_derefs(lhs, ld);
            let b = self.operand_derefs(rhs, rd);
            self.call_into(CallTarget::Fn(f), vec![a, b], out, span);
            return;
        }
        if matches!(op, BinOp::And | BinOp::Or) {
            // Short circuit. Both sides write a mutable temporary, and the destination is
            // written once at the end. Writing the destination twice would make the borrow
            // checker see `let hot = a && b;` as two assignments to an immutable binding.
            let tmp = Place::local(self.temp(ty));
            self.expr_into(lhs, Some(&tmp));
            let (rhs_bb, end) = (self.new_block(), self.new_block());
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = if op == BinOp::And {
                Terminator::If(Operand::Copy(tmp.clone()), rhs_bb, end)
            } else {
                Terminator::If(Operand::Copy(tmp.clone()), end, rhs_bb)
            };
            b.term_span = span;
            self.cur = rhs_bb;
            self.scopes.push(Vec::new());
            self.expr_into(rhs, Some(&tmp));
            self.pop_scope(span);
            self.goto(end, span);
            self.assign(out, Rvalue::Use(Operand::Copy(tmp)), span);
            return;
        }
        let (ld, rd) = match self.ck.res(e) {
            Res::Bin { ld, rd } => (ld, rd),
            _ => (0, 0),
        };
        let lt = self.ty(lhs);
        let base = self.peel(lt, ld);
        if op.is_cmp() && !matches!(op, BinOp::Eq | BinOp::Ne) && matches!(self.kind(base), TyKind::Tuple(_) | TyKind::Unit) {
            // Tuple ordering is lexicographic: the first unequal field
            // decides, equal tuples order by the operator's reflexivity.
            let ao = self.operand_derefs(lhs, ld);
            let ap = self.op_place(ao, base, span);
            let bo = self.operand_derefs(rhs, rd);
            let bp = self.op_place(bo, base, span);
            self.ord_into(op, ap, bp, base, out, span);
            return;
        }
        let rv = if op.is_cmp() {
            match self.kind(base) {
                TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char => {
                    let a = self.operand_derefs(lhs, ld);
                    let b = self.operand_derefs(rhs, rd);
                    Rvalue::Bin(op, a, b)
                }
                TyKind::Str => {
                    let a = self.str_view(lhs, ld);
                    let b = self.str_view(rhs, rd);
                    Rvalue::StrCmp(op, a, b)
                }
                _ if self.body.tys.is_string_ty(base) => {
                    let a = self.str_view(lhs, ld);
                    let b = self.str_view(rhs, rd);
                    Rvalue::StrCmp(op, a, b)
                }
                _ => {
                    let (a, t) = self.borrow_of(lhs, ld);
                    let (b, _) = self.borrow_of(rhs, rd);
                    Rvalue::Eq { a, b, ty: t, ne: op == BinOp::Ne }
                }
            }
        } else if self.body.tys.is_string_ty(lt) {
            let a = self.operand(lhs);
            let b = self.operand(rhs);
            Rvalue::StringAdd(a, b)
        } else {
            let a = self.operand_derefs(lhs, ld);
            let b = self.operand_derefs(rhs, rd);
            Rvalue::Bin(op, a, b)
        };
        self.assign(out, rv, span);
    }

    /// True when a destructuring assignment target moves a non-Copy
    /// element out of its source. Leaf targets carry their element
    /// type from the checker, in both checking directions.
    fn assign_moves_noncopy(&self, e: ExprId) -> bool {
        match self.p.ast.expr(e) {
            Expr::Underscore | Expr::Unit => false,
            Expr::Path(_) if matches!(self.ck.res(e), Res::Variant(..)) => false,
            Expr::Tuple(elems) | Expr::Array(elems) => elems.iter().any(|&el| !self.is_rest_elem(el) && self.assign_moves_noncopy(el)),
            Expr::StructLit { fields, .. } => fields.iter().any(|&(_, _, fe)| self.assign_moves_noncopy(fe)),
            Expr::Call { args, .. } if matches!(self.ck.res(e), Res::Variant(..)) => {
                args.iter().any(|&arg| !self.is_rest_elem(arg) && self.assign_moves_noncopy(arg))
            }
            _ => !is_copy(self.p, &self.body.tys, self.ty(e)),
        }
    }

    /// The source place of a destructuring assignment, with the
    /// guard `pattern_place` puts on a pattern scrutinee: a move
    /// out of a place that goes through a written index expression
    /// is a move out of the reference the `Index` trait returns
    /// (rustc E0507/E0508), not the partial move the same
    /// projections mean when the target itself projects them.
    fn assign_pattern_place(&mut self, place: Place, ty: Ty, lhs: ExprId, span: Span) -> Place {
        if !place.proj.iter().any(|x| matches!(x, Proj::Index(_))) || !self.assign_moves_noncopy(lhs) {
            return place;
        }
        let rt = self.ref_ty(false, ty);
        let tmp = self.temp(rt);
        self.assign(Place::local(tmp), Rvalue::Ref(false, place), span);
        Place::local(tmp).deref()
    }

    /// Phase one of a destructuring assignment: move each written
    /// element of the source place into its own temporary, in target
    /// order, and collect the writes. `_`, `()`, a unit variant, and
    /// the elements a `..` rest covers write nothing and stay in the
    /// source place: the caller drops a temporary source next, so a
    /// discarded element of a value drops before the overwritten old
    /// values do, and a discarded element of an owned place stays
    /// in that place.
    fn collect_assign_pattern(&mut self, e: ExprId, src: Place, ty: Ty, span: Span, out: &mut Vec<(ExprId, Place, Ty)>) {
        let p = self.p;
        match p.ast.expr(e) {
            Expr::Underscore | Expr::Unit => {}
            Expr::Path(_) if matches!(self.ck.res(e), Res::Variant(..)) => {}
            Expr::Tuple(elems) => {
                let elem_tys: Vec<Ty> = match self.kind(ty) {
                    TyKind::Tuple(ts) => self.body.tys.tys_of(ts).to_vec(),
                    _ => Vec::new(),
                };
                for (i, el) in self.map_assign_elems(elems, elem_tys.len()) {
                    self.collect_assign_pattern(el, src.project(Proj::Field(i as u32)), elem_tys[i], span, out);
                }
            }
            Expr::Array(elems) => {
                let (elem_ty, arr_len) = match self.kind(ty) {
                    TyKind::Array(el, c) => {
                        let n = match self.body.tys.const_kind(c) {
                            ConstKind::Int(n) => Some(n as u64),
                            _ => None,
                        };
                        (el, n)
                    }
                    TyKind::Slice(el) => (el, None),
                    _ => (ERROR, None),
                };
                let (prefix, suffix): (&[ExprId], &[ExprId]) = match elems.iter().position(|&e| self.is_rest_elem(e)) {
                    Some(r) => (&elems[..r], &elems[r + 1..]),
                    None => (elems, &[]),
                };
                for (i, &el) in prefix.iter().enumerate() {
                    let idx = self.const_usize(i as u64, span);
                    self.collect_assign_pattern(el, src.project(Proj::Index(idx)), elem_ty, span, out);
                }
                for (j, &el) in suffix.iter().enumerate() {
                    if self.is_rest_elem(el) {
                        continue;
                    }
                    let back = (suffix.len() - j) as u64;
                    let idx = self.slice_back_index(&src, back, arr_len, span);
                    self.collect_assign_pattern(el, src.project(Proj::Index(idx)), elem_ty, span, out);
                }
            }
            Expr::StructLit { fields, .. } => {
                let Res::Variant(a, v) = self.ck.res(e) else { return };
                let base = if p.adt(a).is_enum { src.project(Proj::Downcast(v)) } else { src };
                let vfields = &p.adt(a).variants[v as usize].fields;
                for &(fname, _, fe) in fields {
                    if let Some(i) = vfields.iter().position(|f| f.name == fname) {
                        let fty = self.ty(fe);
                        self.collect_assign_pattern(fe, base.project(Proj::Field(i as u32)), fty, span, out);
                    }
                }
            }
            Expr::Call { args, .. } => {
                let Res::Variant(a, v) = self.ck.res(e) else { return };
                let base = if p.adt(a).is_enum { src.project(Proj::Downcast(v)) } else { src };
                let n = p.adt(a).variants[v as usize].fields.len();
                for (i, arg) in self.map_assign_elems(args, n) {
                    let fty = self.ty(arg);
                    self.collect_assign_pattern(arg, base.project(Proj::Field(i as u32)), fty, span, out);
                }
            }
            _ => {
                let t = Place::local(self.temp(ty));
                let op = self.operand_from(src, ty);
                self.assign(t.clone(), Rvalue::Use(op), span);
                out.push((e, t, ty));
            }
        }
    }

    /// A `&str` operand for a String or str place (a tuple field in an
    /// ordering expansion).
    fn str_place_view(&mut self, place: Place, ty: Ty, span: Span) -> Operand {
        let rt = self.ref_ty(false, ty);
        let r = self.temp(rt);
        self.assign(Place::local(r), Rvalue::Ref(false, place), span);
        if self.body.tys.is_string_ty(ty) {
            let t = self.temp(REF_STR);
            self.call_into(CallTarget::Builtin(Builtin::StringAsStr), vec![Operand::Copy(Place::local(r))], Place::local(t), span);
            Operand::Copy(Place::local(t))
        } else {
            Operand::Copy(Place::local(r))
        }
    }

    /// Writes the comparison `a <op> b` for orderable places into
    /// `out`. Tuples expand lexicographically, field by field, with a
    /// short circuit on the first unequal field; equality of nested
    /// tuples expands the same way. The checker gates the shapes this
    /// can see through `has_ord`.
    fn ord_into(&mut self, op: BinOp, a: Place, b: Place, ty: Ty, out: Place, span: Span) {
        match self.kind(ty) {
            TyKind::Unit => {
                self.assign(out, Rvalue::Use(Operand::Const(Const::Bool(matches!(op, BinOp::Eq | BinOp::Le | BinOp::Ge)))), span)
            }
            TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char => {
                let (x, y) = (self.operand_from(a, ty), self.operand_from(b, ty));
                self.assign(out, Rvalue::Bin(op, x, y), span);
            }
            TyKind::Ref(_, _, inner) => self.ord_into(op, a.deref(), b.deref(), inner, out, span),
            TyKind::Str => {
                let (x, y) = (self.str_place_view(a, ty, span), self.str_place_view(b, ty, span));
                self.assign(out, Rvalue::StrCmp(op, x, y), span);
            }
            _ if self.body.tys.is_string_ty(ty) => {
                let (x, y) = (self.str_place_view(a, ty, span), self.str_place_view(b, ty, span));
                self.assign(out, Rvalue::StrCmp(op, x, y), span);
            }
            TyKind::Tuple(ts) => {
                let elems: Vec<Ty> = self.body.tys.tys_of(ts).to_vec();
                let res = Place::local(self.temp(BOOL));
                let end = self.new_block();
                if matches!(op, BinOp::Eq | BinOp::Ne) {
                    self.assign(res.clone(), Rvalue::Use(Operand::Const(Const::Bool(true))), span);
                    for (i, &ety) in elems.iter().enumerate() {
                        if self.kind(ety) == TyKind::Unit {
                            continue;
                        }
                        let eq = Place::local(self.temp(BOOL));
                        self.ord_into(BinOp::Eq, a.project(Proj::Field(i as u32)), b.project(Proj::Field(i as u32)), ety, eq.clone(), span);
                        let (next, fail) = (self.new_block(), self.new_block());
                        let blk = &mut self.body.blocks[self.cur.0 as usize];
                        blk.term = Terminator::If(Operand::Copy(eq), next, fail);
                        blk.term_span = span;
                        self.cur = fail;
                        self.assign(res.clone(), Rvalue::Use(Operand::Const(Const::Bool(false))), span);
                        self.goto(end, span);
                        self.cur = next;
                    }
                    self.goto(end, span);
                    self.cur = end;
                    if op == BinOp::Ne {
                        self.assign(out, Rvalue::Un(crate::ast::UnOp::Not, Operand::Copy(res)), span);
                    } else {
                        self.assign(out, Rvalue::Use(Operand::Copy(res)), span);
                    }
                } else {
                    self.assign(res.clone(), Rvalue::Use(Operand::Const(Const::Bool(matches!(op, BinOp::Le | BinOp::Ge)))), span);
                    for (i, &ety) in elems.iter().enumerate() {
                        if self.kind(ety) == TyKind::Unit {
                            continue;
                        }
                        let (af, bf) = (a.project(Proj::Field(i as u32)), b.project(Proj::Field(i as u32)));
                        let eq = Place::local(self.temp(BOOL));
                        self.ord_into(BinOp::Eq, af.clone(), bf.clone(), ety, eq.clone(), span);
                        let (next, decide) = (self.new_block(), self.new_block());
                        let blk = &mut self.body.blocks[self.cur.0 as usize];
                        blk.term = Terminator::If(Operand::Copy(eq), next, decide);
                        blk.term_span = span;
                        self.cur = decide;
                        self.ord_into(op, af, bf, ety, res.clone(), span);
                        self.goto(end, span);
                        self.cur = next;
                    }
                    self.goto(end, span);
                    self.cur = end;
                    self.assign(out, Rvalue::Use(Operand::Copy(res)), span);
                }
            }
            _ => self.assign(out, Rvalue::Use(Operand::Const(Const::Bool(false))), span),
        }
    }

    /// A `&str` view of a String or str value reached through `n` references.
    fn str_view(&mut self, e: ExprId, n: u8) -> Operand {
        let span = self.span(e);
        let base = self.peel(self.ty(e), n);
        if self.kind(base) == TyKind::Str {
            if n == 0 {
                // The expression itself is a `str` place (`*t` for `t: &str`): borrow it back.
                let (r, _) = self.borrow_of(e, 0);
                return r;
            }
            let p = self.place(e);
            return Operand::Copy(Self::derefs(p, n - 1));
        }
        let (r, _) = self.borrow_of(e, n);
        let t = self.temp(REF_STR);
        self.call_into(CallTarget::Builtin(Builtin::StringAsStr), vec![r], Place::local(t), span);
        Operand::Copy(Place::local(t))
    }

    // ---------- Loops ----------

    fn for_loop(
        &mut self,
        for_e: ExprId,
        label: Option<ast::Label>,
        pat: PatId,
        iter: ExprId,
        body: ast::BlockId,
        span: Span,
        dest: Option<&Place>,
    ) {
        let p = self.p;
        self.scopes.push(Vec::new());
        let item_ty = self.ck.pat_ty(pat);
        let (head, bodyb, exit) = (self.new_block(), self.new_block(), self.new_block());
        // `next` computes the loop variable into this local at the top of each iteration.
        let item = self.temp(item_ty);
        if let Res::ForTrait { into_iter, next } = self.ck.res(for_e) {
            // `for x in it`: into_iter() then next() until None,
            // the Chars arm's shape with user methods.
            let next_f = self.resolve_generic_fn(iter, next);
            // The std blanket IntoIterator is synthetic with the
            // sentinel id: the receiver is already the iterator.
            let (iter_ty, it) = if into_iter.0 == u32::MAX {
                let it = self.temp(self.ty(iter));
                self.expr_into(iter, Some(&Place::local(it)));
                (self.ty(iter), it)
            } else {
                let into_f = self.resolve_generic_fn(for_e, into_iter);
                let iter_ty = p.fn_info(into_f).ret;
                let src = self.temp(self.ty(iter));
                self.expr_into(iter, Some(&Place::local(src)));
                let it = self.temp(iter_ty);
                let src_op = self.operand_from(Place::local(src), self.ty(iter));
                self.call_into(CallTarget::Fn(into_f), vec![src_op], Place::local(it), span);
                (iter_ty, it)
            };
            self.goto(head, span);
            let mt = self.ref_ty(true, iter_ty);
            let r = self.temp(mt);
            self.assign(Place::local(r), Rvalue::Ref(true, Place::local(it)), span);
            let ot = p.fn_info(next_f).ret;
            let nx = self.temp(ot);
            self.call_into(CallTarget::Fn(next_f), vec![Operand::Move(Place::local(r))], Place::local(nx), span);
            let d = self.temp(int(IntTy::U32));
            self.assign(Place::local(d), Rvalue::Discriminant(Place::local(nx)), span);
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(1, bodyb)], exit);
            self.cur = bodyb;
            let c = Place::local(nx).project(Proj::Downcast(1)).project(Proj::Field(0));
            let op = self.operand_from(c, item_ty);
            self.assign(Place::local(item), Rvalue::Use(op), span);
        } else if let Expr::Range { lo, hi, inclusive } = p.ast.expr(iter) {
            let (lo, hi) = (lo.unwrap(), hi.unwrap());
            let cur = self.temp(item_ty);
            self.expr_into(lo, Some(&Place::local(cur)));
            let end = self.temp(item_ty);
            self.expr_into(hi, Some(&Place::local(end)));
            let done = self.temp(BOOL);
            self.assign(Place::local(done), Rvalue::Use(Operand::Const(Const::Bool(false))), span);
            self.goto(head, span);
            // head: if !done && cur < end (or <=)
            let c = self.temp(BOOL);
            let cmp = if *inclusive { BinOp::Le } else { BinOp::Lt };
            self.assign(Place::local(c), Rvalue::Bin(cmp, Operand::Copy(Place::local(cur)), Operand::Copy(Place::local(end))), span);
            let check_done = self.new_block();
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), check_done, exit);
            self.cur = check_done;
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(done)), exit, bodyb);
            self.cur = bodyb;
            self.assign(Place::local(item), Rvalue::Use(Operand::Copy(Place::local(cur))), span);
            // Advance before the body, so `continue` can jump straight to `head`.
            let (inc, stop, after) = (self.new_block(), self.new_block(), self.new_block());
            let eq = self.temp(BOOL);
            self.assign(Place::local(eq), Rvalue::Bin(BinOp::Eq, Operand::Copy(Place::local(cur)), Operand::Copy(Place::local(end))), span);
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(eq)), stop, inc);
            self.cur = stop;
            self.assign(Place::local(done), Rvalue::Use(Operand::Const(Const::Bool(true))), span);
            self.goto(after, span);
            self.cur = inc;
            let one = match self.kind(item_ty) {
                TyKind::Int(it) => Const::Int(1, it),
                _ => Const::Int(1, IntTy::I32),
            };
            self.assign(Place::local(cur), Rvalue::Bin(BinOp::Add, Operand::Copy(Place::local(cur)), Operand::Const(one)), span);
            self.goto(after, span);
        } else if self.body.tys.is_chars_ty(self.ty(iter)) {
            // `for c in s.chars()`: call `next` until it returns None.
            let it = self.temp(self.ty(iter));
            self.expr_into(iter, Some(&Place::local(it)));
            self.goto(head, span);
            let mt = self.ref_ty(true, self.ty(iter));
            let r = self.temp(mt);
            self.assign(Place::local(r), Rvalue::Ref(true, Place::local(it)), span);
            let ot = self.body.tys.mk_option(CHAR);
            let nx = self.temp(ot);
            self.call_into(CallTarget::Builtin(Builtin::CharsNext), vec![Operand::Move(Place::local(r))], Place::local(nx), span);
            let d = self.temp(int(IntTy::U32));
            self.assign(Place::local(d), Rvalue::Discriminant(Place::local(nx)), span);
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(1, bodyb)], exit);
            self.cur = bodyb;
            let c = Place::local(nx).project(Proj::Downcast(1)).project(Proj::Field(0));
            self.assign(Place::local(item), Rvalue::Use(Operand::Copy(c)), span);
        } else if self.body.tys.vec_elem(self.ty(iter)).is_some() {
            // `for x in v` by value: move the Vec into a temporary
            // and remove each front element in turn. Removing (not
            // indexing) keeps the temporary's own drop exact on
            // `break`, `return`, and `?` exits from the body: what
            // is left in it is exactly what still must drop.
            let vt = self.ty(iter);
            let it = self.temp(vt);
            self.expr_into(iter, Some(&Place::local(it)));
            self.goto(head, span);
            let sref_t = self.ref_ty(false, vt);
            let sref = self.temp(sref_t);
            self.assign(Place::local(sref), Rvalue::Ref(false, Place::local(it)), span);
            let ln = self.temp(USIZE);
            self.call_into(CallTarget::Builtin(Builtin::VecLen), vec![Operand::Copy(Place::local(sref))], Place::local(ln), span);
            let c = self.temp(BOOL);
            self.assign(
                Place::local(c),
                Rvalue::Bin(BinOp::Lt, Operand::Const(Const::Int(0, IntTy::Usize)), Operand::Copy(Place::local(ln))),
                span,
            );
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), bodyb, exit);
            b.term_span = span;
            self.cur = bodyb;
            let mref_t = self.ref_ty(true, vt);
            let mref = self.temp(mref_t);
            self.assign(Place::local(mref), Rvalue::Ref(true, Place::local(it)), span);
            let zero = self.const_usize(0, span);
            self.call_into(
                CallTarget::Builtin(Builtin::VecRemove),
                vec![Operand::Move(Place::local(mref)), Operand::Copy(Place::local(zero))],
                Place::local(item),
                span,
            );
        } else {
            // `for x in &v` / `&mut v`: index loop over a reference held for the whole loop.
            let it_ty = self.ty(iter);
            let by_value_array = matches!(self.kind(it_ty), TyKind::Array(..));
            let m = matches!(self.kind(it_ty), TyKind::Ref(_, Mut::Mut, _));
            let vref = self.temp(it_ty);
            self.expr_into(iter, Some(&Place::local(vref)));
            // By-value iteration over an array of non-Copy elements moves
            // each element out once. A dynamic index loop cannot express
            // that to the borrow checker, so small arrays unroll: one
            // copy of the body per element, each moving its own const
            // index. Larger non-Copy arrays keep the index loop and are
            // rejected by the borrow checker for now.
            if by_value_array && !is_copy(self.p, &self.body.tys, item_ty) {
                let n = match self.kind(it_ty) {
                    TyKind::Array(_, c) => match self.body.tys.const_kind(c) {
                        ConstKind::Int(n) => Some(n as usize),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(n) = n.filter(|&n| n <= 32) {
                    let heads: Vec<Bb> = (0..n).map(|_| self.new_block()).collect();
                    self.goto(heads.first().copied().unwrap_or(exit), span);
                    for (i, &hb) in heads.iter().enumerate() {
                        self.cur = hb;
                        let idx = self.const_usize(i as u64, span);
                        let elem = Place::local(vref).project(Proj::Index(idx));
                        let op = self.operand_from(elem, item_ty);
                        self.assign(Place::local(item), Rvalue::Use(op), span);
                        let next = heads.get(i + 1).copied().unwrap_or(exit);
                        self.scopes.push(Vec::new());
                        self.bind_pat(pat, Place::local(item));
                        self.loops.push(LoopInfo {
                            break_bb: exit,
                            continue_bb: next,
                            dest: None,
                            depth: self.scopes.len() - 1,
                            label: label.map(|l| (l.name, l.span)),
                            is_block: false,
                        });
                        self.block_into(body, None);
                        self.loops.pop();
                        self.pop_scope(span);
                        self.goto(next, span);
                    }
                    self.cur = exit;
                    self.pop_scope(span);
                    self.unit(dest, span);
                    return;
                }
            }
            let len = self.temp(USIZE);
            if by_value_array {
                let n = match self.kind(it_ty) {
                    TyKind::Array(_, c) => match self.body.tys.const_kind(c) {
                        ConstKind::Int(n) => n as u64,
                        _ => 0,
                    },
                    _ => 0,
                };
                self.assign(Place::local(len), Rvalue::Use(Operand::Const(Const::Int(n as u128, IntTy::Usize))), span);
            } else {
                let shared = self.ref_ty(false, self.peel(it_ty, 1));
                let sref = self.temp(shared);
                self.assign(Place::local(sref), Rvalue::Ref(false, Place::local(vref).deref()), span);
                let len_builtin = if self.body.tys.vec_elem(self.peel(it_ty, 1)).is_some() { Builtin::VecLen } else { Builtin::SliceLen };
                self.call_into(CallTarget::Builtin(len_builtin), vec![Operand::Copy(Place::local(sref))], Place::local(len), span);
            }
            let idx = self.temp(USIZE);
            self.assign(Place::local(idx), Rvalue::Use(Operand::Const(Const::Int(0, IntTy::Usize))), span);
            self.goto(head, span);
            let c = self.temp(BOOL);
            self.assign(Place::local(c), Rvalue::Bin(BinOp::Lt, Operand::Copy(Place::local(idx)), Operand::Copy(Place::local(len))), span);
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), bodyb, exit);
            self.cur = bodyb;
            if by_value_array {
                let elem = Place::local(vref).project(Proj::Index(idx));
                let op = self.operand_from(elem, item_ty);
                self.assign(Place::local(item), Rvalue::Use(op), span);
            } else {
                let elem = Place::local(vref).deref().project(Proj::Index(idx));
                self.assign(Place::local(item), Rvalue::Ref(m, elem), span);
            }
            self.assign(
                Place::local(idx),
                Rvalue::Bin(BinOp::Add, Operand::Copy(Place::local(idx)), Operand::Const(Const::Int(1, IntTy::Usize))),
                span,
            );
        }
        self.scopes.push(Vec::new());
        self.bind_pat(pat, Place::local(item));
        self.loops.push(LoopInfo {
            break_bb: exit,
            continue_bb: head,
            dest: None,
            depth: self.scopes.len() - 1,
            label: label.map(|l| (l.name, l.span)),
            is_block: false,
        });
        self.block_into(body, None);
        self.loops.pop();
        self.pop_scope(span);
        self.goto(head, span);
        self.cur = exit;
        self.pop_scope(span);
        self.unit(dest, span);
    }

    /// True when `pat` has a binding that moves a non-Copy part
    /// out of the value it matches.
    fn pat_moves_noncopy(&self, pat: PatId) -> bool {
        let binding_moves = |this: &Self, pat: PatId| {
            matches!(this.ck.pat_res(pat), PatRes::Binding { mode: BindMode::Move, .. })
                && !is_copy(this.p, &this.body.tys, this.ck.pat_ty(pat))
        };
        match self.p.ast.pat(pat) {
            Pat::Binding { .. } => binding_moves(self, pat),
            Pat::At { inner, .. } => binding_moves(self, pat) || self.pat_moves_noncopy(*inner),
            Pat::TupleStruct { elems, .. } | Pat::Tuple(elems) | Pat::Or(elems) => elems.iter().any(|&s| self.pat_moves_noncopy(s)),
            Pat::Struct { fields, .. } => fields.iter().any(|&(_, s)| self.pat_moves_noncopy(s)),
            Pat::Slice { prefix, middle, suffix } => {
                middle.is_some_and(|m| self.pat_moves_noncopy(m))
                    || prefix.iter().chain(suffix.iter()).any(|&s| self.pat_moves_noncopy(s))
            }
            Pat::Paren(i) | Pat::Ref { inner: i, .. } => self.pat_moves_noncopy(*i),
            _ => false,
        }
    }

    /// The place a pattern binds out of, when `place` came from a
    /// place expression. A move out of a place that goes through
    /// an index expression is a move out of the reference the
    /// `Index` trait returns (rustc E0507/E0508), not the partial
    /// move the same projections mean when a pattern projects
    /// them: route such a place through a shared borrow temporary
    /// so the borrow checker reports the move, as `operand_raw`
    /// does for operand reads. When no pattern in `pats` moves a
    /// non-Copy part (tests only, `ref` bindings, Copy bindings),
    /// the direct place stays, so those matches work as before.
    fn pattern_place(&mut self, place: Place, ty: Ty, pats: &[PatId], span: Span) -> Place {
        if !place.proj.iter().any(|x| matches!(x, Proj::Index(_))) || !pats.iter().any(|&pat| self.pat_moves_noncopy(pat)) {
            return place;
        }
        let rt = self.ref_ty(false, ty);
        let tmp = self.temp(rt);
        self.assign(Place::local(tmp), Rvalue::Ref(false, place), span);
        Place::local(tmp).deref()
    }

    // ---------- Match ----------

    fn match_into(&mut self, scrut: ExprId, arms: &[ast::Arm], dest: Option<&Place>, span: Span) {
        // Temporaries in the scrutinee live until the end of the match.
        self.scopes.push(Vec::new());
        // Arms bind out of the scrutinee place itself, as in rustc: an
        // arm that moves a part is a partial move of that place, and
        // the rest drops with it (codegen elaborates the drop).
        let sp = self.place(scrut);
        let arm_pats: Vec<PatId> = arms.iter().map(|a| a.pat).collect();
        let sp = self.pattern_place(sp, self.ty(scrut), &arm_pats, span);
        let end = self.new_block();
        for arm in arms {
            let next = self.new_block();
            self.test_pat(arm.pat, sp.clone(), next);
            self.scopes.push(Vec::new());
            // A guard reads the arm's bindings by shared reference
            // (rustc binds pattern variables by reference for the
            // guard, then by their declared mode in the arm body):
            // bind for the guard first, and do the real binding,
            // moves included, only on the guard's success edge. A
            // failed guard then leaves the scrutinee whole for the
            // next arm. The one shape with no reference place to
            // read through, a binding for the middle of a slice
            // pattern, keeps the move-first order for now.
            let by_ref_guard = arm.guard.is_some() && !self.pat_has_slice_middle_binding(arm.pat);
            let mut guard_bound: Vec<u32> = Vec::new();
            if by_ref_guard {
                self.scopes.push(Vec::new());
                self.bind_pat_guard(arm.pat, sp.clone(), &mut guard_bound);
            } else {
                self.bind_pat(arm.pat, sp.clone());
            }
            if let Some(g) = arm.guard {
                let gspan = self.span(g);
                self.scopes.push(Vec::new());
                let c = self.operand(g);
                // Mutable: the same local is written again on every
                // pass when the match sits in a loop.
                let cl = self.new_local(BOOL, true, None);
                self.assign(Place::local(cl), Rvalue::Use(c), gspan);
                self.pop_scope(gspan);
                for l in &guard_bound {
                    self.guard_places[*l as usize] = None;
                }
                let (ok, fail) = (self.new_block(), self.new_block());
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::If(Operand::Copy(Place::local(cl)), ok, fail);
                self.cur = fail;
                let arm_locals = self.scopes.last().unwrap().clone();
                self.emit_drops(&arm_locals, gspan);
                self.goto(next, gspan);
                self.cur = ok;
                if by_ref_guard {
                    // End the guard bindings' storage before the
                    // real binding moves out of the same places.
                    self.emit_drops(&arm_locals, gspan);
                    self.scopes.pop();
                    self.bind_pat(arm.pat, sp.clone());
                }
            }
            self.expr_into(arm.body, dest);
            self.pop_scope(span);
            self.goto(end, span);
            self.cur = next;
        }
        self.terminate(Terminator::Unreachable, span);
        self.cur = end;
        self.pop_scope(span);
    }

    /// True when a slice pattern in `pat` binds its middle (`rest`
    /// or `rest @ ..`). That binding has no single place to read by
    /// reference for a guard, so `match_into` keeps the old
    /// move-first order for such an arm.
    fn pat_has_slice_middle_binding(&self, pat: PatId) -> bool {
        fn binds(p: &Program, pat: PatId) -> bool {
            match p.ast.pat(pat) {
                Pat::Binding { .. } | Pat::At { .. } => true,
                Pat::Paren(i) | Pat::Ref { inner: i, .. } => binds(p, *i),
                _ => false,
            }
        }
        fn walk(p: &Program, pat: PatId) -> bool {
            match p.ast.pat(pat) {
                Pat::Slice { prefix, middle, suffix } => {
                    middle.is_some_and(|m| binds(p, m) || walk(p, m))
                        || prefix.iter().chain(suffix.iter()).any(|&s| walk(p, s))
                }
                Pat::TupleStruct { elems, .. } | Pat::Tuple(elems) | Pat::Or(elems) => elems.iter().any(|&s| walk(p, s)),
                Pat::Struct { fields, .. } => fields.iter().any(|&(_, s)| walk(p, s)),
                Pat::Paren(i) | Pat::Ref { inner: i, .. } | Pat::At { inner: i, .. } => walk(p, *i),
                _ => false,
            }
        }
        walk(self.p, pat)
    }

    /// Records one pattern binding for guard evaluation: a fresh
    /// shared-reference local that borrows `place`, with
    /// `guard_places` set so the guard reads the binding through
    /// it. A move binding reads the value at `*tmp` (a move out of
    /// it in the guard is then a move out of a reference, and a
    /// mutable borrow of it borrows through a shared reference:
    /// both errors, as in rustc); a `ref` binding, whose value is
    /// itself a reference, reads as the local holding a shared
    /// borrow of the same place. The temporaries go in the
    /// innermost scope and need no drop.
    fn guard_binding(&mut self, local: u32, mode: BindMode, value_ty: Ty, place: Place, span: Span, bound: &mut Vec<u32>) {
        let name = self.p.name(self.ck.locals[local as usize].name).to_string();
        let rt = self.ref_ty(false, value_ty);
        let t = self.new_local(rt, false, Some(name));
        self.scopes.last_mut().unwrap().push(t);
        self.assign(Place::local(t), Rvalue::Ref(false, place), span);
        self.guard_places[local as usize] = Some(match mode {
            BindMode::Move => Place::local(t).deref(),
            BindMode::Ref(_) => Place::local(t),
        });
        bound.push(local);
    }

    /// Binds an already-tested pattern for a match guard, mirroring
    /// `bind_pat` case by case, but by shared reference (see
    /// `guard_binding`). Records every bound checker local in
    /// `bound` so the caller can clear `guard_places` after the
    /// guard. A slice middle binding never reaches here (see
    /// `pat_has_slice_middle_binding`).
    fn bind_pat_guard(&mut self, pat: PatId, place: Place, bound: &mut Vec<u32>) {
        let p = self.p;
        let place = Self::derefs(place, self.ck.pat_derefs(pat));
        let span = p.ast.pat_span(pat);
        match (p.ast.pat(pat), self.ck.pat_res(pat)) {
            (Pat::Binding { .. }, PatRes::Binding { local, mode }) => {
                self.guard_binding(local, mode, self.ck.pat_ty(pat), place, span, bound);
            }
            (Pat::TupleStruct { elems, .. }, PatRes::Opt(true)) => {
                self.bind_pat_guard(elems[0], place.project(Proj::Downcast(1)).project(Proj::Field(0)), bound);
            }
            (Pat::TupleStruct { elems, .. }, PatRes::Res(is_ok)) => {
                self.bind_pat_guard(elems[0], place.project(Proj::Downcast((!is_ok) as u32)).project(Proj::Field(0)), bound);
            }
            (Pat::TupleStruct { .. } | Pat::Struct { .. }, PatRes::Variant(a, v)) => {
                let base = if p.adt(a).is_enum { place.project(Proj::Downcast(v)) } else { place };
                for (i, sub) in self.sub_pats(pat, a, v) {
                    self.bind_pat_guard(sub, base.project(Proj::Field(i)), bound);
                }
            }
            (Pat::Tuple(elems), _) => {
                let ty = self.ck.pat_ty(pat);
                let n = match self.kind(ty) {
                    TyKind::Tuple(ts) => self.body.tys.tys_of(ts).len(),
                    _ => elems.len(),
                };
                if let Some(mapped) = crate::check::map_tuple_elems(p.ast, elems, n) {
                    for (i, sub) in mapped {
                        self.bind_pat_guard(sub, place.project(Proj::Field(i as u32)), bound);
                    }
                }
            }
            (Pat::Paren(inner), _) => self.bind_pat_guard(*inner, place, bound),
            (Pat::Slice { prefix, middle: _, suffix }, _) => {
                let ty = self.ck.pat_ty(pat);
                let arr_len = match self.kind(ty) {
                    TyKind::Array(_, c) => match self.body.tys.const_kind(c) {
                        ConstKind::Int(n) => Some(n as u64),
                        _ => None,
                    },
                    _ => None,
                };
                for (i, &sub) in prefix.iter().enumerate() {
                    let idx = self.const_usize(i as u64, span);
                    self.bind_pat_guard(sub, place.project(Proj::Index(idx)), bound);
                }
                for (j, &sub) in suffix.iter().enumerate() {
                    let back = (suffix.len() - j) as u64;
                    let idx = self.slice_back_index(&place, back, arr_len, span);
                    self.bind_pat_guard(sub, place.project(Proj::Index(idx)), bound);
                }
            }
            (Pat::Ref { inner, .. }, _) => self.bind_pat_guard(*inner, place.deref(), bound),
            (Pat::At { inner, .. }, PatRes::Binding { local, mode }) => {
                self.bind_pat_guard(*inner, place.clone(), bound);
                self.guard_binding(local, mode, self.ck.pat_ty(pat), place, span, bound);
            }
            _ => {}
        }
    }

    fn lit_operand(&mut self, l: ExprId, ty: Ty) -> Operand {
        match self.p.ast.expr(l) {
            Expr::Unary { expr, .. } => match (self.p.ast.expr(*expr), self.kind(ty)) {
                (Expr::Int(v, _), TyKind::Int(it)) => Operand::Const(Const::Int(v.wrapping_neg(), it)),
                _ => Operand::Const(Const::Unit),
            },
            Expr::Int(v, _) => match self.kind(ty) {
                TyKind::Int(it) => Operand::Const(Const::Int(*v, it)),
                _ => Operand::Const(Const::Int(*v, IntTy::I32)),
            },
            Expr::Float(i) => {
                let text = &self.p.ast.strings[*i as usize];
                let ft = match self.kind(ty) {
                    TyKind::Float(f) => f,
                    _ => FloatTy::F64,
                };
                // Parse straight to the literal's type: one rounding.
                match crate::check::collect::parse_float_literal_as(text, ft) {
                    Some(bits) => Operand::Const(Const::Float(bits, ft)),
                    None => Operand::Const(Const::Unit),
                }
            }
            Expr::Bool(b) => Operand::Const(Const::Bool(*b)),
            Expr::Char(c) => Operand::Const(Const::Char(*c)),
            Expr::Str(s) => Operand::Const(Const::Str(*s)),
            Expr::Path(_) => self.operand_raw(l),
            _ => Operand::Const(Const::Unit),
        }
    }

    /// A usize local holding a constant, for slice pattern indexes.
    fn const_usize(&mut self, v: u64, span: Span) -> Local {
        let t = self.temp(USIZE);
        self.assign(Place::local(t), Rvalue::Use(Operand::Const(Const::Int(v as u128, IntTy::Usize))), span);
        t
    }

    /// The index local for an element `back` positions from the end of a
    /// slice or array place.
    fn slice_back_index(&mut self, place: &Place, back: u64, arr_len: Option<u64>, span: Span) -> Local {
        match arr_len {
            Some(n) => self.const_usize(n - back, span),
            None => {
                let len = self.temp(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(place.clone()), span);
                let idx = self.temp(USIZE);
                self.assign(
                    Place::local(idx),
                    Rvalue::Bin(BinOp::Sub, Operand::Copy(Place::local(len)), Operand::Const(Const::Int(back as u128, IntTy::Usize))),
                    span,
                );
                idx
            }
        }
    }

    /// Emits tests for `pat` against `place`. Falls through on a match; jumps to `fail` otherwise.
    fn test_pat(&mut self, pat: PatId, place: Place, fail: Bb) {
        let p = self.p;
        let place = Self::derefs(place, self.ck.pat_derefs(pat));
        let ty = self.ck.pat_ty(pat);
        let span = p.ast.pat_span(pat);
        if let PatRes::Opt(some) = self.ck.pat_res(pat) {
            let d = self.temp(int(IntTy::U32));
            self.assign(Place::local(d), Rvalue::Discriminant(place.clone()), span);
            let ok = self.new_block();
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(some as u32, ok)], fail);
            self.cur = ok;
            if let (true, Pat::TupleStruct { elems, .. }) = (some, p.ast.pat(pat)) {
                self.test_pat(elems[0], place.project(Proj::Downcast(1)).project(Proj::Field(0)), fail);
            }
            return;
        }
        if let PatRes::Res(is_ok) = self.ck.pat_res(pat) {
            let d = self.temp(int(IntTy::U32));
            self.assign(Place::local(d), Rvalue::Discriminant(place.clone()), span);
            let ok = self.new_block();
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![((!is_ok) as u32, ok)], fail);
            self.cur = ok;
            if let Pat::TupleStruct { elems, .. } = p.ast.pat(pat) {
                self.test_pat(elems[0], place.project(Proj::Downcast((!is_ok) as u32)).project(Proj::Field(0)), fail);
            }
            return;
        }
        let const_pat = match self.ck.pat_res(pat) {
            PatRes::ConstItem(idx) => Some(p.consts[idx as usize].value.clone()),
            PatRes::PrimConst(v) => Some(crate::ty::consteval::ConstValue::Int(v)),
            PatRes::BodyConst(idx) => Some(p.body_consts[idx as usize].value.clone()),
            _ => None,
        };
        if let Some(cv) = const_pat {
            let op = self.const_operand(&cv, ty, span);
            let c = self.temp(BOOL);
            let cond = if matches!(cv, crate::ty::consteval::ConstValue::Str(_)) {
                Rvalue::StrCmp(BinOp::Eq, Operand::Copy(place), op)
            } else {
                Rvalue::Bin(BinOp::Eq, Operand::Copy(place), op)
            };
            self.assign(Place::local(c), cond, span);
            let ok = self.new_block();
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), ok, fail);
            self.cur = ok;
            return;
        }
        if let Some(cv) = self.ck.pat_const(pat).cloned() {
            let op = self.const_operand(&cv, ty, span);
            let c = self.temp(BOOL);
            self.assign(Place::local(c), Rvalue::Bin(BinOp::Eq, Operand::Copy(place), op), span);
            let ok = self.new_block();
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), ok, fail);
            self.cur = ok;
            return;
        }
        // A lone identifier that resolved to a unit variant tests the
        // discriminant, exactly like the written path form.
        if let (Pat::Binding { .. }, PatRes::Variant(a, v)) = (p.ast.pat(pat), self.ck.pat_res(pat))
            && p.adt(a).is_enum
        {
            let d = self.temp(int(IntTy::U32));
            self.assign(Place::local(d), Rvalue::Discriminant(place), span);
            let ok = self.new_block();
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(v, ok)], fail);
            self.cur = ok;
            return;
        }
        let branch = |this: &mut Self, cond: Rvalue| {
            let c = this.temp(BOOL);
            this.assign(Place::local(c), cond, span);
            let ok = this.new_block();
            let b = &mut this.body.blocks[this.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), ok, fail);
            this.cur = ok;
        };
        match p.ast.pat(pat) {
            Pat::Wild | Pat::Binding { .. } => {}
            Pat::Lit(l) => {
                let lit = self.lit_operand(*l, ty);
                if matches!(lit, Operand::Const(Const::Str(_))) {
                    branch(self, Rvalue::StrCmp(BinOp::Eq, Operand::Copy(place), lit));
                } else {
                    branch(self, Rvalue::Bin(BinOp::Eq, Operand::Copy(place), lit));
                }
            }
            Pat::Range { lo, hi, inclusive } => {
                if let Some(lo) = lo {
                    let a = self.lit_operand(*lo, ty);
                    branch(self, Rvalue::Bin(BinOp::Ge, Operand::Copy(place.clone()), a));
                }
                if let Some(hi) = hi {
                    let b = self.lit_operand(*hi, ty);
                    let op = if *inclusive { BinOp::Le } else { BinOp::Lt };
                    branch(self, Rvalue::Bin(op, Operand::Copy(place), b));
                }
            }
            Pat::Slice { prefix, middle, suffix } => {
                let fixed = (prefix.len() + suffix.len()) as u64;
                let arr_len = match self.kind(ty) {
                    TyKind::Array(_, c) => match self.body.tys.const_kind(c) {
                        ConstKind::Int(n) => Some(n as u64),
                        _ => None,
                    },
                    _ => None,
                };
                if arr_len.is_none() {
                    // A slice place needs a runtime length test.
                    let len = self.temp(USIZE);
                    self.assign(Place::local(len), Rvalue::LenOf(place.clone()), span);
                    let op = if middle.is_some() { BinOp::Ge } else { BinOp::Eq };
                    branch(
                        self,
                        Rvalue::Bin(op, Operand::Copy(Place::local(len)), Operand::Const(Const::Int(fixed as u128, IntTy::Usize))),
                    );
                }
                for (i, &sub) in prefix.iter().enumerate() {
                    let idx = self.const_usize(i as u64, span);
                    self.test_pat(sub, place.project(Proj::Index(idx)), fail);
                }
                for (j, &sub) in suffix.iter().enumerate() {
                    let back = (suffix.len() - j) as u64;
                    let idx = self.slice_back_index(&place, back, arr_len, span);
                    self.test_pat(sub, place.project(Proj::Index(idx)), fail);
                }
            }
            Pat::Path(_) | Pat::TupleStruct { .. } | Pat::Struct { .. } => {
                let PatRes::Variant(a, v) = self.ck.pat_res(pat) else { return };
                let is_enum = p.adt(a).is_enum;
                if is_enum {
                    let d = self.temp(int(IntTy::U32));
                    self.assign(Place::local(d), Rvalue::Discriminant(place.clone()), span);
                    let ok = self.new_block();
                    let b = &mut self.body.blocks[self.cur.0 as usize];
                    b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(v, ok)], fail);
                    self.cur = ok;
                }
                let base = if is_enum { place.project(Proj::Downcast(v)) } else { place };
                for (i, sub) in self.sub_pats(pat, a, v) {
                    self.test_pat(sub, base.project(Proj::Field(i)), fail);
                }
            }
            Pat::Or(alts) => {
                let cont = self.new_block();
                for &alt in alts {
                    let next = self.new_block();
                    self.test_pat(alt, place.clone(), next);
                    self.goto(cont, span);
                    self.cur = next;
                }
                self.terminate(Terminator::Goto(fail), span);
                self.cur = cont;
            }
            Pat::Tuple(elems) => {
                let n = match self.kind(ty) {
                    TyKind::Tuple(ts) => self.body.tys.tys_of(ts).len(),
                    _ => elems.len(),
                };
                if let Some(mapped) = crate::check::map_tuple_elems(p.ast, elems, n) {
                    for (i, sub) in mapped {
                        self.test_pat(sub, place.project(Proj::Field(i as u32)), fail);
                    }
                }
            }
            Pat::Rest => {}
            Pat::Paren(inner) => self.test_pat(*inner, place, fail),
            Pat::At { inner, .. } => self.test_pat(*inner, place, fail),
            Pat::Ref { inner, .. } => self.test_pat(*inner, place.deref(), fail),
            // AST v2 pattern forms the parser still rejects.
            Pat::Slice { .. } | Pat::QPath { .. } | Pat::MacroCall(_) => {}
        }
    }

    /// Sub-patterns of a struct or variant pattern, with their field indexes.
    fn sub_pats(&self, pat: PatId, a: AdtId, v: u32) -> Vec<(u32, PatId)> {
        let p = self.p;
        match p.ast.pat(pat) {
            Pat::TupleStruct { elems, .. } => {
                let n = p.adt(a).variants[v as usize].fields.len();
                crate::check::map_tuple_elems(p.ast, elems, n).unwrap_or_default().into_iter().map(|(i, s)| (i as u32, s)).collect()
            }
            Pat::Struct { fields, .. } => {
                let vf = &p.adt(a).variants[v as usize].fields;
                fields.iter().filter_map(|&(n, s)| vf.iter().position(|f| f.name == n).map(|i| (i as u32, s))).collect()
            }
            _ => Vec::new(),
        }
    }

    /// Binds the variables of an already-tested pattern.
    fn bind_pat(&mut self, pat: PatId, place: Place) {
        let p = self.p;
        let place = Self::derefs(place, self.ck.pat_derefs(pat));
        let span = p.ast.pat_span(pat);
        match (p.ast.pat(pat), self.ck.pat_res(pat)) {
            (Pat::Binding { .. }, PatRes::Binding { local, mode }) => {
                let info = &self.ck.locals[local as usize];
                let (ty, m, name) = (info.ty, info.mutable, p.name(info.name).to_string());
                let l = self.new_local(ty, m, Some(name));
                self.local_map[local as usize] = l;
                let rv = match mode {
                    BindMode::Move => Rvalue::Use(self.operand_from(place, self.ck.pat_ty(pat))),
                    BindMode::Ref(m) => Rvalue::Ref(m, place),
                };
                self.assign(Place::local(l), rv, span);
                self.scopes.last_mut().unwrap().push(l);
            }
            (Pat::TupleStruct { elems, .. }, PatRes::Opt(true)) => {
                self.bind_pat(elems[0], place.project(Proj::Downcast(1)).project(Proj::Field(0)));
            }
            (Pat::TupleStruct { elems, .. }, PatRes::Res(is_ok)) => {
                self.bind_pat(elems[0], place.project(Proj::Downcast((!is_ok) as u32)).project(Proj::Field(0)));
            }
            (Pat::TupleStruct { .. } | Pat::Struct { .. }, PatRes::Variant(a, v)) => {
                let base = if p.adt(a).is_enum { place.project(Proj::Downcast(v)) } else { place };
                for (i, sub) in self.sub_pats(pat, a, v) {
                    self.bind_pat(sub, base.project(Proj::Field(i)));
                }
            }
            (Pat::Tuple(elems), _) => {
                let ty = self.ck.pat_ty(pat);
                let n = match self.kind(ty) {
                    TyKind::Tuple(ts) => self.body.tys.tys_of(ts).len(),
                    _ => elems.len(),
                };
                if let Some(mapped) = crate::check::map_tuple_elems(p.ast, elems, n) {
                    for (i, sub) in mapped {
                        self.bind_pat(sub, place.project(Proj::Field(i as u32)));
                    }
                }
            }
            (Pat::Paren(inner), _) => self.bind_pat(*inner, place),
            (Pat::Slice { prefix, middle, suffix }, _) => {
                let ty = self.ck.pat_ty(pat);
                let (elem, arr_len) = match self.kind(ty) {
                    TyKind::Array(e, c) => {
                        let n = match self.body.tys.const_kind(c) {
                            ConstKind::Int(n) => Some(n as u64),
                            _ => None,
                        };
                        (e, n)
                    }
                    TyKind::Slice(e) => (e, None),
                    _ => (ERROR, None),
                };
                for (i, &sub) in prefix.iter().enumerate() {
                    let idx = self.const_usize(i as u64, span);
                    self.bind_pat(sub, place.project(Proj::Index(idx)));
                }
                for (j, &sub) in suffix.iter().enumerate() {
                    let back = (suffix.len() - j) as u64;
                    let idx = self.slice_back_index(&place, back, arr_len, span);
                    self.bind_pat(sub, place.project(Proj::Index(idx)));
                }
                if let Some(mid) = middle {
                    match p.ast.pat(*mid) {
                        Pat::Rest | Pat::Wild => {}
                        Pat::Binding { .. } => {
                            let mid_ty = self.ck.pat_ty(*mid);
                            if let (Some(n), TyKind::Array(..)) = (arr_len, self.kind(mid_ty)) {
                                // An owned middle of an array is a smaller array
                                // built from the element places.
                                let mut ops = Vec::new();
                                for i in prefix.len() as u64..(n - suffix.len() as u64) {
                                    let idx = self.const_usize(i, span);
                                    ops.push(self.operand_from(place.project(Proj::Index(idx)), elem));
                                }
                                let t = self.temp(mid_ty);
                                self.assign(Place::local(t), Rvalue::ArrayAgg(mid_ty, ops), span);
                                self.bind_pat(*mid, Place::local(t));
                            } else {
                                // A reference middle is a subslice fat value.
                                let lo = self.const_usize(prefix.len() as u64, span);
                                let hi = match arr_len {
                                    Some(n) => Operand::Const(Const::Int((n - suffix.len() as u64) as u128, IntTy::Usize)),
                                    None => {
                                        let len = self.temp(USIZE);
                                        self.assign(Place::local(len), Rvalue::LenOf(place.clone()), span);
                                        let t = self.temp(USIZE);
                                        self.assign(
                                            Place::local(t),
                                            Rvalue::Bin(
                                                BinOp::Sub,
                                                Operand::Copy(Place::local(len)),
                                                Operand::Const(Const::Int(suffix.len() as u128, IntTy::Usize)),
                                            ),
                                            span,
                                        );
                                        Operand::Copy(Place::local(t))
                                    }
                                };
                                let mode = match self.ck.pat_res(*mid) {
                                    PatRes::Binding { mode, .. } => mode,
                                    _ => BindMode::Move,
                                };
                                let mutable = mode == BindMode::Ref(true);
                                let slice = self.body.tys.intern(TyKind::Slice(elem));
                                let t = self.temp(slice);
                                self.assign(
                                    Place::local(t),
                                    Rvalue::Subslice {
                                        base: place,
                                        lo: Operand::Copy(Place::local(lo)),
                                        hi: Some(hi),
                                        inclusive: false,
                                        mutable,
                                    },
                                    span,
                                );
                                self.bind_pat(*mid, Place::local(t));
                            }
                        }
                        _ => {}
                    }
                }
            }
            (Pat::Ref { inner, .. }, _) => self.bind_pat(*inner, place.deref()),
            (Pat::At { inner, .. }, PatRes::Binding { local, mode }) => {
                // Subpattern bindings first: copying Copy fields out leaves the
                // whole value movable for the `@` binding, as in Rust. A
                // moving subpattern then makes the whole move an error.
                self.bind_pat(*inner, place.clone());
                let info = &self.ck.locals[local as usize];
                let (ty, m, name) = (info.ty, info.mutable, p.name(info.name).to_string());
                let l = self.new_local(ty, m, Some(name));
                self.local_map[local as usize] = l;
                let rv = match mode {
                    BindMode::Move => Rvalue::Use(self.operand_from(place.clone(), self.ck.pat_ty(pat))),
                    BindMode::Ref(m) => Rvalue::Ref(m, place.clone()),
                };
                self.assign(Place::local(l), rv, span);
                self.scopes.last_mut().unwrap().push(l);
            }
            _ => {}
        }
    }

    // ---------- Macros ----------

    fn fmt_parts(&mut self, args: &[ExprId], fmt: &[FmtPiece]) -> Vec<FmtPart> {
        let mut parts = Vec::with_capacity(fmt.len());
        for piece in fmt {
            match piece {
                FmtPiece::Lit(s) => parts.push(FmtPart::Lit(s.clone())),
                FmtPiece::Arg { index, debug, spec } => {
                    let (value, ty) = self.borrow_of(args[*index], 0);
                    parts.push(FmtPart::Arg { value, ty, debug: *debug, spec: *spec });
                }
            }
        }
        parts
    }

    #[allow(clippy::too_many_arguments)]
    fn macro_into(
        &mut self,
        e: ExprId,
        kind: MacroKind,
        args: &[ExprId],
        fmt: &[FmtPiece],
        repeat: bool,
        dest: Option<&Place>,
        ty: Ty,
        span: Span,
    ) {
        match kind {
            MacroKind::Println | MacroKind::Print | MacroKind::Eprintln | MacroKind::Eprint => {
                let parts = self.fmt_parts(args, fmt);
                let stderr = matches!(kind, MacroKind::Eprintln | MacroKind::Eprint);
                let newline = matches!(kind, MacroKind::Println | MacroKind::Eprintln);
                self.push(StmtKind::Print { stderr, newline, parts }, span);
                self.unit(dest, span);
            }
            MacroKind::Format => {
                let parts = self.fmt_parts(args, fmt);
                self.set_or_temp(dest, Rvalue::Format(parts), STRING, span);
            }
            MacroKind::Panic => {
                let mut parts = self.fmt_parts(args, fmt);
                if parts.is_empty() {
                    parts.push(FmtPart::Lit("explicit panic".into()));
                }
                self.terminate(Terminator::Panic(parts), span);
            }
            MacroKind::Todo => self.terminate(Terminator::Panic(vec![FmtPart::Lit("not yet implemented".into())]), span),
            MacroKind::Unreachable => {
                self.terminate(Terminator::Panic(vec![FmtPart::Lit("internal error: entered unreachable code".into())]), span)
            }
            MacroKind::Vec => {
                let elem = self.peel_vec(ty);
                let rv = if repeat {
                    let x = self.operand(args[0]);
                    let n = self.operand(args[1]);
                    Rvalue::VecRepeat(elem, x, n)
                } else {
                    let ops = args.iter().map(|&a| self.operand(a)).collect();
                    Rvalue::VecLit(elem, ops)
                };
                self.set_or_temp(dest, rv, ty, span);
            }
            MacroKind::Assert => {
                let c = self.operand(args[0]);
                let (ok, fail) = (self.new_block(), self.new_block());
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::If(c, ok, fail);
                b.term_span = span;
                self.cur = fail;
                let mut parts = self.fmt_parts(args, fmt);
                if parts.is_empty() {
                    parts.push(FmtPart::Lit("assertion failed".into()));
                }
                self.terminate(Terminator::Panic(parts), span);
                self.cur = ok;
                self.unit(dest, span);
            }
            MacroKind::AssertEq | MacroKind::AssertNe => {
                let ne = kind == MacroKind::AssertNe;
                let (a, t) = self.borrow_of(args[0], 0);
                let (b, tb) = self.borrow_of(args[1], 0);
                let c = self.temp(BOOL);
                let cmp = match self.ck.res(e) {
                    Res::Bin { ld, rd } => {
                        let (x, y) = (self.str_view(args[0], ld), self.str_view(args[1], rd));
                        Rvalue::StrCmp(if ne { BinOp::Ne } else { BinOp::Eq }, x, y)
                    }
                    _ => Rvalue::Eq { a: a.clone(), b: b.clone(), ty: t, ne },
                };
                self.assign(Place::local(c), cmp, span);
                let (ok, fail) = (self.new_block(), self.new_block());
                let blk = &mut self.body.blocks[self.cur.0 as usize];
                blk.term = Terminator::If(Operand::Copy(Place::local(c)), ok, fail);
                blk.term_span = span;
                self.cur = fail;
                let opname = if ne { "!=" } else { "==" };
                let mut parts = vec![FmtPart::Lit(format!("assertion `left {opname} right` failed"))];
                let msg = self.fmt_parts(args, fmt);
                if !msg.is_empty() {
                    parts.push(FmtPart::Lit(": ".into()));
                    parts.extend(msg);
                }
                parts.push(FmtPart::Lit("\n  left: ".into()));
                let dbg = FmtSpec { kind: FmtKind::Debug, ..FmtSpec::default() };
                parts.push(FmtPart::Arg { value: a, ty: t, debug: true, spec: dbg });
                parts.push(FmtPart::Lit("\n right: ".into()));
                parts.push(FmtPart::Arg { value: b, ty: tb, debug: true, spec: dbg });
                self.terminate(Terminator::Panic(parts), span);
                self.cur = ok;
                self.unit(dest, span);
            }
        }
    }

    /// An operand for a const value, building aggregates in a temporary.
    fn const_operand(&mut self, v: &crate::ty::consteval::ConstValue, ty: Ty, span: Span) -> Operand {
        use crate::ty::consteval::ConstValue as CV;
        match v {
            CV::Int(i) => {
                let it = match self.kind(ty) {
                    TyKind::Int(it) => it,
                    _ => IntTy::I32,
                };
                Operand::Const(Const::Int(*i as u128, it))
            }
            CV::Float(bits, f) => Operand::Const(Const::Float(*bits, *f)),
            CV::Bool(b) => Operand::Const(Const::Bool(*b)),
            CV::Char(c) => Operand::Const(Const::Char(*c)),
            CV::Str(i) => Operand::Const(Const::Str(*i)),
            CV::Unit => Operand::Const(Const::Unit),
            CV::StaticRef(idx) => {
                let t = self.temp(ty);
                self.assign(Place::local(t), Rvalue::StaticRef(*idx), span);
                Operand::Copy(Place::local(t))
            }
            _ => {
                let t = self.temp(ty);
                self.const_into(v, ty, &Place::local(t), span);
                self.operand_from(Place::local(t), ty)
            }
        }
    }

    /// Stores a const value into a place, building it from its parts.
    fn const_into(&mut self, v: &crate::ty::consteval::ConstValue, ty: Ty, dest: &Place, span: Span) {
        use crate::ty::consteval::ConstValue as CV;
        // An array const value at a slice reference type goes through a
        // temporary array and a SliceOf, like the coercion path.
        if let TyKind::Ref(_, _, inner) = self.kind(ty)
            && let TyKind::Slice(elem) = self.kind(inner)
            && matches!(v, CV::Aggregate(_) | CV::Repeat(..))
        {
            let n = match v {
                CV::Aggregate(vals) => vals.len() as u128,
                CV::Repeat(_, n) => *n as u128,
                _ => unreachable!(),
            };
            let c = self.body.tys.intern_const(ConstKind::Int(n));
            let at = self.body.tys.intern(TyKind::Array(elem, c));
            let t = self.temp(at);
            self.const_into(v, at, &Place::local(t), span);
            self.assign(dest.clone(), Rvalue::SliceOf(Place::local(t)), span);
            return;
        }
        match v {
            CV::Aggregate(vals) => match self.kind(ty) {
                TyKind::Tuple(ts) => {
                    let tys: Vec<Ty> = self.body.tys.tys_of(ts).to_vec();
                    let ops: Vec<Operand> =
                        vals.iter().enumerate().map(|(i, x)| self.const_operand(x, tys.get(i).copied().unwrap_or(ERROR), span)).collect();
                    self.assign(dest.clone(), Rvalue::TupleAgg(ty, ops), span);
                }
                TyKind::Array(elem, _) => {
                    let ops: Vec<Operand> = vals.iter().map(|x| self.const_operand(x, elem, span)).collect();
                    self.assign(dest.clone(), Rvalue::ArrayAgg(ty, ops), span);
                }
                _ => match self.body.tys.local_adt(ty) {
                    Some(a) => {
                        let ops: Vec<Operand> = vals
                            .iter()
                            .enumerate()
                            .map(|(i, x)| self.const_operand(x, self.p.adt(a).variants[0].fields[i].ty, span))
                            .collect();
                        self.assign(dest.clone(), Rvalue::Aggregate(a, 0, ops), span);
                    }
                    None => {
                        let op = self.const_operand(v, ty, span);
                        self.assign(dest.clone(), Rvalue::Use(op), span);
                    }
                },
            },
            CV::Variant(variant, vals) => {
                if let Some(elem) = self.body.tys.option_elem(ty) {
                    let op = if *variant == 1 && !vals.is_empty() { Some(self.const_operand(&vals[0], elem, span)) } else { None };
                    self.assign(dest.clone(), Rvalue::Opt(ty, op), span);
                } else if let Some((ok_t, err_t)) = self.body.tys.result_args(ty) {
                    if !vals.is_empty() {
                        let is_ok = *variant == 0;
                        let op = self.const_operand(&vals[0], if is_ok { ok_t } else { err_t }, span);
                        self.assign(dest.clone(), Rvalue::Res(ty, is_ok, op), span);
                    }
                } else if let Some(a) = self.body.tys.local_adt(ty) {
                    let ops: Vec<Operand> = vals
                        .iter()
                        .enumerate()
                        .map(|(i, x)| self.const_operand(x, self.p.adt(a).variants[*variant as usize].fields[i].ty, span))
                        .collect();
                    self.assign(dest.clone(), Rvalue::Aggregate(a, *variant, ops), span);
                }
            }
            CV::Repeat(x, n) => {
                let elem = match self.kind(ty) {
                    TyKind::Array(el, _) => el,
                    _ => ERROR,
                };
                if *n > 1 && is_copy(self.p, &self.body.tys, elem) && matches!(**x, CV::Int(_) | CV::Bool(_) | CV::Char(_)) {
                    let op = self.const_operand(x, elem, span);
                    self.assign(dest.clone(), Rvalue::ArrayRepeat(ty, op, *n), span);
                } else {
                    let ops: Vec<Operand> = (0..*n).map(|_| self.const_operand(x, elem, span)).collect();
                    self.assign(dest.clone(), Rvalue::ArrayAgg(ty, ops), span);
                }
            }
            CV::Ref(inner) => {
                let inner_ty = match self.kind(ty) {
                    TyKind::Ref(_, _, it) => it,
                    _ => ERROR,
                };
                let t = self.temp(inner_ty);
                self.const_into(inner, inner_ty, &Place::local(t), span);
                let mutable = matches!(self.kind(ty), TyKind::Ref(_, Mut::Mut, _));
                self.assign(dest.clone(), Rvalue::Ref(mutable, Place::local(t)), span);
            }
            CV::StaticRef(idx) => self.assign(dest.clone(), Rvalue::StaticRef(*idx), span),
            _ => {
                let op = self.const_operand(v, ty, span);
                self.assign(dest.clone(), Rvalue::Use(op), span);
            }
        }
    }

    fn set_or_temp(&mut self, dest: Option<&Place>, rv: Rvalue, ty: Ty, span: Span) {
        match dest {
            Some(d) => self.assign(d.clone(), rv, span),
            None => {
                let t = self.temp(ty);
                self.assign(Place::local(t), rv, span);
            }
        }
    }
}
