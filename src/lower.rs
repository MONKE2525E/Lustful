// Lowering: checked AST to IR. Makes evaluation order, temporaries, moves, borrows, and drops explicit.
use crate::ast::{self, BinOp, Expr, ExprId, FmtKind, FmtPiece, FmtSpec, MacroKind, Pat, PatId, Stmt};
use crate::check::collect::*;
use crate::check::{Autoref, BindMode, Builtin, Checked, CmpVia, Coerce, OrdPickKind, OrderingOpKind, PatRes, PrimCmpKind, PrimOpKind, Res};
use crate::diag::Span;
use crate::ir::*;
use crate::ty::*;

mod any;
mod closure;
pub mod iter;

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
    /// For each or-pattern with bindings that `test_pat` has
    /// tested, the local holding the index of the alternative
    /// that matched: `bind_pat` switches on it because bindings
    /// move only after the whole pattern (and any guard) pass.
    or_tags: Vec<(PatId, Local)>,
    /// While one expanded guard row lowers (see `match_into`),
    /// the alternative each or-pattern is fixed to for the row.
    or_forced: Vec<(PatId, usize)>,
    /// The guard temporary already made for a checker local, so
    /// every alternative (and guard row) that binds it writes
    /// the one temporary a guard later reads.
    guard_temps: Vec<(u32, Local)>,
    /// The IR local a pattern binding was created as, by
    /// checker local: all or-pattern alternatives of one name
    /// share a checker local and must assign the same IR local.
    bind_reuse: Vec<(u32, Local)>,
    /// Depth of `bind_pat` recursion, for tag cleanup at the
    /// outermost call (see `bind_pat`).
    bind_depth: u32,
    /// Binary-chain spine nodes already lowered into a temporary by
    /// `prelower_binary_spine`, with the generation of the spine run
    /// that made them (see `expr_into_raw`). An entry is taken out
    /// when the node's value is consumed, exactly once.
    prelowered: Vec<(ExprId, Place, u32)>,
    /// The current binary-spine run number; each run cleans up its
    /// own unconsumed `prelowered` entries.
    spine_gen: u32,
    /// Temporary lifetime extension (rustc `record_rvalue_scope`):
    /// while a `let` initializer lowers, the expressions whose
    /// temporaries live to the end of the enclosing block, with the
    /// index of that block's scope (see `let_stmt`, `materialize`).
    extended: Vec<(ExprId, usize)>,
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
    let body = Body {
        fn_id: fid,
        tys,
        locals: Vec::new(),
        blocks: vec![entry],
        arg_count: f.params.len(),
        reads,
        lower_errs: Vec::new(),
        annotations: Vec::new(),
        promoted: Vec::new(),
        index_exprs: Vec::new(),
        false_edges: Vec::new(),
        opaque_locals: Vec::new(),
    };
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
        or_tags: Vec::new(),
        or_forced: Vec::new(),
        guard_temps: Vec::new(),
        bind_reuse: Vec::new(),
        bind_depth: 0,
        prelowered: Vec::new(),
        spine_gen: 0,
        extended: Vec::new(),
    };
    // A template's own `impl Trait` return is its hidden type here, so the
    // borrow checker sees the returned value's regions (check/opaque.rs).
    let ret = match p.tys.kind(f.ret) {
        TyKind::Opaque(od, _) => lw.ck.opaque_hidden.iter().find(|(d, _)| *d == od).map_or(f.ret, |&(_, h)| h),
        _ => f.ret,
    };
    lw.new_local(ret, true, None);
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
    // Pattern parameters bind out of their argument locals
    // before the body: the bindings drop first, then the parts
    // of the arguments they did not move drop with the locals
    // above, as in a destructuring `let`.
    {
        let skip = usize::from(f.def.self_param.is_some());
        let param_pats: Vec<(ast::PatId, Local)> = f
            .def
            .params
            .iter()
            .zip(lw.ck.param_locals.iter().skip(skip))
            .filter_map(|(param, &cl)| param.pat.map(|pat| (pat, lw.local_map[cl as usize])))
            .collect();
        for (pat, arg) in param_pats {
            lw.bind_pat(pat, Place::local(arg));
        }
    }
    // A declaration shape (a trait method with no body) lowers to an
    // empty return so this can never panic; cgen refuses to generate
    // it or any call to it (`cgen::has_generated_body`).
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
    lw.map_annotations();
    lw.mark_opaque_locals();
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
    /// Evaluates `e` (through its coercion unless `raw`) into a new
    /// temporary of type `ty`. As rustc's `as_temp` schedules a
    /// temporary's drop after evaluating its expression, the temporary
    /// joins its scope only then, so it drops before the temporaries
    /// of its own expression (`wrap(&mk()).0`: the wrapper, then the
    /// argument). Its scope is the innermost one, or the enclosing
    /// block's when a `let` extends it (`extended`).
    fn materialize(&mut self, e: ExprId, ty: Ty, raw: bool) -> Local {
        let t = self.new_local(ty, true, None);
        if raw {
            self.expr_into_raw(e, Some(&Place::local(t)));
        } else {
            self.expr_into(e, Some(&Place::local(t)));
        }
        let depth = self.extended.iter().rev().find(|&&(x, _)| x == e).map_or(self.scopes.len() - 1, |&(_, d)| d);
        self.scopes[depth].push(t);
        t
    }
    /// Whether a value of type `ty` needs a drop (cached per body type).
    fn needs_drop_ty(&mut self, ty: Ty) -> bool {
        if let Some(&d) = self.drop_ty.get(&ty) {
            return d;
        }
        let d = needs_drop(self.p, &self.body.tys, ty);
        self.drop_ty.insert(ty, d);
        d
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
    /// The checker's regioned `let` annotations (W-BORROW) on the IR
    /// locals their bindings lowered to.
    fn map_annotations(&mut self) {
        for &(cl, t) in &self.ck.annotations {
            if let Some(&l) = self.local_map.get(cl as usize)
                && l != u32::MAX
            {
                self.body.annotations.push((l, t));
            }
        }
    }

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
    /// Fills `Body::opaque_locals` (see `holds_revealed`).
    fn mark_opaque_locals(&mut self) {
        if self.ck.revealed.is_empty() {
            return;
        }
        let marked: Vec<Local> = (0..self.body.locals.len() as Local).filter(|&l| self.holds_revealed(self.body.locals[l as usize].ty)).collect();
        self.body.opaque_locals = marked;
    }
    /// True when a value of type `ty` may hold an `impl Trait` value the
    /// check revealed (`Checked::revealed`): its drop is a use of every
    /// region it holds (`Body::opaque_locals`). A plain value of the same
    /// type counts too, which can only make the borrow check stricter.
    fn holds_revealed(&self, ty: Ty) -> bool {
        !self.ck.revealed.is_empty() && self.ck.revealed.iter().any(|&r| crate::check::opaque::ty_contains(&self.body.tys, ty, r))
    }
    fn emit_drops(&mut self, locals: &[Local], span: Span) {
        for &l in locals.iter().rev() {
            let ty = self.body.locals[l as usize].ty;
            if self.needs_drop_ty(ty) || self.holds_revealed(ty) {
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
            Expr::Path(_) | Expr::SelfValue => matches!(self.ck.res(e), Res::Local(_) | Res::Static(_)),
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
        if let Some(pl) = self.take_prelowered(e) {
            return pl;
        }
        match (self.p.ast.expr(e), self.ck.res(e)) {
            (Expr::Path(_) | Expr::SelfValue, Res::Local(l)) => match &self.guard_places[l as usize] {
                // A match guard reads its arm's bindings through a
                // shared reference (see `bind_pat_guard`).
                Some(p) => p.clone(),
                None => Place::local(self.local_map[l as usize]),
            },
            (Expr::Field { base, .. }, Res::Field { derefs, index }) => {
                // Through a user `Deref` impl, the field is on the target.
                let span = self.span(e);
                let b = match self.deref_steps(e, *base, span) {
                    Some(root) => root,
                    None => self.place(*base),
                };
                Self::derefs(b, derefs).project(Proj::Field(index))
            }
            (Expr::TupleField { base, .. }, Res::Field { derefs, index }) => {
                let b = self.place(*base);
                Self::derefs(b, derefs).project(Proj::Field(index))
            }
            (Expr::Index { base, index }, Res::SliceIndex { derefs }) => {
                let span = self.span(e);
                let b = match self.deref_steps(e, *base, span) {
                    Some(root) => root,
                    None => self.place(*base),
                };
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
                let span = self.span(e);
                let (b, root_ty) = match self.deref_steps(e, *base, span) {
                    Some(root) => {
                        let t = self.body.locals[root.local as usize].ty;
                        (root, t)
                    }
                    None => (self.place(*base), self.ty(*base)),
                };
                let b = Self::derefs(b, derefs);
                // Mutable use: borrow the container before the index expression runs
                // (see `place_for_mut`), and index through that borrow.
                let b = if self.mut_index > 0 {
                    let bt = self.peel(root_ty, derefs);
                    let rt = self.ref_ty(true, bt);
                    let t = self.temp(rt);
                    let span = self.span(e);
                    self.assign(Place::local(t), Rvalue::Ref(true, b), span);
                    Place::local(t).deref()
                } else {
                    b
                };
                let i = self.temp(USIZE);
                self.body.index_exprs.push(i);
                // The index is a value, not part of the mutable place.
                let saved = std::mem::take(&mut self.mut_index);
                self.expr_into(*index, Some(&Place::local(i)));
                self.mut_index = saved;
                b.project(Proj::Index(i))
            }
            (Expr::Deref(inner), _) => {
                let span = self.span(e);
                match self.deref_steps(e, *inner, span) {
                    Some(root) => root.deref(),
                    None => self.place(*inner).deref(),
                }
            }
            // A static is a place of its own (W-BORROW): reach it through
            // its address, as `&STATIC` does, never through a copy in a
            // temporary. A borrow of it is then `'static`, and a move out
            // of it is a move out of a reference (rustc E0507).
            (Expr::Path(_), Res::Static(idx)) => {
                let rt = self.ref_ty(false, self.ty(e));
                let t = self.temp(rt);
                let span = self.span(e);
                self.assign(Place::local(t), Rvalue::StaticRef(idx), span);
                Place::local(t).deref()
            }
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
                let t = self.materialize(e, self.ty(e), false);
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
            // Through user `Deref` impls: the coerced reference's place,
            // then each impl's `deref` (or `deref_mut`).
            Coerce::UserDeref(target) => {
                let steps: Vec<crate::check::DerefRecv> = self.ck.deref_coerce(e).into_iter().cloned().collect();
                let place = self.op_place(op, ty, span);
                let root = self.apply_deref_steps(place, ty, steps, span);
                if matches!(self.kind(target), TyKind::Ref(_, m, _) if m.is_mut()) { Operand::Move(root) } else { Operand::Copy(root) }
            }
        }
    }

    /// The type of `e` after its recorded coercion, for temporaries
    /// that hold the coerced operand: the type `operand` produces (a
    /// struct field `&[]` into `&[u8]` is a slice, not `&[u8; 0]`).
    fn coerced_ty(&mut self, e: ExprId) -> Ty {
        let ty = self.ty(e);
        match self.ck.coerce(e) {
            Coerce::None => ty,
            Coerce::StrFromString => REF_STR,
            Coerce::Unsize(t) | Coerce::UserDeref(t) => t,
            Coerce::Deref(n) => self.peel(ty, n),
            Coerce::BoxToRef(n, m) => {
                let elem = self.peel(ty, n);
                self.ref_ty(m, elem)
            }
            Coerce::MutToShared | Coerce::Reborrow => {
                let m = self.ck.coerce(e) == Coerce::Reborrow;
                let inner = self.peel(ty, 1);
                self.ref_ty(m, inner)
            }
            Coerce::SliceFromArray(m) | Coerce::SliceFromVec(m) => {
                let mut inner = self.peel(ty, 1);
                if let Some(b) = self.body.tys.smart_elem(inner) {
                    inner = b;
                }
                let elem = match self.kind(inner) {
                    TyKind::Array(el, _) => el,
                    _ => self.body.tys.vec_elem(inner).unwrap_or(ERROR),
                };
                let slice = self.body.tys.intern(TyKind::Slice(elem));
                self.ref_ty(m, slice)
            }
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
        // An owning unsizing (`Box<T>` to `Box<dyn Tr>`, `Rc<T>` to
        // `Rc<dyn Tr>`): the box or Rc moves into the fat pointer.
        if let (Some(src), Some(dyn_ty)) = (self.body.tys.smart_elem(found), self.body.tys.smart_elem(target)) {
            let rv = match (object::principal_of(&self.body.tys, src), object::principal_of(&self.body.tys, dyn_ty)) {
                (Some(from), Some(to)) => {
                    let path = object::upcast_path(self.p, &mut self.body.tys, from, to).unwrap_or_default();
                    if path.is_empty() { Rvalue::Use(op) } else { Rvalue::DynUpcast { ptr: op, path } }
                }
                _ => Rvalue::MakeDyn { ptr: op, src, dyn_ty },
            };
            let out = self.temp(target);
            self.assign(Place::local(out), rv, span);
            return Operand::Move(Place::local(out));
        }
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

    /// The user `Deref` steps check recorded for `e` (a method call's
    /// receiver, a field access base, or an explicit `*x`), applied to
    /// the place of `input`. None when `e` has no step.
    fn deref_steps(&mut self, e: ExprId, input: ExprId, span: Span) -> Option<Place> {
        let steps: Vec<crate::check::DerefRecv> = self.ck.deref_recv(e).into_iter().cloned().collect();
        let first = steps.first()?;
        let mutable = first.mutable || (first.f_mut.is_some() && self.mut_index > 0);
        let pl = if mutable { self.place_for_mut(input) } else { self.place(input) };
        let ty = self.ty(input);
        Some(self.apply_deref_steps(pl, ty, steps, span))
    }

    /// Applies user `Deref` steps outermost first to `start` (of type
    /// `start_ty`): borrow the step's input, call the impl's `deref`
    /// (or `deref_mut`: a step check fixed as mutable, or a place step
    /// under `place_for_mut`), and go on from the `&Target` it returns.
    /// Returns that last reference's place.
    fn apply_deref_steps(&mut self, start: Place, start_ty: Ty, steps: Vec<crate::check::DerefRecv>, span: Span) -> Place {
        let (mut root, mut root_ty) = (start, start_ty);
        for dr in steps {
            let place_mut = dr.f_mut.is_some() && self.mut_index > 0;
            let mutable = dr.mutable || place_mut;
            let base = Self::derefs(root, dr.before);
            let base_ty = self.peel(root_ty, dr.before);
            let rt = self.ref_ty(mutable, base_ty);
            let r = self.temp(rt);
            self.assign(Place::local(r), Rvalue::Ref(mutable, base), span);
            let (f, args) = match dr.f_mut {
                Some(g) if place_mut => (g, dr.args_mut.clone()),
                _ => (dr.f, dr.args.clone()),
            };
            let f = if args.is_empty() { f } else { crate::check::generics::instance_for(self.p, &self.body.tys, f, &args).unwrap_or(f) };
            let target = self.peel(dr.target_ref, 1);
            let tt = self.ref_ty(mutable, target);
            let t = self.temp(tt);
            let arg = if mutable { Operand::Move(Place::local(r)) } else { Operand::Copy(Place::local(r)) };
            self.call_into(CallTarget::Fn(f), vec![arg], Place::local(t), span);
            (root, root_ty) = (Place::local(t), tt);
        }
        root
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
        if let Some(pl) = self.take_prelowered(e) {
            return Operand::Move(pl);
        }
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
                let t = self.materialize(e, ty, true);
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

    /// Takes out the temporary `prelower_binary_spine` made for `e`,
    /// if it made one and the value has not been consumed yet.
    fn take_prelowered(&mut self, e: ExprId) -> Option<Place> {
        let i = self.prelowered.iter().rposition(|&(x, _, _)| x == e)?;
        Some(self.prelowered.swap_remove(i).1)
    }

    /// Lowers every node below `top` on the left spine of a binary
    /// chain (`a + b + c + ...`) into its own temporary, deepest
    /// first, and records them in `prelowered`. Evaluating the spine
    /// this way emits the same statements in the same order as the
    /// recursive walk (the left operand of every node is ready before
    /// its right operand runs), but the walk itself is a loop, so a
    /// 2000-term chain uses constant stack here. A node the checker
    /// const-evaluated stops the spine: it materializes directly in
    /// `expr_into_here` and nothing below it must run.
    /// Returns the run's generation for cleanup of leftovers.
    fn prelower_binary_spine(&mut self, top: ExprId) -> u32 {
        self.spine_gen += 1;
        let run = self.spine_gen;
        let mut spine: Vec<ExprId> = Vec::new();
        let mut cur = top;
        while let Expr::Binary { lhs, .. } = self.p.ast.expr(cur) {
            if self.ck.const_value(cur).is_some() {
                break;
            }
            spine.push(cur);
            cur = *lhs;
        }
        for i in (1..spine.len()).rev() {
            let node = spine[i];
            let pl = Place::local(self.temp(self.ty(node)));
            // The left side of `&&` or `||` is a terminating scope, as in
            // rustc (and `binary_into`): its temporaries drop right after it.
            let term = matches!(self.p.ast.expr(spine[i - 1]), Expr::Binary { op: BinOp::And | BinOp::Or, .. });
            if term {
                self.scopes.push(Vec::new());
            }
            self.expr_into_here(node, Some(&pl));
            if term {
                let span = self.span(node);
                self.pop_scope(span);
            }
            self.prelowered.push((node, pl, run));
        }
        run
    }

    fn expr_into_raw(&mut self, e: ExprId, dest: Option<&Place>) {
        if let Some(pl) = self.take_prelowered(e) {
            if let Some(d) = dest {
                let d = d.clone();
                let span = self.span(e);
                self.assign(d, Rvalue::Use(Operand::Move(pl)), span);
            }
            return;
        }
        if matches!(self.p.ast.expr(e), Expr::Binary { .. }) && self.ck.const_value(e).is_none() {
            let run = self.prelower_binary_spine(e);
            self.expr_into_here(e, dest);
            // Not every spine value is always consumed (a node below
            // a const-evaluated one, an error path): drop this run's
            // leftovers so a later use of the same expression (a
            // match guard row lowers its guard once per row) always
            // evaluates it fresh.
            self.prelowered.retain(|&(_, _, g)| g != run);
            return;
        }
        self.expr_into_here(e, dest)
    }

    fn expr_into_here(&mut self, e: ExprId, dest: Option<&Place>) {
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
                        self.aggregate_into(e, Rvalue::Aggregate(a, v, Vec::new()), dest, ty, span)
                    }
                }
                Res::Fn(f) => {
                    // A fn item used as a value: zero-sized at its FnDef
                    // type, the slot trampoline where a fn pointer goes.
                    // A generic fn names its mono instance.
                    let f = self.resolve_generic_fn(e, f);
                    let want = match dest {
                        Some(d) if d.proj.is_empty() => {
                            let dt = self.body.locals[d.local as usize].ty;
                            if matches!(self.kind(dt), TyKind::FnPtr(_)) { dt } else { ty }
                        }
                        _ => ty,
                    };
                    self.set_or_temp(dest, Rvalue::FnValue(f, want), ty, span)
                }
                // A static's value of a non-Copy type moves out of a
                // place reached through its address (`place`), which the
                // borrow checker rejects as a move out of a reference
                // (rustc E0507); a copy loads it.
                Res::Static(_) if !is_copy(self.p, &self.body.tys, ty) => {
                    let pl = self.place(e);
                    let op = self.operand_from(pl, ty);
                    match dest {
                        Some(d) => self.assign(d.clone(), Rvalue::Use(op), span),
                        None => {
                            let t = self.temp(ty);
                            self.assign(Place::local(t), Rvalue::Use(op), span);
                        }
                    }
                }
                Res::Static(idx) => self.set_or_temp(dest, Rvalue::StaticLoad(idx), ty, span),
                Res::OptNone => self.set_or_temp(dest, Rvalue::Opt(ty, None), ty, span),
                // `Some`, `Ok`, `Err`, `Box::new`, `Rc::new`, or
                // `String::from` used as a value (W-CHECK-G): a
                // zero-sized item, as for a user constructor above.
                Res::OptSome | Res::ResOk | Res::ResErr | Res::Builtin(_) if matches!(self.kind(ty), TyKind::FnDef(..)) => {
                    self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Unit)), ty, span)
                }
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
                    let reborrow = self.reborrows_arms(ty) && !self.block_diverges(*then);
                    self.arm_into(*els, reborrow, dest);
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
                    let reborrow = self.reborrows_arms(ty) && !self.block_diverges(*then);
                    self.arm_into(*els, reborrow, dest);
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
                // (template checks), or through a `dyn Fn` value's
                // vtable: a method call with the callee as its receiver.
                // (A qualified path call through a dyn receiver,
                // `Tr::m(d)`, passes its receiver as an argument.)
                let dyn_fn_call = matches!(res, Res::DynMethod { owner, .. } if self.p.gx.lang.is_fn_family(owner));
                if matches!(res, Res::Method { .. }) || dyn_fn_call {
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
                    Res::Builtin(Builtin::VecNew) => self.set_or_temp(dest, Rvalue::VecLit(self.peel_vec(ty), Vec::new()), ty, span),
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
                    Res::Builtin(Builtin::MemTake) => {
                        // Check limited `take` to types whose `Default`
                        // value is one of the forms below (or the
                        // default glue): fill a slot with it, then
                        // byte-replace.
                        let slot = self.temp(ty);
                        match self.kind(ty) {
                            TyKind::Int(it) => self.assign(Place::local(slot), Rvalue::Use(Operand::Const(Const::Int(0, it))), span),
                            TyKind::Float(f) => self.assign(Place::local(slot), Rvalue::Use(Operand::Const(Const::Float(0, f))), span),
                            TyKind::Bool => self.assign(Place::local(slot), Rvalue::Use(Operand::Const(Const::Bool(false))), span),
                            TyKind::Char => self.assign(Place::local(slot), Rvalue::Use(Operand::Const(Const::Char('\0'))), span),
                            TyKind::Unit => self.assign(Place::local(slot), Rvalue::Use(Operand::Const(Const::Unit)), span),
                            _ if self.body.tys.is_string_ty(ty) => {
                                self.call_into(CallTarget::Builtin(Builtin::StringNew), Vec::new(), Place::local(slot), span)
                            }
                            _ if self.body.tys.vec_elem(ty).is_some() => {
                                self.assign(Place::local(slot), Rvalue::VecLit(self.peel_vec(ty), Vec::new()), span)
                            }
                            _ if self.body.tys.option_elem(ty).is_some() => self.assign(Place::local(slot), Rvalue::Opt(ty, None), span),
                            // Every other type the checker allowed has
                            // its value in the default glue.
                            _ => self.call_into(CallTarget::Builtin(Builtin::DefaultGlue), Vec::new(), Place::local(slot), span),
                        }
                        let fill = self.operand_from(Place::local(slot), ty);
                        let mut ops = ops;
                        ops.push(fill);
                        let d = self.call_dest(dest, ty);
                        self.call_into(CallTarget::Builtin(Builtin::MemReplace), ops, d, span);
                    }
                    Res::Builtin(b) => {
                        let d = self.call_dest(dest, ty);
                        self.call_into(CallTarget::Builtin(b), ops, d, span);
                    }
                    Res::Variant(a, v) => self.aggregate_into(e, Rvalue::Aggregate(a, v, ops), dest, ty, span),
                    Res::ConstUsize(v) => {
                        self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Int(v as u128, IntTy::Usize))), ty, span)
                    }
                    Res::Any { .. } => self.type_id_of_into(e, dest, ty, span),
                    Res::ConstBool(b) => self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Bool(b))), ty, span),
                    Res::SizeOfVal { len, elem } => {
                        if elem == 1 {
                            let d = self.call_dest(dest, ty);
                            self.call_into(CallTarget::Builtin(len), ops, d, span);
                        } else {
                            let t = self.temp(ty);
                            self.call_into(CallTarget::Builtin(len), ops, Place::local(t), span);
                            self.set_or_temp(
                                dest,
                                Rvalue::Bin(
                                    BinOp::Mul,
                                    Operand::Copy(Place::local(t)),
                                    Operand::Const(Const::Int(elem as u128, IntTy::Usize)),
                                ),
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
                            TyKind::Unit => Const::Unit,
                            // Other types build their default value in
                            // the `default` glue, typed by the call's
                            // destination.
                            _ => {
                                let d = self.call_dest(dest, ty);
                                self.call_into(CallTarget::Builtin(Builtin::DefaultGlue), Vec::new(), d, span);
                                return;
                            }
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
                // `&[]` and `&mut []` are promoted to `'static`, as in rustc:
                // the empty array has no bytes, so a temporary that never
                // dies serves, and it makes no loan (`Body::promoted`).
                if let Expr::Array(elems) = p.ast.expr(*expr)
                    && elems.is_empty()
                {
                    let at = self.ty(*expr);
                    let t = self.new_local(at, true, None);
                    self.assign(Place::local(t), Rvalue::ArrayAgg(at, Vec::new()), span);
                    self.body.promoted.push(t);
                    if let Some(d) = dest {
                        self.assign(d.clone(), Rvalue::Ref(*mutable, Place::local(t)), span);
                    }
                    return;
                }
                // `&|n| n - 1`: a shared borrow of a closure that captures
                // nothing is promoted too (rustc promotes the constant
                // value; the env is empty).
                if !*mutable
                    && matches!(p.ast.expr(*expr), Expr::Closure { .. })
                    && self.ck.closures.iter().any(|c| c.expr == *expr && c.captures.is_empty())
                {
                    let ct = self.ty(*expr);
                    let t = self.new_local(ct, true, None);
                    self.closure_value(*expr, Some(&Place::local(t)), span);
                    self.body.promoted.push(t);
                    if let Some(d) = dest {
                        self.assign(d.clone(), Rvalue::Ref(false, Place::local(t)), span);
                    }
                    return;
                }
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
                self.aggregate_into(e, Rvalue::Aggregate(a, v, ops), dest, ty, span);
            }
            // A range value (check/iter.rs): the std struct's fields,
            // `start`, `end`, and `exhausted` for the inclusive form.
            Expr::Range { lo: Some(lo), hi: Some(hi), inclusive } => {
                let ty = self.ty(e);
                let mut ops = vec![self.operand(*lo), self.operand(*hi)];
                if *inclusive {
                    ops.push(Operand::Const(Const::Bool(false)));
                }
                self.set_or_temp(dest, Rvalue::TupleAgg(ty, ops), ty, span);
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
                        // A template's const param length: lower the element
                        // so the borrow checker sees it (templates get no code).
                        ConstKind::Param(_) => 2,
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
            // A qualified path fn value (`<S as Tr>::mk`), lowered as
            // the plain path's fn value; a qualified const lowered
            // above from its value.
            Expr::QPath { .. } => {
                if let Res::Fn(f) = self.ck.res(e) {
                    // A generic fn (an impl's or a trait default) names
                    // its mono instance, as on a plain path.
                    let f = self.resolve_generic_fn(e, f);
                    let want = match dest {
                        Some(d) if d.proj.is_empty() => {
                            let dt = self.body.locals[d.local as usize].ty;
                            if matches!(self.kind(dt), TyKind::FnPtr(_)) { dt } else { ty }
                        }
                        _ => ty,
                    };
                    self.set_or_temp(dest, Rvalue::FnValue(f, want), ty, span)
                }
            }
            Expr::Float(_)
            | Expr::Await(_)
            | Expr::AsyncBlock { .. }
            | Expr::UnsafeBlock(_)
            | Expr::Let { .. }
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
                    self.stmt_expr(*expr);
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

    /// An expression statement, as rustc's `stmt_expr`: the value goes
    /// into a statement temporary that drops at the end of the
    /// statement. A place moves (or copies) into it (`s;` drops `s`
    /// here), and a block, `if`, `match`, or `loop` value drops after
    /// the locals of the block that made it. Other values already go to
    /// a temporary of this scope where the expression needs one.
    fn stmt_expr(&mut self, e: ExprId) {
        let value = matches!(
            self.p.ast.expr(e),
            Expr::Block(_) | Expr::LabeledBlock { .. } | Expr::If { .. } | Expr::Match { .. } | Expr::Loop { .. }
        );
        let ty = self.ty(e);
        // A const value (`CD;`, an inline const) is no place and
        // builds no temporary on its own, but the copy it makes is a
        // statement temporary like any other and drops here.
        let const_temp = self.ck.const_value(e).is_some() && self.needs_drop_ty(ty);
        if self.ck.coerce(e) == Coerce::None && (self.is_place_expr(e) || value && self.needs_drop_ty(ty) || const_temp) {
            self.materialize(e, ty, false);
        } else {
            self.expr_into(e, None);
        }
    }

    /// An `if` or `match` arm. rustc's LUB coercion reborrows (`&*arm`)
    /// each reference-typed arm after the first one that does not
    /// diverge (`reborrow`): the reborrow reads the arm's value after the
    /// arm's block has dropped its locals and tail temporaries, so a
    /// borrow of those is an error even when the result is unused (`if c
    /// { .. } else { &temp() };`). Such an arm goes into a temporary
    /// first; a coerced arm is already read through its coercion.
    fn arm_into(&mut self, e: ExprId, reborrow: bool, dest: Option<&Place>) {
        if !reborrow || self.ck.coerce(e) != Coerce::None {
            self.expr_into(e, dest);
            return;
        }
        let (ty, span) = (self.ty(e), self.span(e));
        let t = self.materialize(e, ty, false);
        match dest {
            Some(d) => {
                let op = self.operand_from(Place::local(t), ty);
                self.assign(d.clone(), Rvalue::Use(op), span);
            }
            None => self.push(StmtKind::FakeRead(t), span),
        }
    }

    /// True when an `if` or `match` result of type `ty` is a reference,
    /// whose later arms rustc reborrows (`arm_into`).
    fn reborrows_arms(&self, ty: Ty) -> bool {
        matches!(self.kind(ty), TyKind::Ref(..))
    }

    fn diverges(&self, e: ExprId) -> bool {
        matches!(self.kind(self.ty(e)), TyKind::Never)
    }

    /// True when block `b` has type `!`: its tail diverges, or it has no
    /// tail where a value is expected.
    fn block_diverges(&self, b: ast::BlockId) -> bool {
        self.p.ast.block(b).tail.is_none_or(|t| self.diverges(t))
    }

    /// Marks the temporaries a `let` initializer extends to the end of
    /// the enclosing block (scope `depth`), as rustc's
    /// `record_rvalue_scope_if_borrow_expr`: the operand of each
    /// extending borrow, found through the initializer itself and the
    /// operands of extending struct, tuple, array, and cast expressions,
    /// the arguments of tuple struct and variant constructors, block
    /// tails, and the arms of `if` and `match`.
    fn mark_extending(&mut self, e: ExprId, depth: usize) {
        let p = self.p;
        match p.ast.expr(e) {
            Expr::Ref { expr, .. } => {
                self.mark_extending(*expr, depth);
                self.mark_extended(*expr, depth);
            }
            Expr::StructLit { fields, .. } => {
                for &(_, _, f) in fields {
                    self.mark_extending(f, depth);
                }
            }
            Expr::Tuple(es) | Expr::Array(es) => {
                for &x in es {
                    self.mark_extending(x, depth);
                }
            }
            Expr::Cast { expr, .. } => self.mark_extending(*expr, depth),
            Expr::Block(b) | Expr::UnsafeBlock(b) | Expr::LabeledBlock { body: b, .. } => {
                if let Some(t) = p.ast.block(*b).tail {
                    self.mark_extending(t, depth);
                }
            }
            Expr::If { then, els, .. } => {
                if let Some(t) = p.ast.block(*then).tail {
                    self.mark_extending(t, depth);
                }
                if let Some(x) = els {
                    self.mark_extending(*x, depth);
                }
            }
            Expr::Match { arms, .. } => {
                for arm in arms {
                    self.mark_extending(arm.body, depth);
                }
            }
            Expr::Call { callee, args } if self.is_ctor_callee(e, *callee) => {
                for &a in args {
                    self.mark_extending(a, depth);
                }
            }
            _ => {}
        }
    }

    /// rustc's `record_rvalue_scope`: `e`, and the expressions it
    /// borrows, derefs, or projects a field or an index from, get the
    /// extended temporary scope (`&temp().field` extends `temp()`).
    fn mark_extended(&mut self, mut e: ExprId, depth: usize) {
        loop {
            self.extended.push((e, depth));
            match self.p.ast.expr(e) {
                Expr::Ref { expr, .. } | Expr::Deref(expr) => e = *expr,
                Expr::Field { base, .. } | Expr::TupleField { base, .. } | Expr::Index { base, .. } => e = *base,
                _ => return,
            }
        }
    }

    /// True for the callee of a tuple struct or tuple variant
    /// constructor call written as a resolved path (`W(..)`, `Some(..)`,
    /// `m::E::V(..)`, `Self(..)`), whose arguments extend like a
    /// struct literal's fields. A type-relative path (`Self::V(..)`, a
    /// variant through a type alias) does not extend, as in rustc.
    fn is_ctor_callee(&self, call: ExprId, callee: ExprId) -> bool {
        let p = self.p;
        let Expr::Path(segs) = p.ast.expr(callee) else { return false };
        if !matches!(self.ck.res(call), Res::Variant(..) | Res::OptSome | Res::ResOk | Res::ResErr) {
            return false;
        }
        match segs.len() {
            0 | 1 => true,
            n => {
                let head = segs[n - 2].name;
                head != p.known.self_type && !p.aliases.contains_key(&head)
            }
        }
    }

    /// rustc's `is_binding_pat`: a pattern with an explicit `ref` or
    /// `ref mut` binding (not one match ergonomics makes) extends its
    /// whole initializer to the end of the block.
    fn is_binding_pat(&self, pat: PatId) -> bool {
        match self.p.ast.pat(pat) {
            Pat::Binding { by_ref, .. } | Pat::At { by_ref, .. } => *by_ref,
            Pat::Struct { fields, .. } => fields.iter().any(|&(_, s)| self.is_binding_pat(s)),
            Pat::TupleStruct { elems, .. } | Pat::Tuple(elems) | Pat::Or(elems) => elems.iter().any(|&s| self.is_binding_pat(s)),
            Pat::Slice { prefix, middle, suffix } => {
                middle.is_some_and(|m| self.is_binding_pat(m)) || prefix.iter().chain(suffix.iter()).any(|&s| self.is_binding_pat(s))
            }
            Pat::Paren(i) => self.is_binding_pat(*i),
            _ => false,
        }
    }

    /// `let PAT = init;`, as rustc builds it: the initializer's
    /// temporaries drop at the end of the statement, except those a
    /// borrow extends to the end of the block (`mark_extending`). A
    /// plain binding takes the value directly and is used once it is
    /// set (rustc's `FakeRead(ForLet)`), so a borrow of something the
    /// initializer already dropped is an error. Any other pattern binds
    /// out of the initializer's place (see `pattern_init`).
    fn let_stmt(&mut self, pat: PatId, init: Option<ExprId>, span: Span) {
        let p = self.p;
        let Some(init) = init else {
            if let (Pat::Binding { .. }, PatRes::Binding { local, .. }) = (p.ast.pat(pat), self.ck.pat_res(pat)) {
                let l = self.binding_local(local);
                self.scopes.last_mut().unwrap().push(l);
            }
            return;
        };
        let block = self.scopes.len() - 1;
        let mark = self.extended.len();
        self.mark_extending(init, block);
        self.scopes.push(Vec::new());
        match (p.ast.pat(pat), self.ck.pat_res(pat)) {
            (Pat::Binding { by_ref: false, .. }, PatRes::Binding { local, mode: BindMode::Move }) => {
                let l = self.binding_local(local);
                self.expr_into(init, Some(&Place::local(l)));
                self.push(StmtKind::FakeRead(l), span);
                self.scopes[block].push(l);
            }
            (Pat::Wild, _) => {
                // `let _ = init;` binds nothing. A place initializer is
                // only mentioned (rustc `PlaceMention`): not read or
                // moved, but its root is live here; an index in it still
                // runs, through a shared borrow. A value goes into a
                // statement temporary that is mentioned the same way.
                if self.ck.coerce(init) == Coerce::None && self.is_place_expr(init) {
                    let pl = self.place(init);
                    if pl.proj.iter().any(|x| matches!(x, Proj::Index(_))) {
                        let rt = self.ref_ty(false, self.ty(init));
                        let t = self.temp(rt);
                        self.assign(Place::local(t), Rvalue::Ref(false, pl), span);
                    } else {
                        self.push(StmtKind::FakeRead(pl.local), span);
                    }
                } else if let Operand::Copy(pl) | Operand::Move(pl) = self.operand(init) {
                    self.push(StmtKind::FakeRead(pl.local), span);
                }
            }
            _ => {
                let src = self.pattern_init(pat, init, block, span);
                let stmt = self.scopes.pop().unwrap();
                self.bind_pat(pat, src);
                self.scopes.push(stmt);
            }
        }
        self.pop_scope(span);
        self.extended.truncate(mark);
    }

    /// The IR local for a `let` binding's checker local.
    fn binding_local(&mut self, local: u32) -> Local {
        let info = &self.ck.locals[local as usize];
        let (ty, m, name) = (info.ty, info.mutable, self.p.name(info.name).to_string());
        let l = self.new_local(ty, m, Some(name));
        self.local_map[local as usize] = l;
        l
    }

    /// The place a destructuring `let` (or `let`-`else`) binds out of,
    /// evaluated in the statement scope (the innermost one): a place
    /// initializer itself, as in rustc (a binding that moves a part is
    /// a partial move of it; the rest stays and drops with its owner,
    /// `cgen::FnGen::elab_drop`); any other value moves into a
    /// temporary whose leftover parts drop at the end of the statement,
    /// or at the end of the block (scope `block`) when the pattern has
    /// an explicit `ref` binding, which extends the whole initializer.
    fn pattern_init(&mut self, pat: PatId, init: ExprId, block: usize, span: Span) -> Place {
        if self.is_binding_pat(pat) {
            self.mark_extended(init, block);
        }
        if self.ck.coerce(init) == Coerce::None && self.is_place_expr(init) {
            let pl = self.place(init);
            return self.pattern_place(pl, self.ty(init), &[pat], span);
        }
        let ty = self.coerced_ty(init);
        let t = self.materialize(init, ty, false);
        Place::local(t)
    }

    /// `let PAT = init else { ... };`: test the pattern against the
    /// initializer's place (`pattern_init`), bind on success, and run
    /// the diverging else block on failure. The statement's
    /// temporaries drop at its end on success and before the else
    /// block on failure, as in rustc.
    fn let_else_stmt(&mut self, pat: PatId, init: Option<ExprId>, els: ast::BlockId, span: Span) {
        let Some(init) = init else { return };
        let block = self.scopes.len() - 1;
        let mark = self.extended.len();
        self.mark_extending(init, block);
        self.scopes.push(Vec::new());
        let sp = self.pattern_init(pat, init, block, span);
        let fail = self.new_block();
        self.test_pat(pat, sp.clone(), fail);
        let stmt = self.scopes.pop().unwrap();
        self.bind_pat(pat, sp);
        self.emit_drops(&stmt, span);
        self.extended.truncate(mark);
        let cont = self.cur;
        self.cur = fail;
        self.emit_drops(&stmt, span);
        self.block_into(els, None);
        self.terminate(Terminator::Unreachable, span);
        self.cur = cont;
    }

    // ---------- Calls ----------

    /// A comparison trait method (`Res::PrimCmp`): the receiver is
    /// borrowed `&self` (so borrowck sees the loan a method call
    /// would make), and the result is the comparison, an
    /// `Ordering` value, or an `Option<Ordering>` (`None` only when
    /// the comparison is unordered). Scalars compare directly,
    /// `str` through the string comparison, and other types by
    /// structure through the `eq` and `cmp` glue.
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
        let b_ref = self.operand(args[0]);
        let b_pl = self.op_place(b_ref, self.ty(args[0]), span);
        // One comparison of the two sides as a `bool` rvalue. The
        // eq test of `partial_cmp` asks `<=` after `<` failed: that
        // is "equal" exactly as the type's `partial_cmp` orders,
        // also for a structure whose `PartialEq` is not derived.
        let scalar = matches!(self.kind(recv_ty), TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char);
        let is_str = self.kind(recv_ty) == TyKind::Str;
        let (a_ref, b_ref) = (Operand::Copy(Place::local(rt)), Operand::Copy(b_pl.clone()));
        let (code_a, code_b) = (a_ref.clone(), b_ref.clone());
        let rv = move |op: BinOp| -> Rvalue {
            if scalar {
                Rvalue::Bin(op, Operand::Copy(Place::local(rt).deref()), Operand::Copy(b_pl.deref()))
            } else if is_str {
                Rvalue::StrCmp(op, a_ref.clone(), b_ref.clone())
            } else if matches!(op, BinOp::Eq | BinOp::Ne) {
                Rvalue::Eq { a: a_ref.clone(), b: b_ref.clone(), ty: recv_ty, ne: op == BinOp::Ne }
            } else {
                Rvalue::Cmp { op, a: a_ref.clone(), b: b_ref.clone(), ty: recv_ty }
            }
        };
        match kind {
            Ck::Op(op) => self.assign(out, rv(op), span),
            Ck::Total(adt) | Ck::Partial(adt) => {
                let partial = matches!(kind, Ck::Partial(_));
                // A structural type compares once, through the cmp
                // glue's code (-1, 0, 1, or 2 for unordered); the
                // tests below then read that code.
                let code = if scalar || is_str {
                    None
                } else {
                    let i8_ty = int(IntTy::I8);
                    let c = self.temp(i8_ty);
                    self.call_into(CallTarget::Builtin(Builtin::CmpCode), vec![code_a, code_b], Place::local(c), span);
                    Some(c)
                };
                let cmp = |this: &mut Self, op: BinOp| {
                    let t = this.temp(BOOL);
                    let r = match code {
                        Some(c) => {
                            let want: i128 = match op {
                                BinOp::Lt => -1,
                                BinOp::Gt => 1,
                                _ => 0,
                            };
                            Rvalue::Bin(BinOp::Eq, Operand::Copy(Place::local(c)), Operand::Const(Const::Int(want as u128, IntTy::I8)))
                        }
                        None => rv(op),
                    };
                    this.assign(Place::local(t), r, span);
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

    /// Calls a written comparison method `f` on the borrowed sides `a`
    /// and `b` and writes the answer `via` asks for into `out`: the
    /// method's own `bool`, its negation (`ne` through `eq`), or a
    /// test of its `Option<Ordering>` (`lt` and kin through
    /// `partial_cmp`, as core's default bodies).
    fn trait_cmp_call(&mut self, f: LocalDefId, a: Operand, b: Operand, via: CmpVia, out: Place, span: Span) {
        match via {
            CmpVia::Direct => self.call_into(CallTarget::Fn(f), vec![a, b], out, span),
            CmpVia::NotEq => {
                let t = self.temp(BOOL);
                self.call_into(CallTarget::Fn(f), vec![a, b], Place::local(t), span);
                self.assign(out, Rvalue::Un(crate::ast::UnOp::Not, Operand::Copy(Place::local(t))), span);
            }
            CmpVia::Partial(op) => {
                let ret = self.p.fn_info(f).ret;
                let t = self.temp(ret);
                self.call_into(CallTarget::Fn(f), vec![a, b], Place::local(t), span);
                self.ordering_test(Place::local(t), op, out, span);
            }
        }
    }

    /// Writes `opt <op> Some(Equal)` for an `Option<Ordering>` place
    /// into `out`, as `PartialOrd::lt` and kin answer from
    /// `partial_cmp`: false on `None`, else the variant index of the
    /// `Ordering` (Less 0, Equal 1, Greater 2) against Equal's.
    fn ordering_test(&mut self, opt: Place, op: BinOp, out: Place, span: Span) {
        let u32_ty = int(IntTy::U32);
        let d = self.temp(u32_ty);
        self.assign(Place::local(d), Rvalue::Discriminant(opt.clone()), span);
        let (some_b, none_b, end) = (self.new_block(), self.new_block(), self.new_block());
        let b = &mut self.body.blocks[self.cur.0 as usize];
        b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(1, some_b)], none_b);
        b.term_span = span;
        self.cur = none_b;
        self.assign(out.clone(), Rvalue::Use(Operand::Const(Const::Bool(false))), span);
        self.goto(end, span);
        self.cur = some_b;
        let k = self.temp(u32_ty);
        self.assign(Place::local(k), Rvalue::Discriminant(opt.project(Proj::Downcast(1)).project(Proj::Field(0))), span);
        self.assign(out, Rvalue::Bin(op, Operand::Copy(Place::local(k)), Operand::Const(Const::Int(1, IntTy::U32))), span);
        self.goto(end, span);
    }

    /// A `core::cmp::Ordering` method (`Res::OrderingOp`): the
    /// receiver's variant index (Less 0, Equal 1, Greater 2) decides.
    /// `then` evaluates its argument after the receiver, as a call
    /// does, and keeps the receiver unless it is `Equal`.
    #[allow(clippy::too_many_arguments)]
    fn ordering_op_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], dest: Option<&Place>, span: Span, kind: OrderingOpKind, derefs: u8) {
        use OrderingOpKind as K;
        let ty = self.ty(e);
        let ord_ty = self.peel(self.ty(recv), derefs);
        let Some(adt) = self.body.tys.local_adt(ord_ty) else { return };
        let r = self.temp(ord_ty);
        let op = self.operand_derefs(recv, derefs);
        self.assign(Place::local(r), Rvalue::Use(op), span);
        let u32_ty = int(IntTy::U32);
        let d = self.temp(u32_ty);
        self.assign(Place::local(d), Rvalue::Discriminant(Place::local(r)), span);
        let out = self.call_dest(dest, ty);
        let test = |op: BinOp| Rvalue::Bin(op, Operand::Copy(Place::local(d)), Operand::Const(Const::Int(1, IntTy::U32)));
        match kind {
            K::IsEq => self.assign(out, test(BinOp::Eq), span),
            K::IsNe => self.assign(out, test(BinOp::Ne), span),
            K::IsLt => self.assign(out, test(BinOp::Lt), span),
            K::IsGt => self.assign(out, test(BinOp::Gt), span),
            K::IsLe => self.assign(out, test(BinOp::Le), span),
            K::IsGe => self.assign(out, test(BinOp::Ge), span),
            K::Reverse => {
                let (b0, b1, b2, end) = (self.new_block(), self.new_block(), self.new_block(), self.new_block());
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(0, b0), (1, b1)], b2);
                b.term_span = span;
                for (blk, v) in [(b0, 2u32), (b1, 1), (b2, 0)] {
                    self.cur = blk;
                    self.assign(out.clone(), Rvalue::Aggregate(adt, v, Vec::new()), span);
                    self.goto(end, span);
                }
            }
            K::ThenWith => {
                // The closure moves into a local; it runs only on Equal.
                let fty = self.ty(args[0]);
                let c = self.temp(fty);
                self.expr_into(args[0], Some(&Place::local(c)));
                let eq = self.temp(BOOL);
                self.assign(Place::local(eq), test(BinOp::Eq), span);
                let (t, f, end) = (self.new_block(), self.new_block(), self.new_block());
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::If(Operand::Copy(Place::local(eq)), t, f);
                b.term_span = span;
                self.cur = t;
                self.call_closure_once(Place::local(c), fty, out.clone(), span);
                self.goto(end, span);
                self.cur = f;
                self.assign(out, Rvalue::Use(Operand::Copy(Place::local(r))), span);
                if needs_drop(self.p, &self.body.tys, fty) {
                    self.push(StmtKind::Drop(c), span);
                }
                self.goto(end, span);
            }
            K::Then => {
                let o = self.temp(ord_ty);
                self.expr_into(args[0], Some(&Place::local(o)));
                let eq = self.temp(BOOL);
                self.assign(Place::local(eq), test(BinOp::Eq), span);
                let (t, f, end) = (self.new_block(), self.new_block(), self.new_block());
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::If(Operand::Copy(Place::local(eq)), t, f);
                b.term_span = span;
                self.cur = t;
                self.assign(out.clone(), Rvalue::Use(Operand::Copy(Place::local(o))), span);
                self.goto(end, span);
                self.cur = f;
                self.assign(out, Rvalue::Use(Operand::Copy(Place::local(r))), span);
                self.goto(end, span);
            }
        }
    }

    /// Calls the closure value at `place` (type `fty`) with no
    /// arguments through `FnOnce`, into `dest`: an `FnOnce` closure
    /// takes its env by value, the others by reference (the value
    /// itself then drops after the call, as the moved callee would).
    fn call_closure_once(&mut self, place: Place, fty: Ty, dest: Place, span: Span) {
        use crate::check::closure::ClosureKind;
        let TyKind::Closure(def, _) = self.kind(fty) else { return };
        let Some(entry) = self.p.gx.closures.get(&def) else { return };
        let (body_fn, kind) = (entry.body_fn, entry.kind);
        let env = match kind {
            ClosureKind::FnOnce => self.operand_from(place.clone(), fty),
            ClosureKind::Fn | ClosureKind::FnMut => {
                let mutable = kind == ClosureKind::FnMut;
                let rt = self.ref_ty(mutable, fty);
                let t = self.temp(rt);
                self.assign(Place::local(t), Rvalue::Ref(mutable, place.clone()), span);
                Operand::Move(Place::local(t))
            }
        };
        self.call_into(CallTarget::Fn(body_fn), vec![env], dest, span);
        if kind != ClosureKind::FnOnce && needs_drop(self.p, &self.body.tys, fty) {
            self.push(StmtKind::Drop(place.local), span);
        }
    }

    /// One `PartialOrd` test `a <op> b` between two places of type
    /// `ty` for `Res::OrdPick`, into a fresh `bool` local: through the
    /// written method `f` (`via`), or by structure.
    fn pick_cmp(&mut self, f: Option<LocalDefId>, via: CmpVia, op: BinOp, a: &Place, b: &Place, ty: Ty, span: Span) -> Local {
        let c = self.temp(BOOL);
        let rt = self.ref_ty(false, ty);
        let (ra, rb) = (self.temp(rt), self.temp(rt));
        self.assign(Place::local(ra), Rvalue::Ref(false, a.clone()), span);
        self.assign(Place::local(rb), Rvalue::Ref(false, b.clone()), span);
        let (ra, rb) = (Operand::Copy(Place::local(ra)), Operand::Copy(Place::local(rb)));
        match f {
            Some(f) => {
                // `max`/`min` may call the impl's own `lt`; every other
                // test goes through `partial_cmp`.
                let via = if op == BinOp::Lt { via } else { CmpVia::Partial(op) };
                self.trait_cmp_call(f, ra, rb, via, Place::local(c), span);
            }
            None => {
                // `Ord for &A` compares the pointees.
                let (mut a, mut b, mut ty, mut ra, mut rb) = (a.clone(), b.clone(), ty, ra, rb);
                while let TyKind::Ref(_, _, inner) = self.kind(ty) {
                    (ra, rb) = (Operand::Copy(a.clone()), Operand::Copy(b.clone()));
                    (a, b, ty) = (a.deref(), b.deref(), inner);
                }
                let rv = match self.kind(ty) {
                    TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char => Rvalue::Bin(op, Operand::Copy(a), Operand::Copy(b)),
                    _ => Rvalue::Cmp { op, a: ra, b: rb, ty },
                };
                self.assign(Place::local(c), rv, span);
            }
        }
        c
    }

    /// `Ord::max`, `min`, and `clamp` (`Res::OrdPick`) by core's
    /// default bodies: the receiver and the arguments move into
    /// locals in order, the comparisons run as in core
    /// (`max`/`min`: `other < self`; `clamp`: `assert!(min <= max)`,
    /// then `self < min`, then `self > max`), the answer moves out,
    /// and the other values drop right there, in reverse parameter
    /// order, as the callee's parameters would.
    #[allow(clippy::too_many_arguments)]
    fn ord_pick_into(
        &mut self,
        e: ExprId,
        recv: ExprId,
        args: &[ExprId],
        dest: Option<&Place>,
        span: Span,
        kind: OrdPickKind,
        f: Option<LocalDefId>,
        via: CmpVia,
    ) {
        let ty = self.ty(e);
        let mut vals: Vec<Local> = Vec::with_capacity(args.len() + 1);
        for &x in std::iter::once(&recv).chain(args) {
            let l = self.temp(ty);
            self.expr_into(x, Some(&Place::local(l)));
            vals.push(l);
        }
        let out = self.call_dest(dest, ty);
        let pl = |l: Local| Place::local(l);
        // Moves value `win` into `out`, then drops the others in
        // reverse parameter order.
        let finish = |this: &mut Self, win: usize, vals: &[Local], end: Bb| {
            let op = this.operand_from(pl(vals[win]), ty);
            this.assign(out.clone(), Rvalue::Use(op), span);
            for (i, &l) in vals.iter().enumerate().rev() {
                if i != win && needs_drop(this.p, &this.body.tys, ty) {
                    this.push(StmtKind::Drop(l), span);
                }
            }
            this.goto(end, span);
        };
        let end = self.new_block();
        let branch = |this: &mut Self, c: Local| -> (Bb, Bb) {
            let (t, f) = (this.new_block(), this.new_block());
            let b = &mut this.body.blocks[this.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), t, f);
            b.term_span = span;
            (t, f)
        };
        match kind {
            OrdPickKind::Max | OrdPickKind::Min => {
                // `other < self`: Max keeps self, Min keeps other.
                let c = self.pick_cmp(f, via, BinOp::Lt, &pl(vals[1]), &pl(vals[0]), ty, span);
                let (t, el) = branch(self, c);
                let (on_true, on_false) = if kind == OrdPickKind::Max { (0, 1) } else { (1, 0) };
                self.cur = t;
                finish(self, on_true, &vals, end);
                self.cur = el;
                finish(self, on_false, &vals, end);
            }
            OrdPickKind::Clamp => {
                let ok = self.pick_cmp(f, via, BinOp::Le, &pl(vals[1]), &pl(vals[2]), ty, span);
                let (good, bad) = branch(self, ok);
                self.cur = bad;
                self.terminate(Terminator::Panic(vec![FmtPart::Lit("assertion failed: min <= max".into())]), span);
                self.cur = good;
                let below = self.pick_cmp(f, via, BinOp::Lt, &pl(vals[0]), &pl(vals[1]), ty, span);
                let (t, el) = branch(self, below);
                self.cur = t;
                finish(self, 1, &vals, end);
                self.cur = el;
                let above = self.pick_cmp(f, via, BinOp::Gt, &pl(vals[0]), &pl(vals[2]), ty, span);
                let (t2, el2) = branch(self, above);
                self.cur = t2;
                finish(self, 2, &vals, end);
                self.cur = el2;
                finish(self, 0, &vals, end);
            }
        }
        self.cur = end;
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
            // core's blanket `IntoIterator for I: Iterator`: the receiver moves through.
            K::IntoIterSelf => {
                let a = self.operand_derefs(recv, derefs);
                self.set_or_temp(dest, Rvalue::Use(a), self.ty(e), span);
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
        // A method call reports caller locations (track_caller builtins
        // such as unwrap and pow) at the method name, as rustc does, not
        // at the receiver. A qualified-path call (`Type::name(..)`) is a
        // plain call here and keeps the whole-expression span.
        let span = match self.p.ast.expr(e) {
            Expr::MethodCall { name_span, .. } => *name_span,
            _ => span,
        };
        if let Res::BuiltinMethod { b: Builtin::FmtWriteFmt, derefs, .. } = self.ck.res(e) {
            self.write_fmt_into(e, recv, args, derefs, dest, span);
            return;
        }
        if let Res::PrimCmp { kind, derefs } = self.ck.res(e) {
            self.prim_cmp_into(e, recv, args, dest, span, kind, derefs);
            return;
        }
        if let Res::TraitCmpMethod { f, derefs, via } = self.ck.res(e) {
            let f = self.resolve_generic_fn(e, f);
            let recv_ty = self.peel(self.ty(recv), derefs);
            let pl = Self::derefs(self.place(recv), derefs);
            let rt_ty = self.ref_ty(false, recv_ty);
            let rt = self.temp(rt_ty);
            self.assign(Place::local(rt), Rvalue::Ref(false, pl), span);
            let b = self.operand(args[0]);
            let out = self.call_dest(dest, BOOL);
            self.trait_cmp_call(f, Operand::Copy(Place::local(rt)), b, via, out, span);
            return;
        }
        if let Res::OrderingOp { kind, derefs } = self.ck.res(e) {
            self.ordering_op_into(e, recv, args, dest, span, kind, derefs);
            return;
        }
        if let Res::Any { op, derefs, autoref } = self.ck.res(e) {
            self.any_op_into(e, recv, dest, span, op, derefs, autoref);
            return;
        }
        if let Res::OrdPick { kind, f, via } = self.ck.res(e) {
            let f = f.map(|f| self.resolve_generic_fn(e, f));
            self.ord_pick_into(e, recv, args, dest, span, kind, f, via);
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
        // Through a user `Deref` impl (check's `DerefRecv`): borrow the
        // receiver, call the impl's `deref` (or `deref_mut`), and apply
        // the call's derefs and autoref to the `&Target` it returns.
        let root = self.deref_steps(e, recv, span);
        let root_ty = match &root {
            Some(pl) => self.body.locals[pl.local as usize].ty,
            None => self.ty(recv),
        };
        let recv_ty = self.peel(root_ty, derefs);
        let mut ops = Vec::with_capacity(args.len() + 1);
        match autoref {
            Autoref::None => {
                let o = match &root {
                    Some(pl) => self.operand_from(Self::derefs(pl.clone(), derefs), recv_ty),
                    None => self.operand_derefs(recv, derefs),
                };
                ops.push(o);
                for &a in args {
                    let o = self.operand(a);
                    ops.push(o);
                }
            }
            Autoref::Ref => {
                let pl = match &root {
                    Some(pl) => pl.clone(),
                    None => self.place(recv),
                };
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
                let pl = match &root {
                    Some(pl) => pl.clone(),
                    None => self.place_for_mut(recv),
                };
                let pl = Self::derefs(pl, derefs);
                let mt = self.ref_ty(true, recv_ty);
                let via_deref = matches!(callee, Callee::Builtin(b) if self.slice_method_via_deref(b, recv_ty));
                if via_deref || pl.proj.iter().any(|x| matches!(x, Proj::Index(_))) {
                    // The receiver is reached through an `IndexMut` borrow or a slice
                    // method's `DerefMut`/unsize, which is not two-phase: take the `&mut`
                    // before the arguments run, so an argument that borrows the container
                    // again is an error, as in rustc.
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
                let r = ops.remove(0);
                // A `dyn Fn` value called as a function uses its own
                // principal's call entry: no upcast.
                let r = match self.p.ast.expr(e) {
                    Expr::MethodCall { name, .. } => self.dyn_receiver(r, recv_ty, autoref == Autoref::RefMut, owner, cand, *name, span),
                    _ => r,
                };
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

    /// True when a `&mut self` builtin is a slice method called on a `Vec`
    /// or an array (`v.swap(..)`, `a.get_mut(..)`): rustc reaches the slice
    /// through `DerefMut` or an unsize, so its autoref is not a two-phase
    /// borrow. On a slice place (`s.swap(..)` with `s: &mut [T]`) it is.
    fn slice_method_via_deref(&self, b: Builtin, recv_ty: Ty) -> bool {
        use Builtin as B;
        matches!(b, B::VecSwap | B::VecReverse | B::VecFirstMut | B::VecLastMut | B::VecGetMut | B::IterIterMut)
            && (self.body.tys.vec_elem(recv_ty).is_some() || matches!(self.kind(recv_ty), TyKind::Array(..)))
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
        if let Res::TraitCmp { f, ld, rd, via } = self.ck.res(e) {
            let f = self.resolve_generic_fn(e, f);
            let (a, _) = self.borrow_of(lhs, ld);
            let (b, _) = self.borrow_of(rhs, rd);
            self.trait_cmp_call(f, a, b, via, out, span);
            return;
        }
        if matches!(op, BinOp::And | BinOp::Or) {
            // Short circuit. Both sides write a mutable temporary, and the destination is
            // written once at the end. Writing the destination twice would make the borrow
            // checker see `let hot = a && b;` as two assignments to an immutable binding.
            // Each side is a terminating scope, as in rustc: its temporaries drop right
            // after it.
            let tmp = Place::local(self.temp(ty));
            self.scopes.push(Vec::new());
            self.expr_into(lhs, Some(&tmp));
            self.pop_scope(span);
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
        if op.is_cmp() && !matches!(op, BinOp::Eq | BinOp::Ne) && matches!(self.kind(base), TyKind::Tuple(_) | TyKind::Unit) && self.expands_ord(base) {
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
                _ if matches!(op, BinOp::Eq | BinOp::Ne) => {
                    let (a, t) = self.borrow_of(lhs, ld);
                    let (b, _) = self.borrow_of(rhs, rd);
                    Rvalue::Eq { a, b, ty: t, ne: op == BinOp::Ne }
                }
                // Ordering by structure (`has_ord`): the `cmp` glue.
                _ => {
                    let (a, t) = self.borrow_of(lhs, ld);
                    let (b, _) = self.borrow_of(rhs, rd);
                    Rvalue::Cmp { op, a, b, ty: t }
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

    /// True when an ordering of `ty` expands in lowering (`ord_into`):
    /// tuples whose elements are scalars, strings, references to
    /// such, or tuples of such. Other orderable types compare
    /// through the `cmp` glue (`Rvalue::Cmp`).
    fn expands_ord(&self, ty: Ty) -> bool {
        match self.kind(ty) {
            TyKind::Unit | TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Str => true,
            TyKind::Ref(_, _, e) => self.expands_ord(e),
            TyKind::Tuple(ts) => self.body.tys.tys_of(ts).to_vec().into_iter().all(|e| self.expands_ord(e)),
            _ => self.body.tys.is_string_ty(ty),
        }
    }

    /// Writes the comparison `a <op> b` for orderable places into
    /// `out`. Tuples expand lexicographically, field by field, with a
    /// short circuit on the first unequal field; equality of nested
    /// tuples expands the same way. The checker gates the shapes this
    /// can see through `has_ord`; the caller sends only the shapes
    /// `expands_ord` accepts.
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

    /// For an mpsc `Receiver<T>` (true) or `&Receiver<T>` (false): the
    /// element type `T`.
    fn recv_iterable(&self, t: Ty) -> Option<(bool, Ty)> {
        let (owned, r) = match self.kind(t) {
            TyKind::Ref(_, m, inner) if !m.is_mut() => (false, inner),
            _ => (true, t),
        };
        (crate::ty::sync::sync_kind(&self.body.tys, r) == Some(crate::ty::sync::SyncTy::Receiver)).then(|| self.body.tys.adt_first_ty_arg(r)).flatten().map(|e| (owned, e))
    }

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
        let item_ty = self.for_item_ty(for_e, pat, iter);
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
        } else if crate::ty::iter::is_iter(&self.body.tys, self.ty(iter))
            || self.body.tys.boxed_slice_elem(self.ty(iter)).is_some()
            || self.recv_iterable(self.ty(iter)).is_some()
        {
            // `for x in it` over a builtin iterator (ty/iter.rs): call
            // `next` until it returns None, like the Chars arm. A boxed
            // slice by value iterates its `vec::IntoIter` (Rust 2024).
            let recv = self.recv_iterable(self.ty(iter));
            let (it_ty, it) = match self.body.tys.boxed_slice_elem(self.ty(iter)) {
                // An mpsc receiver (W-THREADS): `for x in rx` iterates
                // its `IntoIter`, `for x in &rx` its `Iter`.
                _ if let Some((owned, el)) = recv => {
                    let src = self.temp(self.ty(iter));
                    self.expr_into(iter, Some(&Place::local(src)));
                    let k = if owned { crate::ty::iter::IterKind::RecvIntoIter } else { crate::ty::iter::IterKind::RecvIter };
                    let it_ty = crate::ty::iter::mk_iter(&mut self.body.tys, k, &[el]);
                    let it = self.temp(it_ty);
                    let op = crate::check::sync::SyncOp::RecvMakeIter(if owned { 2 } else { 0 });
                    self.call_into(CallTarget::Builtin(Builtin::Sync(op)), vec![Operand::Move(Place::local(src))], Place::local(it), span);
                    (it_ty, it)
                }
                Some(el) => {
                    let bx = self.temp(self.ty(iter));
                    self.expr_into(iter, Some(&Place::local(bx)));
                    let it_ty = crate::ty::iter::mk_iter(&mut self.body.tys, crate::ty::iter::IterKind::VecIntoIter, &[el]);
                    let it = self.temp(it_ty);
                    self.call_into(CallTarget::Builtin(Builtin::BoxSliceIntoIter), vec![Operand::Move(Place::local(bx))], Place::local(it), span);
                    (it_ty, it)
                }
                None => {
                    let it_ty = self.ty(iter);
                    let it = self.temp(it_ty);
                    self.expr_into(iter, Some(&Place::local(it)));
                    (it_ty, it)
                }
            };
            self.goto(head, span);
            let mt = self.ref_ty(true, it_ty);
            let r = self.temp(mt);
            self.assign(Place::local(r), Rvalue::Ref(true, Place::local(it)), span);
            let ot = self.body.tys.mk_option(item_ty);
            let nx = self.temp(ot);
            self.call_into(CallTarget::Builtin(Builtin::IterNext), vec![Operand::Move(Place::local(r))], Place::local(nx), span);
            let d = self.temp(int(IntTy::U32));
            self.assign(Place::local(d), Rvalue::Discriminant(Place::local(nx)), span);
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(1, bodyb)], exit);
            self.cur = bodyb;
            let c = Place::local(nx).project(Proj::Downcast(1)).project(Proj::Field(0));
            let op = self.operand_from(c, item_ty);
            self.assign(Place::local(item), Rvalue::Use(op), span);
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

    /// The type of a `for` loop's item: the pattern's type, or, when the
    /// pattern matches through references (default binding modes:
    /// `for (k, v) in &map_vec`, `pat_derefs`), the iterator's item those
    /// references wrap, which `bind_pat` derefs.
    fn for_item_ty(&mut self, for_e: ExprId, pat: PatId, iter: ExprId) -> Ty {
        let pt = self.ck.pat_ty(pat);
        if self.ck.pat_derefs(pat) == 0 {
            return pt;
        }
        let it = self.ty(iter);
        let elem = |this: &Self, t: Ty| match this.kind(t) {
            TyKind::Array(e, _) | TyKind::Slice(e) => Some(e),
            _ => this.body.tys.vec_elem(t),
        };
        let item = if let Res::ForTrait { next, .. } = self.ck.res(for_e) {
            let ret = self.p.fn_info(self.resolve_generic_fn(iter, next)).ret;
            self.body.tys.option_elem(ret)
        } else if crate::ty::iter::is_iter(&self.body.tys, it) {
            crate::ty::iter::item_ty(&mut self.body.tys, it)
        } else if let TyKind::Ref(_, m, inner) = self.kind(it) {
            elem(self, inner).map(|e| self.ref_ty(m == Mut::Mut, e))
        } else {
            elem(self, it)
        };
        item.unwrap_or(pt)
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
                middle.is_some_and(|m| self.pat_moves_noncopy(m)) || prefix.iter().chain(suffix.iter()).any(|&s| self.pat_moves_noncopy(s))
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
        // Temporaries in the scrutinee belong to the enclosing scope, as
        // in rustc (the scrutinee is not a terminating scope): in a `let`
        // or a call argument they live to the end of the statement.
        // Arms bind out of the scrutinee place itself, as in rustc: an
        // arm that moves a part is a partial move of that place, and
        // the rest drops with it (codegen elaborates the drop).
        let sp = self.place(scrut);
        let arm_pats: Vec<PatId> = arms.iter().map(|a| a.pat).collect();
        let scrut_ty = self.ty(scrut);
        let sp = self.pattern_place(sp, scrut_ty, &arm_pats, span);
        let end = self.new_block();
        // Reference-typed arms after the first that does not diverge are
        // reborrowed (`arm_into`).
        let first = arms.iter().position(|a| !self.diverges(a.body));
        let reborrow = first.is_some_and(|i| self.reborrows_arms(self.ty(arms[i].body)));
        for (ai, arm) in arms.iter().enumerate() {
            // A guard reads the arm's bindings by shared reference
            // (rustc binds pattern variables by reference for the
            // guard, then by their declared mode in the arm body):
            // bind for the guard first, and do the real binding,
            // moves included, only on the guard's success edge. A
            // failed guard then leaves the scrutinee whole for the
            // next arm. The one shape with no reference place to
            // read through, a by-value binding for the middle of
            // an array pattern, keeps the move-first order.
            let by_ref_guard = arm.guard.is_some() && !self.pat_has_slice_middle_move(arm.pat);
            // Under a guard, an or-pattern arm runs as one row
            // per combination of alternatives: a guard that
            // fails on one row tries the next matching row, as
            // in Rust, before the next arm (so the guard may run
            // more than once). Rows beyond a bound
            // keep the single tag-switched test; the checker
            // accepts those programs, so cap the expansion and
            // report it below instead of risking such a split.
            let rows: Vec<Vec<(PatId, usize)>> =
                if by_ref_guard && self.pat_has_or(arm.pat) { self.or_rows(arm.pat) } else { vec![Vec::new()] };
            if rows.len() > 64 {
                self.body.lower_errs.push(crate::diag::Diag::new(
                    "L9001",
                    span,
                    "a match guard over this many or-pattern alternatives is not supported yet",
                    "Split the arm into several arms, one per alternative.",
                ));
            }
            let expanded = rows.len() > 1 && rows.len() <= 64;
            let rows: Vec<Vec<(PatId, usize)>> = if expanded { rows } else { vec![Vec::new()] };
            let next = self.new_block();
            let body_bb = self.new_block();
            let row_starts: Vec<Bb> = (0..rows.len()).map(|r| if r == 0 { self.cur } else { self.new_block() }).collect();
            // A match nested in this arm's guard manages its own
            // rows; the outer rows resume after it.
            let saved_forced = std::mem::take(&mut self.or_forced);
            self.scopes.push(Vec::new());
            for (r, row) in rows.iter().enumerate() {
                self.cur = row_starts[r];
                let row_fail = if r + 1 < rows.len() { row_starts[r + 1] } else { next };
                self.or_forced = row.clone();
                self.test_pat(arm.pat, sp.clone(), row_fail);
                if arm.guard.is_none() {
                    self.false_edge_if_unreached(row_starts[r], next);
                }
                let mut guard_bound: Vec<u32> = Vec::new();
                let guard_popped;
                if by_ref_guard {
                    self.scopes.push(Vec::new());
                    self.bind_pat_guard(arm.pat, sp.clone(), &mut guard_bound);
                    guard_popped = false;
                } else {
                    self.bind_pat(arm.pat, sp.clone());
                    guard_popped = true;
                }
                match arm.guard {
                    Some(g) => {
                        let gspan = self.span(g);
                        self.scopes.push(Vec::new());
                        let held = self.hold_scrutinee(&sp, scrut_ty, gspan);
                        let c = self.operand(g);
                        // Mutable: the same local is written again on every
                        // pass when the match sits in a loop.
                        let cl = self.new_local(BOOL, true, None);
                        self.assign(Place::local(cl), Rvalue::Use(c), gspan);
                        self.push(StmtKind::FakeRead(held), gspan);
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
                        self.goto(row_fail, gspan);
                        self.cur = ok;
                        if by_ref_guard {
                            // End the guard bindings' storage before the
                            // real binding moves out of the same places.
                            self.emit_drops(&arm_locals, gspan);
                            self.scopes.pop();
                            self.bind_pat(arm.pat, sp.clone());
                        }
                    }
                    None => {
                        debug_assert!(!expanded, "rows only expand under a guard");
                    }
                }
                if by_ref_guard && !guard_popped && arm.guard.is_none() {
                    self.scopes.pop();
                }
                self.goto(body_bb, span);
            }
            self.or_forced = saved_forced;
            self.cur = body_bb;
            let rb = reborrow && first.is_some_and(|i| ai > i) && !self.diverges(arm.body);
            self.arm_into(arm.body, rb, dest);
            self.pop_scope(span);
            self.goto(end, span);
            self.cur = next;
        }
        self.terminate(Terminator::Unreachable, span);
        self.cur = end;
    }

    /// A shared borrow of the scrutinee place that a guard holds until it
    /// ends (the caller emits the `FakeRead` of the returned local), as
    /// rustc's fake borrows of the matched places: a guard cannot assign
    /// to the scrutinee or borrow it mutably (E0510). rustc's borrows are
    /// shallow and cover only tested places; this one is deep, so a guard
    /// that writes an untested part is a false reject.
    fn hold_scrutinee(&mut self, sp: &Place, ty: Ty, span: Span) -> Local {
        let rt = self.ref_ty(false, ty);
        let t = self.temp(rt);
        self.assign(Place::local(t), Rvalue::Ref(false, sp.clone()), span);
        t
    }

    /// After an arm's pattern tests, which began in block `start`: when
    /// none of them jumps to `next` (the pattern is irrefutable), ends the
    /// current block and adds a borrowck-only edge from it to `next`, as
    /// rustc's false edge does, so the later arms are borrow-checked. The
    /// tests' blocks are `start` and every block made after `next`.
    fn false_edge_if_unreached(&mut self, start: Bb, next: Bb) {
        let jumps = |t: &Terminator| match t {
            Terminator::Goto(b) => *b == next,
            Terminator::If(_, a, b) => *a == next || *b == next,
            Terminator::Switch(_, cases, other) => *other == next || cases.iter().any(|c| c.1 == next),
            _ => false,
        };
        let blocks = &self.body.blocks;
        if jumps(&blocks[start.0 as usize].term) || blocks[next.0 as usize..].iter().any(|b| jumps(&b.term)) {
            return;
        }
        let pre = self.cur;
        let bind = self.new_block();
        self.goto(bind, Span::default());
        self.body.false_edges.push((pre, next));
    }

    /// True when a slice pattern in `pat` binds its middle by
    /// value: an owned smaller array (`rest @ ..` on an array).
    /// That value has no place to read by reference for a guard
    /// without moving the elements out, so `match_into` keeps
    /// the move-first order for such an arm (element copies on
    /// the guard edge; a non-`Copy` middle then fails borrowck
    /// when a later arm needs the scrutinee, as before). A
    /// middle of slice type is a fat value instead: the guard
    /// binds it by reference from a subslice temporary, like
    /// every other binding.
    fn pat_has_slice_middle_move(&self, pat: PatId) -> bool {
        if let Pat::Slice { middle, .. } = self.p.ast.pat(pat)
            && let Some(mid) = middle
            && self.pat_has_binding(*mid)
            && !matches!(self.kind(self.ck.pat_ty(*mid)), TyKind::Slice(_))
        {
            return true;
        }
        self.pat_children(pat).iter().any(|&s| self.pat_has_slice_middle_move(s))
    }

    /// A temporary holding the middle of a slice or array place
    /// as a slice fat value: elements `lo_n` up to `suffix_len`
    /// before the end.
    fn subslice_temp(&mut self, place: &Place, lo_n: usize, suffix_len: usize, arr_len: Option<u64>, elem: Ty, mutable: bool, span: Span) -> Local {
        let lo = self.const_usize(lo_n as u64, span);
        let hi = match arr_len {
            Some(n) => Operand::Const(Const::Int((n - suffix_len as u64) as u128, IntTy::Usize)),
            None => {
                let len = self.temp(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(place.clone()), span);
                let t = self.temp(USIZE);
                self.assign(
                    Place::local(t),
                    Rvalue::Bin(BinOp::Sub, Operand::Copy(Place::local(len)), Operand::Const(Const::Int(suffix_len as u128, IntTy::Usize))),
                    span,
                );
                Operand::Copy(Place::local(t))
            }
        };
        let slice = self.body.tys.intern(TyKind::Slice(elem));
        let t = self.temp(slice);
        self.assign(
            Place::local(t),
            Rvalue::Subslice { base: place.clone(), lo: Operand::Copy(Place::local(lo)), hi: Some(hi), inclusive: false, mutable },
            span,
        );
        t
    }

    /// The direct sub-patterns of one pattern, in source order.
    fn pat_children(&self, pat: PatId) -> Vec<PatId> {
        match self.p.ast.pat(pat) {
            Pat::TupleStruct { elems, .. } | Pat::Tuple(elems) | Pat::Or(elems) => elems.clone(),
            Pat::Struct { fields, .. } => fields.iter().map(|&(_, s)| s).collect(),
            Pat::Slice { prefix, middle, suffix } => {
                let mut out: Vec<PatId> = prefix.clone();
                if let Some(m) = middle {
                    out.push(*m);
                }
                out.extend(suffix.iter().copied());
                out
            }
            Pat::Paren(i) | Pat::Ref { inner: i, .. } | Pat::At { inner: i, .. } => vec![*i],
            _ => Vec::new(),
        }
    }

    /// True when the pattern binds any name, itself or below.
    fn pat_has_binding(&self, pat: PatId) -> bool {
        matches!(self.ck.pat_res(pat), PatRes::Binding { .. }) || self.pat_children(pat).iter().any(|&s| self.pat_has_binding(s))
    }

    /// True when the pattern holds an or-pattern: the shape whose
    /// alternatives a guard must retry. Rust runs the guard once per
    /// matching combination of alternatives, with or without bindings
    /// (`Some(_) | Some(3) if g()` calls `g` twice on `Some(3)`).
    fn pat_has_or(&self, pat: PatId) -> bool {
        matches!(self.p.ast.pat(pat), Pat::Or(_)) || self.pat_children(pat).iter().any(|&s| self.pat_has_or(s))
    }

    /// The alternative a guard row fixes this or-pattern to.
    fn or_forced(&self, pat: PatId) -> Option<usize> {
        self.or_forced.iter().find(|&&(q, _)| q == pat).map(|&(_, i)| i)
    }

    /// The tag local for an or-pattern, made on first test.
    fn or_tag(&mut self, pat: PatId) -> Local {
        if let Some(&(_, l)) = self.or_tags.iter().find(|&&(q, _)| q == pat) {
            return l;
        }
        let l = self.temp(int(IntTy::U32));
        self.or_tags.push((pat, l));
        l
    }

    /// Every combination of or-pattern alternatives in one
    /// pattern, as a list of (or-pattern, alternative index)
    /// rows. Rust tries the rows in this order under a guard:
    /// a later or-pattern's alternatives cycle first.
    fn or_rows(&self, pat: PatId) -> Vec<Vec<(PatId, usize)>> {
        if let Pat::Or(alts) = self.p.ast.pat(pat) {
            let mut rows = Vec::new();
            for (i, &alt) in alts.iter().enumerate() {
                for sub in self.or_rows(alt) {
                    let mut row = vec![(pat, i)];
                    row.extend(sub);
                    rows.push(row);
                }
            }
            return rows;
        }
        let mut rows: Vec<Vec<(PatId, usize)>> = vec![Vec::new()];
        for child in self.pat_children(pat) {
            let sub = self.or_rows(child);
            let mut next = Vec::with_capacity(rows.len() * sub.len());
            for row in &rows {
                for s in &sub {
                    let mut r = row.clone();
                    r.extend(s.iter().copied());
                    next.push(r);
                }
            }
            rows = next;
        }
        rows
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
        // Every alternative (and guard row) that binds this
        // local writes the one guard temporary: the blocks
        // merge before the guard reads it.
        let t = match self.guard_temps.iter().find(|&&(l, _)| l == local) {
            Some(&(_, t)) => t,
            None => {
                let name = self.p.name(self.ck.locals[local as usize].name).to_string();
                let rt = self.ref_ty(false, value_ty);
                let t = self.new_local(rt, false, Some(name));
                self.guard_temps.push((local, t));
                t
            }
        };
        if !self.scopes.last().unwrap().contains(&t) {
            self.scopes.last_mut().unwrap().push(t);
        }
        self.assign(Place::local(t), Rvalue::Ref(false, place), span);
        self.guard_places[local as usize] = Some(match mode {
            BindMode::Move => Place::local(t).deref(),
            BindMode::Ref(_) => Place::local(t),
        });
        if !bound.contains(&local) {
            bound.push(local);
        }
    }

    /// Binds an already-tested pattern for a match guard, mirroring
    /// `bind_pat` case by case, but by shared reference (see
    /// `guard_binding`). Records every bound checker local in
    /// `bound` so the caller can clear `guard_places` after the
    /// guard. A by-value array middle binding never reaches
    /// here (see `pat_has_slice_middle_move`); a slice middle
    /// reads through a shared subslice temporary.
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
                    self.bind_pat_guard(sub, place.project(Proj::Index(idx)), bound);
                }
                for (j, &sub) in suffix.iter().enumerate() {
                    let back = (suffix.len() - j) as u64;
                    let idx = self.slice_back_index(&place, back, arr_len, span);
                    self.bind_pat_guard(sub, place.project(Proj::Index(idx)), bound);
                }
                // The middle binding reads a shared subslice of
                // the same place for the guard; the real binding
                // makes its own (possibly mutable) one later. A
                // by-value array middle never reaches here (see
                // `pat_has_slice_middle_move`).
                if let Some(mid) = middle
                    && self.pat_has_binding(*mid)
                {
                    let t = self.subslice_temp(&place, prefix.len(), suffix.len(), arr_len, elem, false, span);
                    self.bind_pat_guard(*mid, Place::local(t), bound);
                }
            }
            (Pat::Ref { inner, .. }, _) => self.bind_pat_guard(*inner, place.deref(), bound),
            (Pat::At { inner, .. }, PatRes::Binding { local, mode }) => {
                self.bind_pat_guard(*inner, place.clone(), bound);
                self.guard_binding(local, mode, self.ck.pat_ty(pat), place, span, bound);
            }
            (Pat::Or(alts), _) => {
                // Bind by reference for the alternative that
                // matched: the row's forced alternative, else a
                // switch on the test's tag (see `test_pat`).
                if !self.pat_has_binding(pat) || alts.is_empty() {
                    return;
                }
                if let Some(i) = self.or_forced(pat) {
                    self.bind_pat_guard(alts[i], place, bound);
                    return;
                }
                let alts = alts.clone();
                match self.or_tags.iter().find(|&&(q, _)| q == pat).map(|&(_, l)| l) {
                    Some(tag) => {
                        let end = self.new_block();
                        // The otherwise edge cannot run (a test
                        // set the tag), and must not look like a
                        // path where the bindings stay unassigned.
                        let bad = self.new_block();
                        self.body.blocks[bad.0 as usize].term = Terminator::Unreachable;
                        let branches: Vec<(u32, Bb)> = (0..alts.len()).map(|i| (i as u32, self.new_block())).collect();
                        let b = &mut self.body.blocks[self.cur.0 as usize];
                        b.term = Terminator::Switch(Operand::Copy(Place::local(tag)), branches.clone(), bad);
                        b.term_span = span;
                        for (i, &(_, bb)) in branches.iter().enumerate() {
                            self.cur = bb;
                            self.bind_pat_guard(alts[i], place.clone(), bound);
                            self.goto(end, span);
                        }
                        self.cur = end;
                    }
                    None => {
                        // No test ran (a `let` or parameter bind
                        // reached a guard bind first): try each
                        // alternative, as `bind_pat` does.
                        let end = self.new_block();
                        for &alt in &alts {
                            let next = self.new_block();
                            self.test_pat(alt, place.clone(), next);
                            self.bind_pat_guard(alt, place.clone(), bound);
                            self.goto(end, span);
                            self.cur = next;
                        }
                        self.terminate(Terminator::Unreachable, span);
                        self.cur = end;
                    }
                }
            }
            _ => {}
        }
    }

    /// The bytes of a byte string literal pattern, which the parser
    /// builds as `&[b0, b1, ..]` over `u8` integer literals.
    fn byte_str_bytes(&self, l: ExprId) -> Option<Vec<u8>> {
        let Expr::Ref { mutable: false, raw: false, expr } = self.p.ast.expr(l) else { return None };
        let Expr::Array(elems) = self.p.ast.expr(*expr) else { return None };
        let mut out = Vec::with_capacity(elems.len());
        for &e in elems {
            match self.p.ast.expr(e) {
                Expr::Int(v, Some(crate::lexer::IntSuffix::U8)) => out.push(*v as u8),
                _ => return None,
            }
        }
        Some(out)
    }

    fn lit_operand(&mut self, l: ExprId, ty: Ty) -> Operand {
        match self.p.ast.expr(l) {
            Expr::Unary { expr, .. } => match (self.p.ast.expr(*expr), self.kind(ty)) {
                (Expr::Int(v, _), TyKind::Int(it)) => Operand::Const(Const::Int(v.wrapping_neg(), it)),
                (Expr::Float(i), TyKind::Float(ft)) => {
                    let text = &self.p.ast.strings[*i as usize];
                    // Negation flips only the sign bit, as in rustc:
                    // `-0.0` stays distinct in bits from `0.0`.
                    match crate::check::collect::parse_float_literal_as(text, ft) {
                        Some(bits) => {
                            let sign = match ft {
                                FloatTy::F32 => 1u64 << 31,
                                FloatTy::F64 => 1u64 << 63,
                            };
                            Operand::Const(Const::Float(bits ^ sign, ft))
                        }
                        None => Operand::Const(Const::Unit),
                    }
                }
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
                if let Some(bytes) = self.byte_str_bytes(*l) {
                    // A byte string pattern: `place` holds `&[u8; N]`
                    // or `&[u8]`. A slice needs a length test first;
                    // then each byte must be equal.
                    let base = place.deref();
                    let is_slice = match self.kind(ty) {
                        TyKind::Ref(_, _, inner) => matches!(self.kind(inner), TyKind::Slice(_)),
                        _ => false,
                    };
                    if is_slice {
                        let len = self.temp(USIZE);
                        self.assign(Place::local(len), Rvalue::LenOf(base.clone()), span);
                        branch(
                            self,
                            Rvalue::Bin(
                                BinOp::Eq,
                                Operand::Copy(Place::local(len)),
                                Operand::Const(Const::Int(bytes.len() as u128, IntTy::Usize)),
                            ),
                        );
                    }
                    for (i, b) in bytes.iter().enumerate() {
                        let idx = self.const_usize(i as u64, span);
                        branch(
                            self,
                            Rvalue::Bin(
                                BinOp::Eq,
                                Operand::Copy(base.project(Proj::Index(idx))),
                                Operand::Const(Const::Int(*b as u128, IntTy::U8)),
                            ),
                        );
                    }
                    return;
                }
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
                // One guard row tests only its fixed alternative.
                if let Some(i) = self.or_forced(pat) {
                    self.test_pat(alts[i], place, fail);
                    return;
                }
                let alts = alts.clone();
                // With bindings, remember which alternative
                // matched in a tag: the binding moves happen
                // only after the whole pattern and guard pass,
                // when the merged block no longer knows.
                let tag = if self.pat_has_binding(pat) { Some(self.or_tag(pat)) } else { None };
                let cont = self.new_block();
                for (i, &alt) in alts.iter().enumerate() {
                    let next = self.new_block();
                    self.test_pat(alt, place.clone(), next);
                    if let Some(tag) = tag {
                        self.assign(
                            Place::local(tag),
                            Rvalue::Use(Operand::Const(Const::Int(i as u128, IntTy::U32))),
                            span,
                        );
                    }
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

    /// Binds one checker local from `place` by `mode`. The
    /// first call for a local makes its IR local; later calls
    /// (the other or-pattern alternatives of the same name, the
    /// other guard rows, an unrolled loop's copies) assign into
    /// that same local, and scope membership is per bind site.
    fn bind_one(&mut self, local: u32, mode: BindMode, place: Place, value_ty: Ty, span: Span) {
        let l = match self.bind_reuse.iter().find(|&&(c, _)| c == local) {
            Some(&(_, l)) => l,
            None => {
                let info = &self.ck.locals[local as usize];
                let (ty, m, name) = (info.ty, info.mutable, self.p.name(info.name).to_string());
                let l = self.new_local(ty, m, Some(name));
                self.bind_reuse.push((local, l));
                l
            }
        };
        self.local_map[local as usize] = l;
        let rv = match mode {
            BindMode::Move => Rvalue::Use(self.operand_from(place, value_ty)),
            BindMode::Ref(m) => Rvalue::Ref(m, place),
        };
        self.assign(Place::local(l), rv, span);
        if !self.scopes.last().unwrap().contains(&l) {
            self.scopes.last_mut().unwrap().push(l);
        }
    }

    /// Binds the variables of an already-tested pattern.
    /// rustc's pattern-level check of `x @ sub`, which holds even when the
    /// bindings are never used: a by-move non-Copy `x` cannot have `ref`
    /// bindings in `sub` (L0301), a by-ref `x` cannot have by-move non-Copy
    /// ones (L0311), and `ref mut` conflicts with any other by-ref binding
    /// (L0303). Modes are after default binding modes. A pattern bound
    /// more than once (guard rows) reports once.
    fn check_at_conflicts(&mut self, pat: PatId, inner: PatId, mode: BindMode) {
        let mut subs: Vec<(BindMode, Ty)> = Vec::new();
        let mut stack = vec![inner];
        while let Some(q) = stack.pop() {
            if let PatRes::Binding { mode, .. } = self.ck.pat_res(q)
                && matches!(self.p.ast.pat(q), Pat::Binding { .. } | Pat::At { .. })
            {
                subs.push((mode, self.ck.pat_ty(q)));
            }
            stack.extend(self.pat_children(q));
        }
        let moves = |this: &Self, t: Ty| !is_copy(this.p, &this.body.tys, t);
        let err = match mode {
            BindMode::Move if !moves(self, self.ck.pat_ty(pat)) => None,
            BindMode::Move => subs
                .iter()
                .any(|&(m, _)| m != BindMode::Move)
                .then_some(("L0301", "borrow of moved value: the `@` binding moves the value its subpattern borrows")),
            BindMode::Ref(outer) => {
                if subs.iter().any(|&(m, t)| m == BindMode::Move && moves(self, t)) {
                    Some(("L0311", "cannot move out of a value the `@` binding borrows"))
                } else if subs.iter().any(|&(m, _)| matches!(m, BindMode::Ref(inner) if inner || outer)) {
                    Some(("L0303", "cannot borrow a value as mutable because the `@` pattern also borrows it"))
                } else {
                    None
                }
            }
        };
        let span = self.p.ast.pat_span(pat);
        if let Some((code, msg)) = err
            && !self.body.lower_errs.iter().any(|d| d.span == span && d.code == code)
        {
            let fix = "Bind the parts in the subpattern only, or bind the whole value by `ref` with `ref` parts.";
            self.body.lower_errs.push(crate::diag::Diag::new(code, span, msg, fix));
        }
    }

    fn bind_pat(&mut self, pat: PatId, place: Place) {
        // Or-pattern tags a re-test inside this bind made belong
        // to this one bind: a statically repeated bind of the
        // same pattern (an unrolled loop) tests again.
        let snap = if self.bind_depth == 0 { Some(self.or_tags.len()) } else { None };
        self.bind_depth += 1;
        self.bind_pat_go(pat, place);
        self.bind_depth -= 1;
        if let Some(snap) = snap {
            self.or_tags.truncate(snap);
        }
    }

    fn bind_pat_go(&mut self, pat: PatId, place: Place) {
        let p = self.p;
        let place = Self::derefs(place, self.ck.pat_derefs(pat));
        let span = p.ast.pat_span(pat);
        match (p.ast.pat(pat), self.ck.pat_res(pat)) {
            (Pat::Binding { .. }, PatRes::Binding { local, mode }) => {
                let value_ty = self.ck.pat_ty(pat);
                self.bind_one(local, mode, place, value_ty, span);
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
                        Pat::Binding { .. } | Pat::At { .. } => {
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
                                let mode = match self.ck.pat_res(*mid) {
                                    PatRes::Binding { mode, .. } => mode,
                                    _ => BindMode::Move,
                                };
                                let mutable = mode == BindMode::Ref(true);
                                let t = self.subslice_temp(&place, prefix.len(), suffix.len(), arr_len, elem, mutable, span);
                                self.bind_pat(*mid, Place::local(t));
                            }
                        }
                        _ => {}
                    }
                }
            }
            (Pat::Ref { inner, .. }, _) => self.bind_pat(*inner, place.deref()),
            (Pat::At { inner, .. }, PatRes::Binding { local, mode }) => {
                self.check_at_conflicts(pat, *inner, mode);
                // Subpattern bindings first: copying Copy fields out leaves the
                // whole value movable for the `@` binding, as in Rust. A
                // moving subpattern then makes the whole move an error.
                self.bind_pat(*inner, place.clone());
                let value_ty = self.ck.pat_ty(pat);
                self.bind_one(local, mode, place, value_ty, span);
            }
            (Pat::Or(alts), _) => {
                // Bind the alternative that matched (see
                // `bind_pat_guard` for the same three shapes).
                if !self.pat_has_binding(pat) || alts.is_empty() {
                    return;
                }
                if let Some(i) = self.or_forced(pat) {
                    self.bind_pat(alts[i], place);
                    return;
                }
                let alts = alts.clone();
                match self.or_tags.iter().find(|&&(q, _)| q == pat).map(|&(_, l)| l) {
                    Some(tag) => {
                        let end = self.new_block();
                        // The otherwise edge cannot run (a test
                        // set the tag), and must not look like a
                        // path where the bindings stay unassigned.
                        let bad = self.new_block();
                        self.body.blocks[bad.0 as usize].term = Terminator::Unreachable;
                        let branches: Vec<(u32, Bb)> = (0..alts.len()).map(|i| (i as u32, self.new_block())).collect();
                        let b = &mut self.body.blocks[self.cur.0 as usize];
                        b.term = Terminator::Switch(Operand::Copy(Place::local(tag)), branches.clone(), bad);
                        b.term_span = span;
                        for (i, &(_, bb)) in branches.iter().enumerate() {
                            self.cur = bb;
                            self.bind_pat(alts[i], place.clone());
                            self.goto(end, span);
                        }
                        self.cur = end;
                    }
                    None => {
                        // No test ran before this bind (a plain
                        // `let`, a parameter, a loop binding):
                        // the pattern cannot fail there, so find
                        // the matching alternative now.
                        let end = self.new_block();
                        for &alt in &alts {
                            let next = self.new_block();
                            self.test_pat(alt, place.clone(), next);
                            self.bind_pat(alt, place.clone());
                            self.goto(end, span);
                            self.cur = next;
                        }
                        self.terminate(Terminator::Unreachable, span);
                        self.cur = end;
                    }
                }
            }
            _ => {}
        }
    }

    // ---------- Macros ----------

    /// Format pieces as IR parts. A literal argument rustc inlines into
    /// the format string (`inline_literal`) becomes literal text, merged
    /// with its neighbours, so `format!` capacity and the panic payload
    /// kind match rustc's (W-STD-B).
    fn fmt_parts(&mut self, args: &[ExprId], fmt: &[FmtPiece]) -> Vec<FmtPart> {
        let mut parts: Vec<FmtPart> = Vec::with_capacity(fmt.len());
        let push_lit = |parts: &mut Vec<FmtPart>, text: &str| match parts.last_mut() {
            Some(FmtPart::Lit(prev)) => prev.push_str(text),
            _ => parts.push(FmtPart::Lit(text.to_string())),
        };
        for piece in fmt {
            match piece {
                FmtPiece::Lit(s) => push_lit(&mut parts, s),
                FmtPiece::Arg { index, debug, spec } => {
                    if *spec == FmtSpec::default()
                        && let Some(text) = self.inline_literal(args[*index])
                    {
                        push_lit(&mut parts, &text);
                        continue;
                    }
                    let (value, ty) = self.borrow_of(args[*index], 0);
                    parts.push(FmtPart::Arg { value, ty, debug: *debug, spec: *spec });
                }
            }
        }
        parts
    }

    /// `dst.write_fmt(format_args!(..))` (W-STD-B): a two-phase `&mut`
    /// of the receiver around the borrows of the format arguments, then
    /// one `WriteFmt` rvalue. An argument that borrows the receiver again
    /// is live at the activation, so borrowck rejects it as rustc does.
    fn write_fmt_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], derefs: u8, dest: Option<&Place>, span: Span) {
        let recv_ty = self.peel(self.ty(recv), derefs);
        let pl = self.place_for_mut(recv);
        let pl = Self::derefs(pl, derefs);
        let st = self.ref_ty(false, recv_ty);
        let reserve = self.temp(st);
        self.assign(Place::local(reserve), Rvalue::Ref(false, pl.clone()), span);
        let parts = match args.first().map(|&a| self.p.ast.expr(a)) {
            Some(Expr::Macro { args: fa, fmt, .. }) => self.fmt_parts(fa, fmt),
            _ => Vec::new(),
        };
        self.push(StmtKind::FakeRead(reserve), span);
        let mt = self.ref_ty(true, recv_ty);
        let t = self.temp(mt);
        self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
        let ty = self.ty(e);
        self.set_or_temp(dest, Rvalue::WriteFmt(Operand::Move(Place::local(t)), parts), ty, span);
    }

    /// The text rustc's `format_args!` lowering inlines for a `{}`
    /// argument (`inline_literals`): a string literal, or an integer
    /// literal in range of its type (unsuffixed is `i32`), under any
    /// number of `&`. Other literals (char, bool, float, negative) stay
    /// arguments, as in rustc.
    fn inline_literal(&self, mut e: ExprId) -> Option<String> {
        use crate::lexer::IntSuffix as S;
        while let Expr::Ref { raw: false, expr, .. } = self.p.ast.expr(e) {
            e = *expr;
        }
        match self.p.ast.expr(e) {
            Expr::Str(i) => self.p.ast.strings.get(*i as usize).cloned(),
            Expr::Int(v, suffix) => {
                let max: u128 = match suffix {
                    None | Some(S::I32) => i32::MAX as u128,
                    Some(S::I8) => i8::MAX as u128,
                    Some(S::I16) => i16::MAX as u128,
                    Some(S::I64 | S::Isize) => i64::MAX as u128,
                    Some(S::I128) => i128::MAX as u128,
                    Some(S::U8) => u8::MAX as u128,
                    Some(S::U16) => u16::MAX as u128,
                    Some(S::U32) => u32::MAX as u128,
                    Some(S::U64 | S::Usize) => u64::MAX as u128,
                    Some(S::U128) => u128::MAX,
                };
                (*v <= max).then(|| v.to_string())
            }
            _ => None,
        }
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
            // As a `write_fmt` argument on a Formatter or String it lowers
            // in `write_fmt_into`. Any other `write_fmt` argument (the
            // `io::Write` method, W-SHIM) is an `Arguments` value: its
            // text, formatted here.
            MacroKind::FormatArgs => {
                let parts = self.fmt_parts(args, fmt);
                self.set_or_temp(dest, Rvalue::Format(parts), ty, span);
            }
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
            CV::Int(i) if !self.body.tys.is_exit_code(ty) => {
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
        // `ExitCode::SUCCESS` and `FAILURE` build through `ExitCode::from`.
        if let CV::Int(i) = v
            && self.body.tys.is_exit_code(ty)
        {
            let status = Operand::Const(Const::Int(*i as u128, IntTy::U8));
            self.call_into(CallTarget::Builtin(Builtin::ExitCodeFrom), vec![status], dest.clone(), span);
            return;
        }
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
            // A fn pointer in a const value (W-STD-C): the slot trampoline.
            CV::FnPtr(f) => self.assign(dest.clone(), Rvalue::FnValue(LocalDefId(*f), ty), span),
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

    /// An Adt value built by `e` (`set_or_temp`). Built through a `Self`
    /// path, it has the impl's own lifetimes, as in rustc (W-BORROW):
    /// it goes into a temporary whose regions equal them (a body
    /// annotation), so its fields must outlive them, and then moves on.
    fn aggregate_into(&mut self, e: ExprId, rv: Rvalue, dest: Option<&Place>, ty: Ty, span: Span) {
        match self.self_ctor_regions(e) {
            Some(r) => {
                let t = self.temp(ty);
                self.assign(Place::local(t), rv, span);
                self.body.annotations.push((t, r));
                self.set_or_temp(dest, Rvalue::Use(Operand::Move(Place::local(t))), ty, span);
            }
            None => self.set_or_temp(dest, rv, ty, span),
        }
    }

    /// The impl's regioned `Self` type when `e` builds a value through a
    /// `Self` path (`Self { .. }`, `Self(..)`, `Self::V(..)`, `Self::V`)
    /// and that type has lifetimes. Template and plain bodies only: an
    /// instance's types are concrete, and its template carries the check.
    fn self_ctor_regions(&self, e: ExprId) -> Option<Ty> {
        let p = self.p;
        let head = match p.ast.expr(e) {
            Expr::StructLit { path, .. } | Expr::Path(path) => path.first(),
            Expr::Call { callee, .. } => match p.ast.expr(*callee) {
                Expr::Path(segs) => segs.first(),
                _ => None,
            },
            _ => None,
        }?;
        let fid = self.body.fn_id;
        if head.name != p.known.self_type || self.in_instance(fid) {
            return None;
        }
        let t = p.gx.fn_scopes.get(fid.0 as usize)?.scope.self_ty_regioned?;
        let mut regs = Vec::new();
        crate::borrowck::regions_of(&self.body.tys, t, &mut regs);
        regs.iter().any(|r| matches!(r, Region::Static | Region::Param(_))).then_some(t)
    }

    /// True for a mono instance body, or a closure body fn inside one.
    fn in_instance(&self, fid: LocalDefId) -> bool {
        use crate::check::generics::FnClass;
        let p = self.p;
        match p.gx.fn_class.get(fid.0 as usize) {
            Some(FnClass::Instance) => true,
            Some(FnClass::Closure) => {
                let parent = p.gx.closure_fns.get(&fid).and_then(|d| p.gx.closures.get(d)).map(|c| c.parent);
                parent.is_some_and(|f| f != fid && self.in_instance(f))
            }
            _ => false,
        }
    }
}
