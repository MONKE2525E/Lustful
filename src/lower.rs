// Lowering: checked AST to IR. Makes evaluation order, temporaries, moves, borrows, and drops explicit.
use crate::ast::{self, BinOp, Expr, ExprId, FmtPiece, MacroKind, Pat, PatId, Stmt};
use crate::check::{Autoref, BindMode, Builtin, Checked, Coerce, PatRes, Res};
use crate::collect::*;
use crate::diag::Span;
use crate::ir::*;
use crate::types::*;

struct LoopInfo {
    break_bb: Bb,
    continue_bb: Bb,
    dest: Option<Place>,
    depth: usize,
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
}

/// Lowers one checked function body to IR.
pub fn lower<'p, 'a>(p: &'p Program<'a>, fid: FnId, mut ck: Checked<'p>) -> Body<'p> {
    let f = p.fn_info(fid);
    let tys = std::mem::replace(&mut ck.tys, Tys::new(&p.tys));
    let entry = BlockData { stmts: Vec::new(), term: Terminator::Unreachable, term_span: Span::default() };
    let body = Body { fn_id: fid, tys, locals: Vec::new(), blocks: vec![entry], arg_count: f.params.len() };
    let mut lw = Lower { p, ck, body, cur: Bb(0), scopes: vec![Vec::new()], loops: Vec::new(), local_map: Vec::new() };
    lw.new_local(f.ret, true, None);
    lw.local_map = vec![u32::MAX; lw.ck.locals.len()];
    for i in 0..lw.ck.param_locals.len() {
        let cl = lw.ck.param_locals[i];
        let info = &lw.ck.locals[cl as usize];
        let (ty, m, name) = (info.ty, info.mutable, p.name(info.name).to_string());
        let l = lw.new_local(ty, m, Some(name));
        lw.local_map[cl as usize] = l;
        lw.scopes[0].push(l);
    }
    let span = p.ast.block(f.def.body).span;
    lw.block_into(f.def.body, Some(&Place::local(0)));
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
            if needs_drop(self.p, &self.body.tys, self.body.locals[l as usize].ty) {
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
        self.body.tys.intern(TyKind::Ref(m, t))
    }
    fn peel(&self, mut t: Ty, n: u8) -> Ty {
        for _ in 0..n {
            if let TyKind::Ref(_, inner) = self.kind(t) {
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
            Expr::Field { .. } | Expr::Index { .. } | Expr::Deref(_) => true,
            _ => false,
        }
    }

    /// Evaluates `e` to a place. A value expression goes into a new temporary.
    fn place(&mut self, e: ExprId) -> Place {
        match (self.p.ast.expr(e), self.ck.res(e)) {
            (Expr::Path(_) | Expr::SelfValue, Res::Local(l)) => Place::local(self.local_map[l as usize]),
            (Expr::Field { base, .. }, Res::Field { derefs, index }) => {
                let b = self.place(*base);
                Self::derefs(b, derefs).project(Proj::Field(index))
            }
            (Expr::Index { base, index }, Res::Index { derefs }) => {
                let b = self.place(*base);
                let b = Self::derefs(b, derefs);
                let i = self.temp(USIZE);
                self.expr_into(*index, Some(&Place::local(i)));
                b.project(Proj::Index(i))
            }
            (Expr::Deref(inner), _) => self.place(*inner).deref(),
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
                // `&String` (possibly `&&String`) to `&str`.
                let mut place = self.op_place(op, ty, span);
                let mut t = ty;
                while let TyKind::Ref(_, inner) = self.kind(t) {
                    if self.kind(inner) == TyKind::String {
                        break;
                    }
                    place = place.deref();
                    t = inner;
                }
                let tmp = self.temp(REF_STR);
                self.assign(Place::local(tmp), Rvalue::Builtin(Builtin::StringAsStr, vec![Operand::Copy(place)]), span);
                Operand::Copy(Place::local(tmp))
            }
            Coerce::Deref(n) => {
                let place = self.op_place(op, ty, span);
                Operand::Copy(Self::derefs(place, n))
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
        }
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
            Expr::Bool(b) => Operand::Const(Const::Bool(*b)),
            Expr::Char(c) => Operand::Const(Const::Char(*c)),
            Expr::Str(s) => Operand::Const(Const::Str(*s)),
            Expr::Unit => Operand::Const(Const::Unit),
            _ if self.is_place_expr(e) => {
                let p = self.place(e);
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
        match p.ast.expr(e) {
            Expr::Int(..) | Expr::Bool(_) | Expr::Char(_) | Expr::Str(_) | Expr::Unit => {
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
                Res::Variant(a, v) => self.set_or_temp(dest, Rvalue::Aggregate(a, v, Vec::new()), ty, span),
                Res::OptNone => self.set_or_temp(dest, Rvalue::Opt(ty, None), ty, span),
                _ => {}
            },
            Expr::Field { .. } | Expr::Index { .. } | Expr::Deref(_) => {
                let pl = self.place(e);
                if let Some(d) = dest {
                    let op = self.operand_from(pl, ty);
                    self.assign(d.clone(), Rvalue::Use(op), span);
                }
            }
            Expr::Block(b) => self.block_into(*b, dest),
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
            Expr::While { cond, body } => {
                let (head, bodyb, exit) = (self.new_block(), self.new_block(), self.new_block());
                self.goto(head, span);
                let cl = self.cond(*cond, span);
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::If(Operand::Copy(Place::local(cl)), bodyb, exit);
                b.term_span = span;
                self.cur = bodyb;
                self.loops.push(LoopInfo { break_bb: exit, continue_bb: head, dest: None, depth: self.scopes.len() });
                self.block_into(*body, None);
                self.loops.pop();
                self.goto(head, span);
                self.cur = exit;
                if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Use(Operand::Const(Const::Unit)), span);
                }
            }
            Expr::Loop { body } => {
                let (head, exit) = (self.new_block(), self.new_block());
                self.goto(head, span);
                self.loops.push(LoopInfo { break_bb: exit, continue_bb: head, dest: dest.cloned(), depth: self.scopes.len() });
                self.block_into(*body, None);
                self.loops.pop();
                self.goto(head, span);
                self.cur = exit;
            }
            Expr::For { pat, iter, body } => self.for_loop(*pat, *iter, *body, span, dest),
            Expr::Match { scrut, arms } => self.match_into(*scrut, arms, dest, span),
            Expr::Call { args, .. } => {
                let res = self.ck.res(e);
                let ops: Vec<Operand> = args.iter().map(|&a| self.operand(a)).collect();
                let rv = match res {
                    Res::Fn(f) => Rvalue::Call(f, ops),
                    Res::Variant(a, v) => Rvalue::Aggregate(a, v, ops),
                    Res::OptSome => Rvalue::Opt(ty, ops.into_iter().next()),
                    Res::Builtin(b) => match b {
                        Builtin::VecNew | Builtin::VecWithCapacity => Rvalue::VecLit(self.peel_vec(ty), Vec::new()),
                        _ => Rvalue::Builtin(b, ops),
                    },
                    _ => return,
                };
                match dest {
                    Some(d) => self.assign(d.clone(), rv, span),
                    None => {
                        let t = self.temp(ty);
                        self.assign(Place::local(t), rv, span);
                    }
                }
            }
            Expr::MethodCall { recv, args, .. } => self.method_into(e, *recv, args, dest, span),
            Expr::Binary { op, lhs, rhs } => self.binary_into(e, *op, *lhs, *rhs, dest, span),
            Expr::Unary { op, expr } => {
                let o = self.operand(*expr);
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
                    self.assign(d.clone(), Rvalue::Cast(o, ty), span);
                }
            }
            Expr::Ref { mutable, expr } => {
                let pl = self.place(*expr);
                if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Ref(*mutable, pl), span);
                }
            }
            Expr::Assign { lhs, rhs } => {
                let o = self.operand(*rhs);
                let pl = self.place(*lhs);
                self.assign(pl, Rvalue::Use(o), span);
                self.unit(dest, span);
            }
            Expr::AssignOp { op, lhs, rhs } => {
                let lt = self.ty(*lhs);
                if self.kind(lt) == TyKind::String {
                    let pl = self.place(*lhs);
                    let r = self.operand(*rhs);
                    let mt = self.ref_ty(true, STRING);
                    let t = self.temp(mt);
                    self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
                    let u = self.temp(UNIT);
                    self.assign(Place::local(u), Rvalue::Builtin(Builtin::StringPushStr, vec![Operand::Move(Place::local(t)), r]), span);
                } else {
                    let rd = match self.ck.res(e) {
                        Res::Bin { rd, .. } => rd,
                        _ => 0,
                    };
                    let r = self.operand_derefs(*rhs, rd);
                    let pl = self.place(*lhs);
                    self.assign(pl.clone(), Rvalue::Bin(*op, Operand::Copy(pl), r), span);
                }
                self.unit(dest, span);
            }
            Expr::StructLit { fields, .. } => {
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
                            let ft = self.ty(fe);
                            let ft = if self.ck.coerce(fe) == Coerce::StrFromString { REF_STR } else { ft };
                            let t = self.temp(ft);
                            self.assign(Place::local(t), Rvalue::Use(o), span);
                            self.operand_from(Place::local(t), ft)
                        }
                    };
                    ops[i] = Some(o);
                }
                let ops = ops.into_iter().map(|o| o.unwrap()).collect();
                self.set_or_temp(dest, Rvalue::Aggregate(a, v, ops), ty, span);
            }
            Expr::Range { .. } => {}
            Expr::Break(val) => {
                let li = self.loops.last().unwrap();
                let (bb, depth, ld) = (li.break_bb, li.depth, li.dest.clone());
                if let Some(v) = val {
                    self.expr_into(*v, ld.as_ref());
                }
                self.exit_to(depth, span);
                self.terminate(Terminator::Goto(bb), span);
            }
            Expr::Continue => {
                let li = self.loops.last().unwrap();
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
            Expr::Macro { kind, args, fmt, repeat } => self.macro_into(e, *kind, args, fmt, *repeat, dest, ty, span),
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
        match self.kind(t) {
            TyKind::Vec(e) => e,
            _ => ERROR,
        }
    }

    // ---------- Blocks ----------

    fn block_into(&mut self, b: ast::BlockId, dest: Option<&Place>) {
        let block = self.p.ast.block(b);
        self.scopes.push(Vec::new());
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let { pat, init, span, .. } => self.let_stmt(*pat, *init, *span),
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
                            if let Expr::Ref { mutable, expr } = p.ast.expr(init)
                                && self.ck.coerce(init) == Coerce::None
                                && !self.is_place_expr(*expr)
                            {
                                let t = self.ty(*expr);
                                let tmp = self.new_local(t, true, None);
                                let n = self.scopes.len();
                                self.scopes[n - 2].push(tmp);
                                self.expr_into(*expr, Some(&Place::local(tmp)));
                                self.assign(Place::local(l), Rvalue::Ref(*mutable, Place::local(tmp)), span);
                                self.pop_scope(span);
                                self.scopes.last_mut().unwrap().push(l);
                                return;
                            }
                            self.expr_into(init, Some(&Place::local(l)));
                        }
                        BindMode::Ref(m) => {
                            let pl = self.place(init);
                            self.assign(Place::local(l), Rvalue::Ref(m, pl), span);
                        }
                    }
                    self.pop_scope(span);
                }
                self.scopes.last_mut().unwrap().push(l);
            }
            (Pat::Wild, _) => {
                if let Some(init) = init {
                    // `let _ = place;` does not move the place.
                    self.scopes.push(Vec::new());
                    if self.is_place_expr(init) {
                        self.place(init);
                    } else {
                        self.expr_into(init, None);
                    }
                    self.pop_scope(span);
                }
            }
            _ => {}
        }
    }

    // ---------- Calls ----------

    fn method_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], dest: Option<&Place>, span: Span) {
        let (callee, derefs, autoref) = match self.ck.res(e) {
            Res::Method { f, derefs, autoref } => (Ok(f), derefs, autoref),
            Res::BuiltinMethod { b, derefs, autoref } => (Err(b), derefs, autoref),
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
                // Two-phase borrow: a shared reservation while the arguments run, then `&mut`.
                let pl = self.place(recv);
                let pl = Self::derefs(pl, derefs);
                let st = self.ref_ty(false, recv_ty);
                let reserve = self.temp(st);
                self.assign(Place::local(reserve), Rvalue::Ref(false, pl.clone()), span);
                let mut arg_ops = Vec::new();
                for &a in args {
                    let o = self.operand(a);
                    arg_ops.push(o);
                }
                self.push(StmtKind::FakeRead(reserve), span);
                let mt = self.ref_ty(true, recv_ty);
                let t = self.temp(mt);
                self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
                ops.push(Operand::Move(Place::local(t)));
                ops.extend(arg_ops);
            }
        }
        let rv = match callee {
            Ok(f) => Rvalue::Call(f, ops),
            Err(b) => Rvalue::Builtin(b, ops),
        };
        match dest {
            Some(d) => self.assign(d.clone(), rv, span),
            None => {
                let t = self.temp(self.ty(e));
                self.assign(Place::local(t), rv, span);
            }
        }
    }

    fn binary_into(&mut self, e: ExprId, op: BinOp, lhs: ExprId, rhs: ExprId, dest: Option<&Place>, span: Span) {
        let ty = self.ty(e);
        let out = match dest {
            Some(d) => d.clone(),
            None => Place::local(self.temp(ty)),
        };
        if matches!(op, BinOp::And | BinOp::Or) {
            // Short circuit.
            self.expr_into(lhs, Some(&out));
            let (rhs_bb, end) = (self.new_block(), self.new_block());
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = if op == BinOp::And {
                Terminator::If(Operand::Copy(out.clone()), rhs_bb, end)
            } else {
                Terminator::If(Operand::Copy(out.clone()), end, rhs_bb)
            };
            b.term_span = span;
            self.cur = rhs_bb;
            self.scopes.push(Vec::new());
            self.expr_into(rhs, Some(&out));
            self.pop_scope(span);
            self.goto(end, span);
            return;
        }
        let (ld, rd) = match self.ck.res(e) {
            Res::Bin { ld, rd } => (ld, rd),
            _ => (0, 0),
        };
        let lt = self.ty(lhs);
        let base = self.peel(lt, ld);
        let rv = if op.is_cmp() {
            match self.kind(base) {
                TyKind::Int(_) | TyKind::Bool | TyKind::Char => {
                    let a = self.operand_derefs(lhs, ld);
                    let b = self.operand_derefs(rhs, rd);
                    Rvalue::Bin(op, a, b)
                }
                TyKind::String | TyKind::Str => {
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
        } else if self.kind(lt) == TyKind::String {
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

    /// A `&str` view of a String or str value reached through `n` references.
    fn str_view(&mut self, e: ExprId, n: u8) -> Operand {
        let span = self.span(e);
        let base = self.peel(self.ty(e), n);
        if self.kind(base) == TyKind::Str {
            let p = self.place(e);
            return Operand::Copy(Self::derefs(p, n - 1));
        }
        let (r, _) = self.borrow_of(e, n);
        let t = self.temp(REF_STR);
        self.assign(Place::local(t), Rvalue::Builtin(Builtin::StringAsStr, vec![r]), span);
        Operand::Copy(Place::local(t))
    }

    // ---------- Loops ----------

    fn for_loop(&mut self, pat: PatId, iter: ExprId, body: ast::BlockId, span: Span, dest: Option<&Place>) {
        let p = self.p;
        self.scopes.push(Vec::new());
        let item_ty = self.ck.pat_ty(pat);
        let (head, bodyb, exit) = (self.new_block(), self.new_block(), self.new_block());
        // `next` computes the loop variable into this local at the top of each iteration.
        let item = self.temp(item_ty);
        if let Expr::Range { lo, hi, inclusive } = p.ast.expr(iter) {
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
        } else if self.kind(self.ty(iter)) == TyKind::Chars {
            // `for c in s.chars()`: call `next` until it returns None.
            let it = self.temp(self.ty(iter));
            self.expr_into(iter, Some(&Place::local(it)));
            self.goto(head, span);
            let mt = self.ref_ty(true, self.ty(iter));
            let r = self.temp(mt);
            self.assign(Place::local(r), Rvalue::Ref(true, Place::local(it)), span);
            let ot = self.body.tys.intern(TyKind::Option(CHAR));
            let nx = self.temp(ot);
            self.assign(Place::local(nx), Rvalue::Builtin(Builtin::CharsNext, vec![Operand::Move(Place::local(r))]), span);
            let d = self.temp(int(IntTy::U32));
            self.assign(Place::local(d), Rvalue::Discriminant(Place::local(nx)), span);
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(1, bodyb)], exit);
            self.cur = bodyb;
            let c = Place::local(nx).project(Proj::Downcast(1)).project(Proj::Field(0));
            self.assign(Place::local(item), Rvalue::Use(Operand::Copy(c)), span);
        } else {
            // `for x in &v` / `&mut v`: index loop over a reference held for the whole loop.
            let it_ty = self.ty(iter);
            let m = matches!(self.kind(it_ty), TyKind::Ref(true, _));
            let vref = self.temp(it_ty);
            self.expr_into(iter, Some(&Place::local(vref)));
            let shared = self.ref_ty(false, self.peel(it_ty, 1));
            let sref = self.temp(shared);
            self.assign(Place::local(sref), Rvalue::Ref(false, Place::local(vref).deref()), span);
            let len = self.temp(USIZE);
            self.assign(Place::local(len), Rvalue::Builtin(Builtin::VecLen, vec![Operand::Copy(Place::local(sref))]), span);
            let idx = self.temp(USIZE);
            self.assign(Place::local(idx), Rvalue::Use(Operand::Const(Const::Int(0, IntTy::Usize))), span);
            self.goto(head, span);
            let c = self.temp(BOOL);
            self.assign(Place::local(c), Rvalue::Bin(BinOp::Lt, Operand::Copy(Place::local(idx)), Operand::Copy(Place::local(len))), span);
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), bodyb, exit);
            self.cur = bodyb;
            let elem = Place::local(vref).deref().project(Proj::Index(idx));
            self.assign(Place::local(item), Rvalue::Ref(m, elem), span);
            self.assign(
                Place::local(idx),
                Rvalue::Bin(BinOp::Add, Operand::Copy(Place::local(idx)), Operand::Const(Const::Int(1, IntTy::Usize))),
                span,
            );
        }
        self.scopes.push(Vec::new());
        self.bind_pat(pat, Place::local(item));
        self.loops.push(LoopInfo { break_bb: exit, continue_bb: head, dest: None, depth: self.scopes.len() - 1 });
        self.block_into(body, None);
        self.loops.pop();
        self.pop_scope(span);
        self.goto(head, span);
        self.cur = exit;
        self.pop_scope(span);
        self.unit(dest, span);
    }

    // ---------- Match ----------

    fn match_into(&mut self, scrut: ExprId, arms: &[ast::Arm], dest: Option<&Place>, span: Span) {
        // Temporaries in the scrutinee live until the end of the match.
        self.scopes.push(Vec::new());
        let sp = self.place(scrut);
        let end = self.new_block();
        for arm in arms {
            let next = self.new_block();
            self.test_pat(arm.pat, sp.clone(), next);
            self.scopes.push(Vec::new());
            self.bind_pat(arm.pat, sp.clone());
            if let Some(g) = arm.guard {
                let gspan = self.span(g);
                self.scopes.push(Vec::new());
                let c = self.operand(g);
                let cl = self.new_local(BOOL, false, None);
                self.assign(Place::local(cl), Rvalue::Use(c), gspan);
                self.pop_scope(gspan);
                let (ok, fail) = (self.new_block(), self.new_block());
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::If(Operand::Copy(Place::local(cl)), ok, fail);
                self.cur = fail;
                let arm_locals = self.scopes.last().unwrap().clone();
                self.emit_drops(&arm_locals, gspan);
                self.goto(next, gspan);
                self.cur = ok;
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

    fn lit_operand(&mut self, l: ExprId, ty: Ty) -> Operand {
        match self.p.ast.expr(l) {
            Expr::Unary { expr, .. } => match (self.p.ast.expr(*expr), self.kind(ty)) {
                (Expr::Int(v, _), TyKind::Int(it)) => Operand::Const(Const::Int((*v as i64).wrapping_neg() as u64, it)),
                _ => Operand::Const(Const::Unit),
            },
            Expr::Int(v, _) => match self.kind(ty) {
                TyKind::Int(it) => Operand::Const(Const::Int(*v, it)),
                _ => Operand::Const(Const::Int(*v, IntTy::I32)),
            },
            Expr::Bool(b) => Operand::Const(Const::Bool(*b)),
            Expr::Char(c) => Operand::Const(Const::Char(*c)),
            Expr::Str(s) => Operand::Const(Const::Str(*s)),
            _ => Operand::Const(Const::Unit),
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
            Pat::Range { lo, hi } => {
                let (a, b) = (self.lit_operand(*lo, ty), self.lit_operand(*hi, ty));
                branch(self, Rvalue::Bin(BinOp::Ge, Operand::Copy(place.clone()), a));
                branch(self, Rvalue::Bin(BinOp::Le, Operand::Copy(place), b));
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
        }
    }

    /// Sub-patterns of a struct or variant pattern, with their field indexes.
    fn sub_pats(&self, pat: PatId, a: AdtId, v: u32) -> Vec<(u32, PatId)> {
        let p = self.p;
        match p.ast.pat(pat) {
            Pat::TupleStruct { elems, .. } => elems.iter().enumerate().map(|(i, &s)| (i as u32, s)).collect(),
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
            (Pat::TupleStruct { .. } | Pat::Struct { .. }, PatRes::Variant(a, v)) => {
                let base = if p.adt(a).is_enum { place.project(Proj::Downcast(v)) } else { place };
                for (i, sub) in self.sub_pats(pat, a, v) {
                    self.bind_pat(sub, base.project(Proj::Field(i)));
                }
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
                FmtPiece::Arg { index, debug } => {
                    let (value, ty) = self.borrow_of(args[*index], 0);
                    parts.push(FmtPart::Arg { value, ty, debug: *debug });
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
                parts.push(FmtPart::Arg { value: a, ty: t, debug: true });
                parts.push(FmtPart::Lit("\n right: ".into()));
                parts.push(FmtPart::Arg { value: b, ty: tb, debug: true });
                self.terminate(Terminator::Panic(parts), span);
                self.cur = ok;
                self.unit(dest, span);
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
