// Expansion of the iterator builtins into plain IR (W-STD-A phase 3,
// ty/iter.rs).
//
// Check and borrowck see each iterator method as one builtin call
// (check/iter.rs). Codegen calls `expand` first, so every such call
// becomes ordinary IR: closure body calls, switches on `Option`, slice
// places, and explicit drops, with Rust 1.99's semantics per kind (pull
// order, early exits, drop points, `size_hint`, and `collect`'s
// capacity rules). It runs after borrowck on purpose: borrowck checks
// the call's summary (its args and result), which covers everything
// the expansion does, and the places the expansion makes are not user
// borrows.
//
// Every `emit_*` function starts in `self.cur` and leaves `self.cur`
// at the block that follows the value it wrote.
use crate::check::Builtin;
use crate::check::closure::ClosureKind;
use crate::check::collect::{Program, is_copy};
use crate::diag::Span;
use crate::ir::*;
use crate::ty::iter::{self as it, IterKind};
use crate::ty::*;

type R = Result<(), String>;

/// True for the builtins this pass rewrites. `IterVecIntoIter` and
/// the `vec::IntoIter` element moves stay calls: codegen emits them.
fn expands(b: Builtin) -> bool {
    use Builtin as B;
    matches!(
        b,
        B::IterIter
            | B::IterIterMut
            | B::IterNext
            | B::IterMap
            | B::IterFilter
            | B::IterFilterMap
            | B::IterEnumerate
            | B::IterRev
            | B::IterTake
            | B::IterSkip
            | B::IterStepBy
            | B::IterChain
            | B::IterZip
            | B::IterCopied
            | B::IterCloned
            | B::IterTakeWhile
            | B::IterSkipWhile
            | B::IterPeekable
            | B::IterPeek
            | B::IterInspect
            | B::IterCount
            | B::IterLast
            | B::IterNth
            | B::IterAny
            | B::IterAll
            | B::IterFind
            | B::IterFindMap
            | B::IterPosition
            | B::IterFold
            | B::IterForEach
            | B::IterMin
            | B::IterMax
            | B::IterMinByKey
            | B::IterMaxByKey
            | B::IterCollect
            | B::IterSum
            | B::IterProduct
    )
}

/// The body with every iterator builtin call expanded, or None when it
/// has none (the common case: no copy is made).
pub fn expand<'g>(p: &Program, body: &Body<'g>) -> Result<Option<Body<'g>>, String> {
    let has = body.blocks.iter().any(|b| matches!(b.term, Terminator::Call { target: CallTarget::Builtin(x), .. } if expands(x)));
    if !has {
        return Ok(None);
    }
    let copy = Body {
        fn_id: body.fn_id,
        tys: body.tys.clone(),
        locals: body.locals.clone(),
        blocks: body.blocks.clone(),
        arg_count: body.arg_count,
        reads: Default::default(),
        lower_errs: Vec::new(),
        annotations: Vec::new(),
        promoted: Vec::new(),
    };
    let mut ex = Ex { p, body: copy, cur: Bb(0), span: Span::default() };
    let n = ex.body.blocks.len();
    for b in 0..n {
        let Terminator::Call { target: CallTarget::Builtin(x), .. } = ex.body.blocks[b].term else { continue };
        if !expands(x) {
            continue;
        }
        let term = std::mem::replace(&mut ex.body.blocks[b].term, Terminator::Unreachable);
        let Terminator::Call { args, dest, next, .. } = term else { unreachable!() };
        ex.cur = Bb(b as u32);
        ex.span = ex.body.blocks[b].term_span;
        ex.builtin(x, args, dest)?;
        ex.goto(next);
    }
    Ok(Some(ex.body))
}

struct Ex<'b, 'p, 'g> {
    p: &'b Program<'p>,
    body: Body<'g>,
    cur: Bb,
    span: Span,
}

impl Ex<'_, '_, '_> {
    // ---------- IR building ----------

    fn local(&mut self, ty: Ty) -> Local {
        self.body.locals.push(LocalDecl { ty, mutable: true, name: None });
        self.body.locals.len() as Local - 1
    }
    fn block(&mut self) -> Bb {
        self.body.blocks.push(BlockData { stmts: Vec::new(), term: Terminator::Unreachable, term_span: self.span });
        Bb(self.body.blocks.len() as u32 - 1)
    }
    fn push(&mut self, kind: StmtKind) {
        let span = self.span;
        self.body.blocks[self.cur.0 as usize].stmts.push(Stmt { kind, span });
    }
    fn assign(&mut self, pl: Place, rv: Rvalue) {
        self.push(StmtKind::Assign(pl, rv));
    }
    fn drop_local(&mut self, l: Local) {
        self.push(StmtKind::Drop(l));
    }
    fn term(&mut self, t: Terminator) {
        let b = &mut self.body.blocks[self.cur.0 as usize];
        b.term = t;
        b.term_span = self.span;
    }
    fn goto(&mut self, b: Bb) {
        self.term(Terminator::Goto(b));
    }
    /// Ends the current block with a call and continues after it.
    fn call(&mut self, target: CallTarget, args: Vec<Operand>, dest: Place) {
        let next = self.block();
        self.term(Terminator::Call { target, args, dest, next, unwind: None });
        self.cur = next;
    }
    fn call_builtin(&mut self, b: Builtin, args: Vec<Operand>, dest: Place) {
        self.call(CallTarget::Builtin(b), args, dest);
    }
    /// Ends the current block on a bool and returns (then, else).
    fn branch(&mut self, cond: Operand) -> (Bb, Bb) {
        let (t, f) = (self.block(), self.block());
        self.term(Terminator::If(cond, t, f));
        (t, f)
    }
    /// Ends the current block on an `Option` place: (some, none).
    fn switch_opt(&mut self, opt: &Place) -> (Bb, Bb) {
        let d = self.local(int(IntTy::U32));
        self.assign(Place::local(d), Rvalue::Discriminant(opt.clone()));
        let (s, n) = (self.block(), self.block());
        self.term(Terminator::Switch(Operand::Copy(Place::local(d)), vec![(1, s)], n));
        (s, n)
    }
    fn payload(opt: &Place) -> Place {
        opt.project(Proj::Downcast(1)).project(Proj::Field(0))
    }
    fn usize_c(n: u64) -> Operand {
        Operand::Const(Const::Int(n as u128, IntTy::Usize))
    }
    /// A copy or a move of a place, by its type.
    fn take(&self, pl: Place, ty: Ty) -> Operand {
        if is_copy(self.p, &self.body.tys, ty) { Operand::Copy(pl) } else { Operand::Move(pl) }
    }
    /// A new bool local holding `a op b`.
    fn cmp(&mut self, op: crate::ast::BinOp, a: Operand, b: Operand) -> Operand {
        let c = self.local(BOOL);
        self.assign(Place::local(c), Rvalue::Bin(op, a, b));
        Operand::Copy(Place::local(c))
    }
    /// A new reference local to a place.
    fn ref_to(&mut self, mutable: bool, pl: Place, ty: Ty) -> Local {
        let rt = self.body.tys.mk_ref(mutable, ty);
        let r = self.local(rt);
        self.assign(Place::local(r), Rvalue::Ref(mutable, pl));
        r
    }
    fn some(&mut self, dest: &Place, opt_ty: Ty, v: Operand) {
        self.assign(dest.clone(), Rvalue::Opt(opt_ty, Some(v)));
    }
    fn none(&mut self, dest: &Place, opt_ty: Ty) {
        self.assign(dest.clone(), Rvalue::Opt(opt_ty, None));
    }
    fn tuple_ty(&mut self, ts: &[Ty]) -> Ty {
        let id = self.body.tys.intern_tys(ts);
        self.body.tys.intern(TyKind::Tuple(id))
    }

    // ---------- Types ----------

    fn place_ty(&mut self, pl: &Place) -> Result<Ty, String> {
        let mut t = self.body.locals[pl.local as usize].ty;
        let mut variant: Option<u32> = None;
        for pr in &pl.proj {
            let tys = &mut self.body.tys;
            t = match *pr {
                Proj::Deref => match tys.kind(t) {
                    TyKind::Ref(_, _, i) => i,
                    _ => tys.smart_elem(t).ok_or("iterator expansion: deref of a non-pointer place")?,
                },
                Proj::Downcast(v) => {
                    variant = Some(v);
                    continue;
                }
                Proj::Field(i) => {
                    let v = variant.take();
                    if let Some(e) = tys.option_elem(t) {
                        e
                    } else if let Some((a, b)) = tys.result_args(t) {
                        if v == Some(1) { b } else { a }
                    } else if let TyKind::Tuple(ts) = tys.kind(t) {
                        tys.tys_of(ts)[i as usize]
                    } else if let Some(fs) = it::field_tys(tys, t) {
                        fs[i as usize]
                    } else if let TyKind::Closure(_, a) = tys.kind(t) {
                        crate::check::collect::closure_fields(tys, a)[i as usize]
                    } else if let Some(a) = tys.local_adt(t) {
                        self.p.adt(a).variants[v.unwrap_or(0) as usize].fields[i as usize].ty
                    } else {
                        return Err("iterator expansion: field of an unknown place type".into());
                    }
                }
                Proj::Index(_) => match tys.kind(t) {
                    TyKind::Slice(e) | TyKind::Array(e, _) => e,
                    _ => tys.vec_elem(t).ok_or("iterator expansion: index of a non-sequence place")?,
                },
            };
        }
        Ok(t)
    }

    fn op_ty(&mut self, o: &Operand) -> Result<Ty, String> {
        match o {
            Operand::Copy(pl) | Operand::Move(pl) => self.place_ty(pl),
            Operand::Const(Const::Int(_, i)) => Ok(int(*i)),
            Operand::Const(Const::Bool(_)) => Ok(BOOL),
            Operand::Const(Const::Char(_)) => Ok(CHAR),
            Operand::Const(Const::Unit) => Ok(UNIT),
            Operand::Const(_) => Err("iterator expansion: unexpected constant operand".into()),
        }
    }

    fn item(&mut self, ty: Ty) -> Result<Ty, String> {
        it::item_ty(&mut self.body.tys, ty).ok_or_else(|| "iterator expansion: no item type".into())
    }

    fn kind_args(&self, ty: Ty) -> Option<(IterKind, Vec<Ty>)> {
        it::iter_parts(&self.body.tys, ty)
    }

    /// The place an operand names, moved into a fresh local first when
    /// it is a constant (no iterator is).
    fn op_place(&mut self, o: Operand, ty: Ty) -> Place {
        match o {
            Operand::Copy(pl) | Operand::Move(pl) => pl,
            c => {
                let l = self.local(ty);
                self.assign(Place::local(l), Rvalue::Use(c));
                Place::local(l)
            }
        }
    }

    // ---------- Callables ----------

    /// `dest = f(args..)` for the closure value at `f_place` (type
    /// `f_ty`), called through `FnMut`: the env goes by `&` for an
    /// `Fn` closure and by `&mut` for an `FnMut` one.
    fn call_fn(&mut self, f_ty: Ty, f_place: Place, args: Vec<Operand>, dest: Place) -> R {
        // A fn pointer, fn item, or tuple constructor (W-CHECK-G): a plain
        // call, as `Ctx::callable_res` resolves a call of the value.
        match self.body.tys.kind(f_ty) {
            TyKind::FnPtr(_) => {
                let l = self.local(f_ty);
                self.assign(Place::local(l), Rvalue::Use(Operand::Copy(f_place)));
                self.call(CallTarget::Indirect(l), args, dest);
                return Ok(());
            }
            TyKind::FnDef(def, fargs) => {
                if let Some(a) = self.p.adt_by_def(def) {
                    let v = match self.body.tys.args(fargs).first() {
                        Some(GenericArg::Const(c)) => match self.body.tys.const_kind(*c) {
                            ConstKind::Int(v) => v as u32,
                            _ => 0,
                        },
                        _ => 0,
                    };
                    // A generic Adt builds its mono instance (the dest's type).
                    let a = self.place_ty(&dest).ok().and_then(|t| self.body.tys.local_adt(t)).unwrap_or(a);
                    self.assign(dest, Rvalue::Aggregate(a, v, args));
                    return Ok(());
                }
                let f = self.p.local_def(def.hash).ok_or("iterator expansion: fn item not found")?;
                let gargs: Vec<GenericArg> = self.body.tys.args(fargs).to_vec();
                let f = if gargs.is_empty() {
                    f
                } else {
                    crate::check::generics::instance_for(self.p, &self.body.tys, f, &gargs)
                        .ok_or("iterator expansion: no instance of the fn item")?
                };
                self.call(CallTarget::Fn(f), args, dest);
                return Ok(());
            }
            _ => {}
        }
        let TyKind::Closure(def, _) = self.body.tys.kind(f_ty) else {
            return Err("iterator expansion: the callable is not a closure".into());
        };
        let Some(entry) = self.p.gx.closures.get(&def) else {
            return Err("iterator expansion: closure body not registered".into());
        };
        let (body_fn, kind) = (entry.body_fn, entry.kind);
        let env = match kind {
            ClosureKind::Fn => self.ref_to(false, f_place, f_ty),
            ClosureKind::FnMut => self.ref_to(true, f_place, f_ty),
            ClosureKind::FnOnce => return Err("iterator expansion: an FnOnce closure behind an FnMut bound".into()),
        };
        let mut ops = vec![Operand::Move(Place::local(env))];
        ops.extend(args);
        self.call(CallTarget::Fn(body_fn), ops, dest);
        Ok(())
    }

    // ---------- Builtin calls ----------

    fn builtin(&mut self, b: Builtin, args: Vec<Operand>, dest: Place) -> R {
        use Builtin as B;
        let dest_ty = self.place_ty(&dest)?;
        let mut args = args.into_iter();
        let mut arg = || args.next().ok_or_else(|| "iterator expansion: missing argument".to_string());
        match b {
            B::IterIter | B::IterIterMut => {
                let r = arg()?;
                let rt = self.op_ty(&r)?;
                let rp = self.op_place(r, rt);
                let fields = it::field_tys(&mut self.body.tys, dest_ty).ok_or("iterator expansion: bad slice iterator")?;
                let s = self.local(fields[0]);
                self.assign(Place::local(s), Rvalue::SliceOf(rp.deref()));
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(s))]));
            }
            B::IterMap | B::IterFilter | B::IterFilterMap | B::IterInspect => {
                let (i, f) = (arg()?, arg()?);
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i, f]));
            }
            B::IterEnumerate => {
                let i = arg()?;
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i, Self::usize_c(0)]));
            }
            B::IterRev | B::IterCopied | B::IterCloned => {
                let i = arg()?;
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i]));
            }
            B::IterTake | B::IterSkip => {
                let (i, n) = (arg()?, arg()?);
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i, n]));
            }
            B::IterTakeWhile | B::IterSkipWhile => {
                let (i, p) = (arg()?, arg()?);
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i, Operand::Const(Const::Bool(false)), p]));
            }
            B::IterPeekable => {
                let i = arg()?;
                let fields = it::field_tys(&mut self.body.tys, dest_ty).ok_or("iterator expansion: bad Peekable")?;
                let slot = self.local(fields[1]);
                self.none(&Place::local(slot), fields[1]);
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i, Operand::Move(Place::local(slot))]));
            }
            B::IterStepBy => {
                let (i, n) = (arg()?, arg()?);
                // `assert!(step != 0)`, then `step_minus_one`.
                let ok = self.cmp(crate::ast::BinOp::Ne, n.clone(), Self::usize_c(0));
                let (good, bad) = self.branch(ok);
                self.cur = bad;
                self.term(Terminator::Panic(vec![FmtPart::Lit("assertion failed: step != 0".into())]));
                self.cur = good;
                let m = self.local(USIZE);
                self.assign(Place::local(m), Rvalue::Bin(crate::ast::BinOp::Sub, n, Self::usize_c(1)));
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i, Operand::Copy(Place::local(m)), Operand::Const(Const::Bool(true))]));
            }
            B::IterChain => {
                let (a, other) = (arg()?, arg()?);
                let fields = it::field_tys(&mut self.body.tys, dest_ty).ok_or("iterator expansion: bad Chain")?;
                let (_, targs) = self.kind_args(dest_ty).ok_or("iterator expansion: bad Chain")?;
                let bv = self.into_iter(other, targs[1])?;
                let (oa, ob) = (self.local(fields[0]), self.local(fields[1]));
                self.some(&Place::local(oa), fields[0], a);
                self.some(&Place::local(ob), fields[1], bv);
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(oa)), Operand::Move(Place::local(ob))]));
            }
            B::IterZip => {
                let (a, other) = (arg()?, arg()?);
                let (_, targs) = self.kind_args(dest_ty).ok_or("iterator expansion: bad Zip")?;
                let bv = self.into_iter(other, targs[1])?;
                let (al, bl) = (self.local(targs[0]), self.local(targs[1]));
                self.assign(Place::local(al), Rvalue::Use(a));
                self.assign(Place::local(bl), Rvalue::Use(bv));
                // Both sides random access: the length is fixed now
                // (Rust's `ZipImpl::new` for `TrustedRandomAccess`).
                let len = self.local(USIZE);
                if self.tra(targs[0]) && self.tra(targs[1]) {
                    let x = self.size(Place::local(al), targs[0])?;
                    let y = self.size(Place::local(bl), targs[1])?;
                    self.call_builtin(B::Min, vec![x, y], Place::local(len));
                } else {
                    self.assign(Place::local(len), Rvalue::Use(Self::usize_c(0)));
                }
                self.assign(
                    dest,
                    Rvalue::TupleAgg(
                        dest_ty,
                        vec![Operand::Move(Place::local(al)), Operand::Move(Place::local(bl)), Self::usize_c(0), Operand::Copy(Place::local(len))],
                    ),
                );
            }
            B::IterNext => {
                let r = arg()?;
                let (itp, ty) = self.deref_arg(r)?;
                self.next(itp, ty, dest, false)?;
            }
            B::IterPeek => {
                let r = arg()?;
                let (itp, ty) = self.deref_arg(r)?;
                self.peek(itp, ty, dest, dest_ty)?;
            }
            B::IterNth => {
                let (r, n) = (arg()?, arg()?);
                let (itp, ty) = self.deref_arg(r)?;
                let nl = self.local(USIZE);
                self.assign(Place::local(nl), Rvalue::Use(n));
                self.nth(itp, ty, nl, dest)?;
            }
            B::IterAny | B::IterAll | B::IterFind | B::IterFindMap | B::IterPosition => {
                let (r, f) = (arg()?, arg()?);
                let (itp, ty) = self.deref_arg(r)?;
                let fty = self.op_ty(&f)?;
                let fl = self.local(fty);
                self.assign(Place::local(fl), Rvalue::Use(f));
                self.search(b, itp, ty, Place::local(fl), fty, dest, dest_ty)?;
                self.drop_local(fl);
            }
            B::IterCount | B::IterLast | B::IterMin | B::IterMax | B::IterCollect | B::IterSum | B::IterProduct => {
                let i = arg()?;
                let (owned, ty) = self.own(i)?;
                match b {
                    B::IterCount => self.count(Place::local(owned), ty, dest)?,
                    B::IterLast => self.last(Place::local(owned), ty, dest, dest_ty)?,
                    B::IterMin | B::IterMax => self.min_max(b == B::IterMax, Place::local(owned), ty, None, dest, dest_ty)?,
                    B::IterCollect => self.collect(Place::local(owned), ty, dest, dest_ty)?,
                    _ => self.sum(b == B::IterProduct, Place::local(owned), ty, dest, dest_ty)?,
                }
                self.drop_local(owned);
            }
            B::IterMinByKey | B::IterMaxByKey | B::IterForEach => {
                let (i, f) = (arg()?, arg()?);
                let (owned, ty) = self.own(i)?;
                let fty = self.op_ty(&f)?;
                let fl = self.local(fty);
                self.assign(Place::local(fl), Rvalue::Use(f));
                if b == B::IterForEach {
                    self.for_each(Place::local(owned), ty, Place::local(fl), fty)?;
                    self.assign(dest, Rvalue::Use(Operand::Const(Const::Unit)));
                } else {
                    self.min_max(b == B::IterMaxByKey, Place::local(owned), ty, Some((Place::local(fl), fty)), dest, dest_ty)?;
                }
                self.drop_local(owned);
                self.drop_local(fl);
            }
            B::IterFold => {
                let (i, init, f) = (arg()?, arg()?, arg()?);
                let (owned, ty) = self.own(i)?;
                let fty = self.op_ty(&f)?;
                let fl = self.local(fty);
                self.assign(Place::local(fl), Rvalue::Use(f));
                self.fold(Place::local(owned), ty, init, Place::local(fl), fty, dest, dest_ty)?;
                self.drop_local(owned);
                self.drop_local(fl);
            }
            _ => return Err(format!("iterator expansion: unexpected builtin {b:?}")),
        }
        Ok(())
    }

    /// The iterator place and type behind a `&mut I` argument.
    fn deref_arg(&mut self, r: Operand) -> Result<(Place, Ty), String> {
        let rt = self.op_ty(&r)?;
        let TyKind::Ref(_, _, ty) = self.body.tys.kind(rt) else {
            return Err("iterator expansion: `&mut self` argument is not a reference".into());
        };
        let pl = self.op_place(r, rt);
        Ok((pl.deref(), ty))
    }

    /// Moves a by-value iterator argument into a fresh local the
    /// consumer owns (dropped when the consumer returns, as in Rust).
    fn own(&mut self, i: Operand) -> Result<(Local, Ty), String> {
        let ty = self.op_ty(&i)?;
        let l = self.local(ty);
        self.assign(Place::local(l), Rvalue::Use(i));
        Ok((l, ty))
    }

    /// An `IntoIterator` argument of `chain` or `zip` as the iterator
    /// type `want` (check/iter.rs `into_iter_ty`).
    fn into_iter(&mut self, o: Operand, want: Ty) -> Result<Operand, String> {
        let ot = self.op_ty(&o)?;
        if ot == want {
            return Ok(o);
        }
        let Some((k, _)) = self.kind_args(want) else { return Err("iterator expansion: bad IntoIterator argument".into()) };
        let l = self.local(want);
        match k {
            IterKind::VecIntoIter => self.call_builtin(Builtin::IterVecIntoIter, vec![o], Place::local(l)),
            IterKind::SliceIter | IterKind::SliceIterMut => {
                let fields = it::field_tys(&mut self.body.tys, want).ok_or("iterator expansion: bad slice iterator")?;
                let pl = self.op_place(o, ot);
                let s = self.local(fields[0]);
                self.assign(Place::local(s), Rvalue::SliceOf(pl.deref()));
                self.assign(Place::local(l), Rvalue::TupleAgg(want, vec![Operand::Move(Place::local(s))]));
            }
            _ => return Err("iterator expansion: bad IntoIterator argument".into()),
        }
        Ok(Operand::Move(Place::local(l)))
    }

    // ---------- next and next_back ----------

    /// `dest = itp.next()` (`next_back` when `back`).
    fn next(&mut self, itp: Place, ty: Ty, dest: Place, back: bool) -> R {
        use crate::ast::BinOp::*;
        use IterKind as K;
        let item = self.item(ty)?;
        let opt = self.body.tys.mk_option(item);
        let join = self.block();
        if self.body.tys.is_chars_ty(ty) {
            let r = self.ref_to(true, itp, ty);
            let b = if back { Builtin::CharsNextBack } else { Builtin::CharsNext };
            self.call_builtin(b, vec![Operand::Move(Place::local(r))], dest);
            self.goto(join);
            self.cur = join;
            return Ok(());
        }
        let (k, a) = self.kind_args(ty).ok_or("iterator expansion: not an iterator")?;
        let f = |i: u32| itp.project(Proj::Field(i));
        match k {
            K::SliceIter | K::SliceIterMut => {
                let m = k == K::SliceIterMut;
                let sd = f(0).deref();
                let len = self.local(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(sd.clone()));
                let c = self.cmp(Lt, Self::usize_c(0), Operand::Copy(Place::local(len)));
                let (s, n) = self.branch(c);
                self.cur = s;
                let idx = self.local(USIZE);
                if back {
                    self.assign(Place::local(idx), Rvalue::Bin(Sub, Operand::Copy(Place::local(len)), Self::usize_c(1)));
                } else {
                    self.assign(Place::local(idx), Rvalue::Use(Self::usize_c(0)));
                }
                let r = self.ref_to(m, sd.project(Proj::Index(idx)), a[0]);
                let rest_ty = self.place_ty(&f(0))?;
                let rest = self.local(rest_ty);
                let (lo, hi) = if back { (Self::usize_c(0), Some(Operand::Copy(Place::local(idx)))) } else { (Self::usize_c(1), None) };
                self.assign(Place::local(rest), Rvalue::Subslice { base: sd, lo, hi, inclusive: false, mutable: m });
                self.assign(f(0), Rvalue::Use(Operand::Move(Place::local(rest))));
                self.some(&dest, opt, Operand::Move(Place::local(r)));
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::VecIntoIter => {
                let r = self.ref_to(true, itp, ty);
                let b = if back { Builtin::VecIterNextBack } else { Builtin::VecIterNext };
                self.call_builtin(b, vec![Operand::Move(Place::local(r))], dest);
                self.goto(join);
            }
            K::Range => {
                let c = self.cmp(Lt, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (s, n) = self.branch(c);
                self.cur = s;
                let one = Self::one(a[0], &self.body.tys)?;
                let v = self.local(a[0]);
                if back {
                    self.assign(f(1), Rvalue::Bin(Sub, Operand::Copy(f(1)), one));
                    self.assign(Place::local(v), Rvalue::Use(Operand::Copy(f(1))));
                } else {
                    self.assign(Place::local(v), Rvalue::Use(Operand::Copy(f(0))));
                    self.assign(f(0), Rvalue::Bin(Add, Operand::Copy(f(0)), one));
                }
                self.some(&dest, opt, Operand::Copy(Place::local(v)));
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::RangeInclusive => {
                let none_b = self.block();
                let (ex, live) = self.branch(Operand::Copy(f(2)));
                self.cur = ex;
                self.goto(none_b);
                self.cur = live;
                let c = self.cmp(Le, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (go, empty) = self.branch(c);
                self.cur = empty;
                self.goto(none_b);
                self.cur = go;
                let lt = self.cmp(Lt, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (step, last) = self.branch(lt);
                let one = Self::one(a[0], &self.body.tys)?;
                let v = self.local(a[0]);
                self.cur = step;
                if back {
                    self.assign(Place::local(v), Rvalue::Use(Operand::Copy(f(1))));
                    self.assign(f(1), Rvalue::Bin(Sub, Operand::Copy(f(1)), one));
                } else {
                    self.assign(Place::local(v), Rvalue::Use(Operand::Copy(f(0))));
                    self.assign(f(0), Rvalue::Bin(Add, Operand::Copy(f(0)), one));
                }
                self.some(&dest, opt, Operand::Copy(Place::local(v)));
                self.goto(join);
                self.cur = last;
                self.assign(f(2), Rvalue::Use(Operand::Const(Const::Bool(true))));
                self.some(&dest, opt, Operand::Copy(if back { f(1) } else { f(0) }));
                self.goto(join);
                self.cur = none_b;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Map | K::Inspect | K::Copied | K::Cloned => {
                let inner_item = self.item(a[0])?;
                let iopt = self.body.tys.mk_option(inner_item);
                let t = self.local(iopt);
                self.next(f(0), a[0], Place::local(t), back)?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = s;
                let x = self.local(inner_item);
                let px = self.take(Self::payload(&Place::local(t)), inner_item);
                self.assign(Place::local(x), Rvalue::Use(px));
                match k {
                    K::Map => {
                        let fty = a[1];
                        let y = self.local(item);
                        let ax = self.take(Place::local(x), inner_item);
                        self.call_fn(fty, f(1), vec![ax], Place::local(y))?;
                        let ay = self.take(Place::local(y), item);
                        self.some(&dest, opt, ay);
                    }
                    K::Inspect => {
                        let rx = self.ref_to(false, Place::local(x), inner_item);
                        let u = self.local(UNIT);
                        self.call_fn(a[1], f(1), vec![Operand::Move(Place::local(rx))], Place::local(u))?;
                        let ax = self.take(Place::local(x), item);
                        self.some(&dest, opt, ax);
                    }
                    K::Copied => self.some(&dest, opt, Operand::Copy(Place::local(x).deref())),
                    _ => {
                        let y = self.local(item);
                        self.call_builtin(Builtin::Clone, vec![Operand::Copy(Place::local(x))], Place::local(y));
                        let ay = self.take(Place::local(y), item);
                        self.some(&dest, opt, ay);
                    }
                }
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Filter | K::SkipWhile => {
                // Pull until the predicate keeps an item; rejected items
                // drop right away.
                let lp = self.block();
                self.goto(lp);
                self.cur = lp;
                let t = self.local(opt);
                self.next(f(0), a[0], Place::local(t), back)?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
                self.cur = s;
                let x = self.local(item);
                let px = self.take(Self::payload(&Place::local(t)), item);
                self.assign(Place::local(x), Rvalue::Use(px));
                let (keep, skip) = if k == K::Filter {
                    let rx = self.ref_to(false, Place::local(x), item);
                    let b = self.local(BOOL);
                    self.call_fn(a[1], f(1), vec![Operand::Move(Place::local(rx))], Place::local(b))?;
                    self.branch(Operand::Copy(Place::local(b)))
                } else {
                    // `*flag || !pred(x)` keeps the item and sets the flag.
                    let keep = self.block();
                    let (flagged, open) = self.branch(Operand::Copy(f(1)));
                    self.cur = flagged;
                    self.goto(keep);
                    self.cur = open;
                    let rx = self.ref_to(false, Place::local(x), item);
                    let b = self.local(BOOL);
                    self.call_fn(a[1], f(2), vec![Operand::Move(Place::local(rx))], Place::local(b))?;
                    let (skip, k2) = self.branch(Operand::Copy(Place::local(b)));
                    self.cur = k2;
                    self.assign(f(1), Rvalue::Use(Operand::Const(Const::Bool(true))));
                    self.goto(keep);
                    (keep, skip)
                };
                self.cur = keep;
                let ax = self.take(Place::local(x), item);
                self.some(&dest, opt, ax);
                self.goto(join);
                self.cur = skip;
                self.drop_local(x);
                self.goto(lp);
            }
            K::FilterMap => {
                let inner_item = self.item(a[0])?;
                let iopt = self.body.tys.mk_option(inner_item);
                let lp = self.block();
                self.goto(lp);
                self.cur = lp;
                let t = self.local(iopt);
                self.next(f(0), a[0], Place::local(t), back)?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
                self.cur = s;
                let px = self.take(Self::payload(&Place::local(t)), inner_item);
                let o = self.local(opt);
                self.call_fn(a[1], f(1), vec![px], Place::local(o))?;
                let (hit, miss) = self.switch_opt(&Place::local(o));
                self.cur = hit;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(o))));
                self.goto(join);
                self.cur = miss;
                self.goto(lp);
            }
            K::Enumerate => {
                if back {
                    return Err("iterator expansion: Enumerate is forward-only here".into());
                }
                let inner_item = self.item(a[0])?;
                let iopt = self.body.tys.mk_option(inner_item);
                let t = self.local(iopt);
                self.next(f(0), a[0], Place::local(t), false)?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = s;
                let i = self.local(USIZE);
                self.assign(Place::local(i), Rvalue::Use(Operand::Copy(f(1))));
                self.assign(f(1), Rvalue::Bin(Add, Operand::Copy(f(1)), Self::usize_c(1)));
                let px = self.take(Self::payload(&Place::local(t)), inner_item);
                let tup = self.local(item);
                self.assign(Place::local(tup), Rvalue::TupleAgg(item, vec![Operand::Copy(Place::local(i)), px]));
                let at = self.take(Place::local(tup), item);
                self.some(&dest, opt, at);
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Rev => {
                self.next(f(0), a[0], dest, !back)?;
                self.goto(join);
            }
            K::Take => {
                if back {
                    return Err("iterator expansion: Take is forward-only here".into());
                }
                let c = self.cmp(Ne, Operand::Copy(f(1)), Self::usize_c(0));
                let (s, n) = self.branch(c);
                self.cur = s;
                self.assign(f(1), Rvalue::Bin(Sub, Operand::Copy(f(1)), Self::usize_c(1)));
                self.next(f(0), a[0], dest.clone(), false)?;
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Skip => {
                if back {
                    return Err("iterator expansion: Skip is forward-only here".into());
                }
                let c = self.cmp(Lt, Self::usize_c(0), Operand::Copy(f(1)));
                let (s, n) = self.branch(c);
                self.cur = s;
                let cnt = self.local(USIZE);
                self.assign(Place::local(cnt), Rvalue::Use(Operand::Copy(f(1))));
                self.assign(f(1), Rvalue::Use(Self::usize_c(0)));
                self.nth(f(0), a[0], cnt, dest.clone())?;
                self.goto(join);
                self.cur = n;
                self.next(f(0), a[0], dest, false)?;
                self.goto(join);
            }
            K::StepBy => {
                if back {
                    return Err("iterator expansion: StepBy is forward-only here".into());
                }
                // `nth(if first_take { 0 } else { step_minus_one })`.
                let step = self.local(USIZE);
                let (first, later) = self.branch(Operand::Copy(f(2)));
                let go = self.block();
                self.cur = first;
                self.assign(Place::local(step), Rvalue::Use(Self::usize_c(0)));
                self.goto(go);
                self.cur = later;
                self.assign(Place::local(step), Rvalue::Use(Operand::Copy(f(1))));
                self.goto(go);
                self.cur = go;
                self.assign(f(2), Rvalue::Use(Operand::Const(Const::Bool(false))));
                self.nth(f(0), a[0], step, dest)?;
                self.goto(join);
            }
            K::Chain => {
                let (first, second) = if back { (1u32, 0u32) } else { (0, 1) };
                let other = self.block();
                let (fs, fnone) = self.switch_opt(&f(first));
                self.cur = fnone;
                self.goto(other);
                self.cur = fs;
                let t = self.local(opt);
                self.next(Self::payload(&f(first)), a[first as usize], Place::local(t), back)?;
                let (hit, done) = self.switch_opt(&Place::local(t));
                self.cur = hit;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(t))));
                self.goto(join);
                self.cur = done;
                // `and_then_or_clear`: the spent side drops now.
                let fty = self.place_ty(&f(first))?;
                self.none(&f(first), fty);
                self.goto(other);
                self.cur = other;
                let (ss, snone) = self.switch_opt(&f(second));
                self.cur = ss;
                self.next(Self::payload(&f(second)), a[second as usize], dest.clone(), back)?;
                self.goto(join);
                self.cur = snone;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Zip => {
                if back {
                    return Err("iterator expansion: Zip is forward-only here".into());
                }
                let (ia, ib) = (self.item(a[0])?, self.item(a[1])?);
                if self.tra(a[0]) && self.tra(a[1]) {
                    let c = self.cmp(Lt, Operand::Copy(f(2)), Operand::Copy(f(3)));
                    let (s, n) = self.branch(c);
                    self.cur = s;
                    let i = self.local(USIZE);
                    self.assign(Place::local(i), Rvalue::Use(Operand::Copy(f(2))));
                    self.assign(f(2), Rvalue::Bin(Add, Operand::Copy(f(2)), Self::usize_c(1)));
                    let (x, y) = (self.local(ia), self.local(ib));
                    self.get(f(0), a[0], i, Place::local(x))?;
                    self.get(f(1), a[1], i, Place::local(y))?;
                    let ax = self.take(Place::local(x), ia);
                    let ay = self.take(Place::local(y), ib);
                    let tup = self.local(item);
                    self.assign(Place::local(tup), Rvalue::TupleAgg(item, vec![ax, ay]));
                    let at = self.take(Place::local(tup), item);
                    self.some(&dest, opt, at);
                    self.goto(join);
                    self.cur = n;
                    self.none(&dest, opt);
                    self.goto(join);
                } else {
                    let none_b = self.block();
                    let (oa, ob) = (self.body.tys.mk_option(ia), self.body.tys.mk_option(ib));
                    let ta = self.local(oa);
                    self.next(f(0), a[0], Place::local(ta), false)?;
                    let (s, n) = self.switch_opt(&Place::local(ta));
                    self.cur = n;
                    self.goto(none_b);
                    self.cur = s;
                    let x = self.local(ia);
                    let px = self.take(Self::payload(&Place::local(ta)), ia);
                    self.assign(Place::local(x), Rvalue::Use(px));
                    let tb = self.local(ob);
                    self.next(f(1), a[1], Place::local(tb), false)?;
                    let (s2, n2) = self.switch_opt(&Place::local(tb));
                    self.cur = n2;
                    self.drop_local(x);
                    self.goto(none_b);
                    self.cur = s2;
                    let py = self.take(Self::payload(&Place::local(tb)), ib);
                    let ax = self.take(Place::local(x), ia);
                    let tup = self.local(item);
                    self.assign(Place::local(tup), Rvalue::TupleAgg(item, vec![ax, py]));
                    let at = self.take(Place::local(tup), item);
                    self.some(&dest, opt, at);
                    self.goto(join);
                    self.cur = none_b;
                    self.none(&dest, opt);
                    self.goto(join);
                }
            }
            K::TakeWhile => {
                if back {
                    return Err("iterator expansion: TakeWhile is forward-only".into());
                }
                let none_b = self.block();
                let (done, open) = self.branch(Operand::Copy(f(1)));
                self.cur = done;
                self.goto(none_b);
                self.cur = open;
                let t = self.local(opt);
                self.next(f(0), a[0], Place::local(t), false)?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = n;
                self.goto(none_b);
                self.cur = s;
                let x = self.local(item);
                let px = self.take(Self::payload(&Place::local(t)), item);
                self.assign(Place::local(x), Rvalue::Use(px));
                let rx = self.ref_to(false, Place::local(x), item);
                let b = self.local(BOOL);
                self.call_fn(a[1], f(2), vec![Operand::Move(Place::local(rx))], Place::local(b))?;
                let (keep, stop) = self.branch(Operand::Copy(Place::local(b)));
                self.cur = keep;
                let ax = self.take(Place::local(x), item);
                self.some(&dest, opt, ax);
                self.goto(join);
                self.cur = stop;
                self.assign(f(1), Rvalue::Use(Operand::Const(Const::Bool(true))));
                self.drop_local(x);
                self.goto(none_b);
                self.cur = none_b;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Peekable => {
                // `match self.peeked.take() { Some(v) => v, None => self.iter.next() }`
                let slot = f(1);
                let (s, n) = self.switch_opt(&slot);
                self.cur = s;
                let pty = self.place_ty(&slot)?;
                let v = self.local(opt);
                self.assign(Place::local(v), Rvalue::Use(Operand::Move(Self::payload(&slot))));
                self.none(&slot, pty);
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(v))));
                self.goto(join);
                self.cur = n;
                if back {
                    return Err("iterator expansion: Peekable is forward-only here".into());
                }
                self.next(f(0), a[0], dest, false)?;
                self.goto(join);
            }
        }
        self.cur = join;
        Ok(())
    }

    /// The integer 1 of a range element type.
    fn one(t: Ty, tys: &Tys) -> Result<Operand, String> {
        match tys.kind(t) {
            TyKind::Int(i) => Ok(Operand::Const(Const::Int(1, i))),
            _ => Err("iterator expansion: range over a non-integer".into()),
        }
    }

    /// `Peekable::peek`: fill the slot from `next` when it is empty,
    /// then a reference to the peeked item.
    fn peek(&mut self, itp: Place, ty: Ty, dest: Place, dest_ty: Ty) -> R {
        let (_, a) = self.kind_args(ty).ok_or("iterator expansion: peek on a non-Peekable")?;
        let item = self.item(ty)?;
        let opt = self.body.tys.mk_option(item);
        let slot = itp.project(Proj::Field(1));
        let pty = self.place_ty(&slot)?;
        let (full, empty) = self.switch_opt(&slot);
        self.cur = empty;
        let t = self.local(opt);
        self.next(itp.project(Proj::Field(0)), a[0], Place::local(t), false)?;
        self.some(&slot, pty, Operand::Move(Place::local(t)));
        self.goto(full);
        self.cur = full;
        let inner = Self::payload(&slot);
        let (s, n) = self.switch_opt(&inner);
        let join = self.block();
        self.cur = s;
        let r = self.ref_to(false, Self::payload(&inner), item);
        self.some(&dest, dest_ty, Operand::Move(Place::local(r)));
        self.goto(join);
        self.cur = n;
        self.none(&dest, dest_ty);
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// `dest = itp.nth(n)`: pull and drop `n` items, then `next`.
    fn nth(&mut self, itp: Place, ty: Ty, n: Local, dest: Place) -> R {
        use crate::ast::BinOp::*;
        let item = self.item(ty)?;
        let opt = self.body.tys.mk_option(item);
        let join = self.block();
        let i = self.local(USIZE);
        self.assign(Place::local(i), Rvalue::Use(Self::usize_c(0)));
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        let c = self.cmp(Lt, Operand::Copy(Place::local(i)), Operand::Copy(Place::local(n)));
        let (pull, last) = self.branch(c);
        self.cur = pull;
        let t = self.local(opt);
        self.next(itp.clone(), ty, Place::local(t), false)?;
        let (s, none) = self.switch_opt(&Place::local(t));
        self.cur = none;
        self.none(&dest, opt);
        self.goto(join);
        self.cur = s;
        self.drop_local(t);
        self.assign(Place::local(i), Rvalue::Bin(Add, Operand::Copy(Place::local(i)), Self::usize_c(1)));
        self.goto(lp);
        self.cur = last;
        self.next(itp, ty, dest, false)?;
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    // ---------- Random access (TrustedRandomAccess) ----------

    /// True when Rust 1.99 implements `TrustedRandomAccess` for this
    /// type: `Zip` then pulls by index, only as far as the short side.
    fn tra(&self, ty: Ty) -> bool {
        use IterKind as K;
        let Some((k, a)) = self.kind_args(ty) else { return false };
        match k {
            K::SliceIter | K::SliceIterMut => true,
            K::Range => matches!(
                self.body.tys.kind(a[0]),
                TyKind::Int(IntTy::Usize | IntTy::U8 | IntTy::U16 | IntTy::U32 | IntTy::U64 | IntTy::Isize | IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64)
            ),
            K::Map | K::Enumerate | K::Copied | K::Cloned | K::Skip => self.tra(a[0]),
            K::Zip => self.tra(a[0]) && self.tra(a[1]),
            _ => false,
        }
    }

    /// The exact remaining length of a random-access iterator.
    fn size(&mut self, itp: Place, ty: Ty) -> Result<Operand, String> {
        use crate::ast::BinOp::*;
        use IterKind as K;
        let (k, a) = self.kind_args(ty).ok_or("iterator expansion: size of a non-iterator")?;
        let f = |i: u32| itp.project(Proj::Field(i));
        let out = self.local(USIZE);
        match k {
            K::SliceIter | K::SliceIterMut => self.assign(Place::local(out), Rvalue::LenOf(f(0).deref())),
            K::Range => {
                let c = self.cmp(Lt, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (s, n) = self.branch(c);
                let join = self.block();
                self.cur = s;
                let wide = int(IntTy::I128);
                let (lo, hi) = (self.local(wide), self.local(wide));
                self.assign(Place::local(lo), Rvalue::Cast(Operand::Copy(f(0)), wide));
                self.assign(Place::local(hi), Rvalue::Cast(Operand::Copy(f(1)), wide));
                let d = self.local(wide);
                self.assign(Place::local(d), Rvalue::Bin(Sub, Operand::Copy(Place::local(hi)), Operand::Copy(Place::local(lo))));
                self.assign(Place::local(out), Rvalue::Cast(Operand::Copy(Place::local(d)), USIZE));
                self.goto(join);
                self.cur = n;
                self.assign(Place::local(out), Rvalue::Use(Self::usize_c(0)));
                self.goto(join);
                self.cur = join;
            }
            K::Map | K::Enumerate | K::Copied | K::Cloned => return self.size(f(0), a[0]),
            K::Skip => {
                let inner = self.size(f(0), a[0])?;
                self.call_builtin(Builtin::SaturatingSub, vec![inner, Operand::Copy(f(1))], Place::local(out));
            }
            K::Zip => {
                self.assign(Place::local(out), Rvalue::Bin(Sub, Operand::Copy(f(3)), Operand::Copy(f(2))));
            }
            _ => return Err("iterator expansion: size of a non-random-access iterator".into()),
        }
        Ok(Operand::Copy(Place::local(out)))
    }

    /// `dest = itp.__iterator_get_unchecked(i)` for a random-access
    /// iterator: the item at index `i` from the current position,
    /// without moving the position (as Rust's `Zip` uses it).
    fn get(&mut self, itp: Place, ty: Ty, i: Local, dest: Place) -> R {
        use crate::ast::BinOp::*;
        use IterKind as K;
        let (k, a) = self.kind_args(ty).ok_or("iterator expansion: get on a non-iterator")?;
        let f = |j: u32| itp.project(Proj::Field(j));
        match k {
            K::SliceIter | K::SliceIterMut => {
                let m = k == K::SliceIterMut;
                let pl = f(0).deref().project(Proj::Index(i));
                self.assign(dest, Rvalue::Ref(m, pl));
            }
            K::Range => {
                let off = self.local(a[0]);
                self.assign(Place::local(off), Rvalue::Cast(Operand::Copy(Place::local(i)), a[0]));
                self.assign(dest, Rvalue::Bin(Add, Operand::Copy(f(0)), Operand::Copy(Place::local(off))));
            }
            K::Map => {
                let ii = self.item(a[0])?;
                let x = self.local(ii);
                self.get(f(0), a[0], i, Place::local(x))?;
                let ax = self.take(Place::local(x), ii);
                self.call_fn(a[1], f(1), vec![ax], dest)?;
            }
            K::Enumerate => {
                let ii = self.item(a[0])?;
                let x = self.local(ii);
                self.get(f(0), a[0], i, Place::local(x))?;
                let c = self.local(USIZE);
                self.assign(Place::local(c), Rvalue::Bin(Add, Operand::Copy(f(1)), Operand::Copy(Place::local(i))));
                let item = self.item(ty)?;
                let ax = self.take(Place::local(x), ii);
                self.assign(dest, Rvalue::TupleAgg(item, vec![Operand::Copy(Place::local(c)), ax]));
            }
            K::Copied | K::Cloned => {
                let ii = self.item(a[0])?;
                let r = self.local(ii);
                self.get(f(0), a[0], i, Place::local(r))?;
                if k == K::Copied {
                    self.assign(dest, Rvalue::Use(Operand::Copy(Place::local(r).deref())));
                } else {
                    self.call_builtin(Builtin::Clone, vec![Operand::Copy(Place::local(r))], dest);
                }
            }
            K::Skip => {
                let j = self.local(USIZE);
                self.assign(Place::local(j), Rvalue::Bin(Add, Operand::Copy(f(1)), Operand::Copy(Place::local(i))));
                self.get(f(0), a[0], j, dest)?;
            }
            K::Zip => {
                let j = self.local(USIZE);
                self.assign(Place::local(j), Rvalue::Bin(Add, Operand::Copy(f(2)), Operand::Copy(Place::local(i))));
                let (ia, ib) = (self.item(a[0])?, self.item(a[1])?);
                let (x, y) = (self.local(ia), self.local(ib));
                self.get(f(0), a[0], j, Place::local(x))?;
                self.get(f(1), a[1], j, Place::local(y))?;
                let item = self.item(ty)?;
                let ax = self.take(Place::local(x), ia);
                let ay = self.take(Place::local(y), ib);
                self.assign(dest, Rvalue::TupleAgg(item, vec![ax, ay]));
            }
            _ => return Err("iterator expansion: get on a non-random-access iterator".into()),
        }
        Ok(())
    }

    // ---------- size_hint ----------

    /// `itp.size_hint()` as (lower, upper) locals: `usize` and
    /// `Option<usize>`, with Rust 1.99's arithmetic per kind.
    fn hint(&mut self, itp: Place, ty: Ty) -> Result<(Local, Local), String> {
        use crate::ast::BinOp::*;
        use IterKind as K;
        let ou = self.body.tys.mk_option(USIZE);
        let (lo, hi) = (self.local(USIZE), self.local(ou));
        let set_exact = |this: &mut Self, n: Operand| {
            this.assign(Place::local(lo), Rvalue::Use(n.clone()));
            this.some(&Place::local(hi), ou, n);
        };
        if self.body.tys.is_chars_ty(ty) {
            // ((bytes + 3) / 4, Some(bytes)) over the bytes left.
            let r = self.ref_to(false, itp, ty);
            let bytes = self.local(USIZE);
            self.call_builtin(Builtin::CharsBytesLeft, vec![Operand::Move(Place::local(r))], Place::local(bytes));
            let b3 = self.local(USIZE);
            self.assign(Place::local(b3), Rvalue::Bin(Add, Operand::Copy(Place::local(bytes)), Self::usize_c(3)));
            self.assign(Place::local(lo), Rvalue::Bin(Div, Operand::Copy(Place::local(b3)), Self::usize_c(4)));
            self.some(&Place::local(hi), ou, Operand::Copy(Place::local(bytes)));
            return Ok((lo, hi));
        }
        let (k, a) = self.kind_args(ty).ok_or("iterator expansion: size_hint of a non-iterator")?;
        let f = |i: u32| itp.project(Proj::Field(i));
        match k {
            K::SliceIter | K::SliceIterMut | K::Range | K::Zip if k != K::Zip || (self.tra(a[0]) && self.tra(a[1])) => {
                let n = self.size(itp.clone(), ty)?;
                set_exact(self, n);
            }
            K::VecIntoIter => {
                let r = self.ref_to(false, itp, ty);
                let n = self.local(USIZE);
                self.call_builtin(Builtin::VecIterLen, vec![Operand::Move(Place::local(r))], Place::local(n));
                set_exact(self, Operand::Copy(Place::local(n)));
            }
            K::RangeInclusive => {
                // Exhausted or empty: (0, Some(0)); else steps + 1, with
                // `checked_add` on the upper bound.
                let join = self.block();
                let zero = self.block();
                let (ex, live) = self.branch(Operand::Copy(f(2)));
                self.cur = ex;
                self.goto(zero);
                self.cur = live;
                let c = self.cmp(Le, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (go, empty) = self.branch(c);
                self.cur = empty;
                self.goto(zero);
                self.cur = go;
                let wide = int(IntTy::I128);
                let (l0, l1) = (self.local(wide), self.local(wide));
                self.assign(Place::local(l0), Rvalue::Cast(Operand::Copy(f(0)), wide));
                self.assign(Place::local(l1), Rvalue::Cast(Operand::Copy(f(1)), wide));
                let d = self.local(wide);
                self.assign(Place::local(d), Rvalue::Bin(Sub, Operand::Copy(Place::local(l1)), Operand::Copy(Place::local(l0))));
                let steps = self.local(USIZE);
                self.assign(Place::local(steps), Rvalue::Cast(Operand::Copy(Place::local(d)), USIZE));
                self.call_builtin(Builtin::SaturatingAdd, vec![Operand::Copy(Place::local(steps)), Self::usize_c(1)], Place::local(lo));
                self.call_builtin(Builtin::CheckedAdd, vec![Operand::Copy(Place::local(steps)), Self::usize_c(1)], Place::local(hi));
                self.goto(join);
                self.cur = zero;
                set_exact(self, Self::usize_c(0));
                self.goto(join);
                self.cur = join;
            }
            K::Map | K::Inspect | K::Copied | K::Cloned | K::Enumerate | K::Rev => return self.hint(f(0), a[0]),
            K::Filter | K::FilterMap | K::SkipWhile => {
                let (_, ih) = self.hint(f(0), a[0])?;
                self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(0)));
                self.assign(Place::local(hi), Rvalue::Use(Operand::Move(Place::local(ih))));
            }
            K::TakeWhile => {
                let join = self.block();
                let (done, open) = self.branch(Operand::Copy(f(1)));
                self.cur = done;
                set_exact(self, Self::usize_c(0));
                self.goto(join);
                self.cur = open;
                let (_, ih) = self.hint(f(0), a[0])?;
                self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(0)));
                self.assign(Place::local(hi), Rvalue::Use(Operand::Move(Place::local(ih))));
                self.goto(join);
                self.cur = join;
            }
            K::Take => {
                let join = self.block();
                let z = self.cmp(Eq, Operand::Copy(f(1)), Self::usize_c(0));
                let (zero, go) = self.branch(z);
                self.cur = zero;
                set_exact(self, Self::usize_c(0));
                self.goto(join);
                self.cur = go;
                let (il, ih) = self.hint(f(0), a[0])?;
                self.call_builtin(Builtin::Min, vec![Operand::Copy(Place::local(il)), Operand::Copy(f(1))], Place::local(lo));
                // Some(x) if x < n => Some(x), _ => Some(n)
                let (s, n) = self.switch_opt(&Place::local(ih));
                let take_n = self.block();
                self.cur = s;
                let x = Self::payload(&Place::local(ih));
                let lt = self.cmp(Lt, Operand::Copy(x.clone()), Operand::Copy(f(1)));
                let (keep, cap) = self.branch(lt);
                self.cur = keep;
                self.some(&Place::local(hi), ou, Operand::Copy(x));
                self.goto(join);
                self.cur = cap;
                self.goto(take_n);
                self.cur = n;
                self.goto(take_n);
                self.cur = take_n;
                self.some(&Place::local(hi), ou, Operand::Copy(f(1)));
                self.goto(join);
                self.cur = join;
            }
            K::Skip => {
                let (il, ih) = self.hint(f(0), a[0])?;
                self.call_builtin(Builtin::SaturatingSub, vec![Operand::Copy(Place::local(il)), Operand::Copy(f(1))], Place::local(lo));
                let join = self.block();
                let (s, n) = self.switch_opt(&Place::local(ih));
                self.cur = s;
                let x = self.local(USIZE);
                self.call_builtin(Builtin::SaturatingSub, vec![Operand::Copy(Self::payload(&Place::local(ih))), Operand::Copy(f(1))], Place::local(x));
                self.some(&Place::local(hi), ou, Operand::Copy(Place::local(x)));
                self.goto(join);
                self.cur = n;
                self.none(&Place::local(hi), ou);
                self.goto(join);
                self.cur = join;
            }
            K::Chain => {
                // (Some, Some): saturating sum, checked upper; one side
                // alone: its hint; neither: (0, Some(0)).
                let join = self.block();
                let (as_, an) = self.switch_opt(&f(0));
                self.cur = as_;
                let (al, ah) = self.hint(Self::payload(&f(0)), a[0])?;
                let (bs, bn) = self.switch_opt(&f(1));
                self.cur = bs;
                let (bl, bh) = self.hint(Self::payload(&f(1)), a[1])?;
                self.call_builtin(Builtin::SaturatingAdd, vec![Operand::Copy(Place::local(al)), Operand::Copy(Place::local(bl))], Place::local(lo));
                let both_none = self.block();
                let (ahs, ahn) = self.switch_opt(&Place::local(ah));
                self.cur = ahn;
                self.goto(both_none);
                self.cur = ahs;
                let (bhs, bhn) = self.switch_opt(&Place::local(bh));
                self.cur = bhn;
                self.goto(both_none);
                self.cur = bhs;
                self.call_builtin(
                    Builtin::CheckedAdd,
                    vec![Operand::Copy(Self::payload(&Place::local(ah))), Operand::Copy(Self::payload(&Place::local(bh)))],
                    Place::local(hi),
                );
                self.goto(join);
                self.cur = both_none;
                self.none(&Place::local(hi), ou);
                self.goto(join);
                self.cur = bn;
                self.assign(Place::local(lo), Rvalue::Use(Operand::Copy(Place::local(al))));
                self.assign(Place::local(hi), Rvalue::Use(Operand::Copy(Place::local(ah))));
                self.goto(join);
                self.cur = an;
                let (bs2, bn2) = self.switch_opt(&f(1));
                self.cur = bs2;
                let (bl2, bh2) = self.hint(Self::payload(&f(1)), a[1])?;
                self.assign(Place::local(lo), Rvalue::Use(Operand::Copy(Place::local(bl2))));
                self.assign(Place::local(hi), Rvalue::Use(Operand::Copy(Place::local(bh2))));
                self.goto(join);
                self.cur = bn2;
                set_exact(self, Self::usize_c(0));
                self.goto(join);
                self.cur = join;
            }
            K::Zip => {
                // The general impl: min of the lowers; the upper is the
                // min of the known uppers.
                let (al, ah) = self.hint(f(0), a[0])?;
                let (bl, bh) = self.hint(f(1), a[1])?;
                self.call_builtin(Builtin::Min, vec![Operand::Copy(Place::local(al)), Operand::Copy(Place::local(bl))], Place::local(lo));
                let join = self.block();
                let (ahs, ahn) = self.switch_opt(&Place::local(ah));
                self.cur = ahs;
                let (bhs, bhn) = self.switch_opt(&Place::local(bh));
                self.cur = bhs;
                let m = self.local(USIZE);
                self.call_builtin(
                    Builtin::Min,
                    vec![Operand::Copy(Self::payload(&Place::local(ah))), Operand::Copy(Self::payload(&Place::local(bh)))],
                    Place::local(m),
                );
                self.some(&Place::local(hi), ou, Operand::Copy(Place::local(m)));
                self.goto(join);
                self.cur = bhn;
                self.assign(Place::local(hi), Rvalue::Use(Operand::Copy(Place::local(ah))));
                self.goto(join);
                self.cur = ahn;
                self.assign(Place::local(hi), Rvalue::Use(Operand::Copy(Place::local(bh))));
                self.goto(join);
                self.cur = join;
            }
            K::StepBy => {
                // `first_size` (1 + (n - 1) / step for n > 0) before the
                // first take, `other_size` (n / step) after; the upper
                // bound maps the same way.
                let (il, ih) = self.hint(f(0), a[0])?;
                let step = self.local(USIZE);
                self.assign(Place::local(step), Rvalue::Bin(Add, Operand::Copy(f(1)), Self::usize_c(1)));
                let size = |this: &mut Self, n: Operand, out: Place| {
                    let join = this.block();
                    let (first, other) = this.branch(Operand::Copy(f(2)));
                    this.cur = first;
                    let z = this.cmp(Eq, n.clone(), Self::usize_c(0));
                    let (zero, pos) = this.branch(z);
                    this.cur = zero;
                    this.assign(out.clone(), Rvalue::Use(Self::usize_c(0)));
                    this.goto(join);
                    this.cur = pos;
                    let (m, q) = (this.local(USIZE), this.local(USIZE));
                    this.assign(Place::local(m), Rvalue::Bin(Sub, n.clone(), Self::usize_c(1)));
                    this.assign(Place::local(q), Rvalue::Bin(Div, Operand::Copy(Place::local(m)), Operand::Copy(Place::local(step))));
                    this.assign(out.clone(), Rvalue::Bin(Add, Operand::Copy(Place::local(q)), Self::usize_c(1)));
                    this.goto(join);
                    this.cur = other;
                    this.assign(out, Rvalue::Bin(Div, n, Operand::Copy(Place::local(step))));
                    this.goto(join);
                    this.cur = join;
                };
                size(self, Operand::Copy(Place::local(il)), Place::local(lo));
                let join = self.block();
                let (s, n) = self.switch_opt(&Place::local(ih));
                self.cur = s;
                let x = self.local(USIZE);
                size(self, Operand::Copy(Self::payload(&Place::local(ih))), Place::local(x));
                self.some(&Place::local(hi), ou, Operand::Copy(Place::local(x)));
                self.goto(join);
                self.cur = n;
                self.none(&Place::local(hi), ou);
                self.goto(join);
                self.cur = join;
            }
            K::Peekable => {
                // A peeked `None` ends it; a peeked item adds 1.
                let join = self.block();
                let slot = f(1);
                let add = self.local(USIZE);
                let go = self.block();
                let (full, empty) = self.switch_opt(&slot);
                self.cur = empty;
                self.assign(Place::local(add), Rvalue::Use(Self::usize_c(0)));
                self.goto(go);
                self.cur = full;
                let (some, none) = self.switch_opt(&Self::payload(&slot));
                self.cur = none;
                set_exact(self, Self::usize_c(0));
                self.goto(join);
                self.cur = some;
                self.assign(Place::local(add), Rvalue::Use(Self::usize_c(1)));
                self.goto(go);
                self.cur = go;
                let (il, ih) = self.hint(f(0), a[0])?;
                self.call_builtin(Builtin::SaturatingAdd, vec![Operand::Copy(Place::local(il)), Operand::Copy(Place::local(add))], Place::local(lo));
                let (hs, hn) = self.switch_opt(&Place::local(ih));
                self.cur = hs;
                self.call_builtin(Builtin::CheckedAdd, vec![Operand::Copy(Self::payload(&Place::local(ih))), Operand::Copy(Place::local(add))], Place::local(hi));
                self.goto(join);
                self.cur = hn;
                self.none(&Place::local(hi), ou);
                self.goto(join);
                self.cur = join;
            }
            K::SliceIter | K::SliceIterMut | K::Range => unreachable!("handled above"),
        }
        Ok((lo, hi))
    }

    /// True when Rust 1.99 implements `TrustedLen` for this type (the
    /// kinds lust has), which picks `collect`'s exact-capacity path.
    fn trusted_len(&self, ty: Ty) -> bool {
        use IterKind as K;
        let Some((k, a)) = self.kind_args(ty) else { return false };
        match k {
            K::SliceIter | K::SliceIterMut | K::VecIntoIter | K::Range | K::RangeInclusive => true,
            K::Map | K::Enumerate | K::Rev | K::Take | K::Copied | K::Cloned | K::Peekable => self.trusted_len(a[0]),
            K::Chain | K::Zip => self.trusted_len(a[0]) && self.trusted_len(a[1]),
            K::Skip | K::StepBy => self.tra(a[0]),
            K::Filter | K::FilterMap | K::TakeWhile | K::SkipWhile | K::Inspect => false,
        }
    }

    // ---------- Consumers ----------

    /// One pull for a consumer loop: `t = it.next()`, then (some, none)
    /// with the item moved into a fresh local on the some side.
    fn pull(&mut self, itp: &Place, ty: Ty) -> Result<(Bb, Bb, Local, Ty), String> {
        let item = self.item(ty)?;
        let opt = self.body.tys.mk_option(item);
        let t = self.local(opt);
        self.next(itp.clone(), ty, Place::local(t), false)?;
        let (s, n) = self.switch_opt(&Place::local(t));
        self.cur = s;
        let x = self.local(item);
        let px = self.take(Self::payload(&Place::local(t)), item);
        self.assign(Place::local(x), Rvalue::Use(px));
        Ok((self.cur, n, x, item))
    }

    /// Internal iteration (Rust's `fold`, which `count`, `sum`,
    /// `for_each`, `last`, `max`, and `collect`'s trusted-length path
    /// use): `k` consumes each item local. It differs from a `next`
    /// loop only through a `Zip` of two `TrustedLen` sides, which folds
    /// exactly `min` pairs; the adapters Rust delegates `fold` through
    /// are followed down to it.
    fn each(&mut self, itp: &Place, ty: Ty, k: &mut dyn FnMut(&mut Self, Local, Ty) -> R) -> R {
        use IterKind as K;
        if !self.fold_differs(ty) {
            let lp = self.block();
            self.goto(lp);
            self.cur = lp;
            let (_, n, x, item) = self.pull(itp, ty)?;
            k(self, x, item)?;
            self.goto(lp);
            self.cur = n;
            return Ok(());
        }
        let (kd, a) = self.kind_args(ty).ok_or("iterator expansion: fold of a non-iterator")?;
        let f = |i: u32| itp.project(Proj::Field(i));
        let item = self.item(ty)?;
        match kd {
            K::Map | K::Inspect | K::Filter | K::FilterMap => {
                let fty = a[1];
                self.each(&f(0), a[0], &mut |this, x, xt| {
                    match kd {
                        K::Map => {
                            let y = this.local(item);
                            let ax = this.take(Place::local(x), xt);
                            this.call_fn(fty, f(1), vec![ax], Place::local(y))?;
                            k(this, y, item)
                        }
                        K::Inspect => {
                            let rx = this.ref_to(false, Place::local(x), xt);
                            let u = this.local(UNIT);
                            this.call_fn(fty, f(1), vec![Operand::Move(Place::local(rx))], Place::local(u))?;
                            k(this, x, xt)
                        }
                        K::Filter => {
                            let rx = this.ref_to(false, Place::local(x), xt);
                            let b = this.local(BOOL);
                            this.call_fn(fty, f(1), vec![Operand::Move(Place::local(rx))], Place::local(b))?;
                            let (yes, no) = this.branch(Operand::Copy(Place::local(b)));
                            let after = this.block();
                            this.cur = no;
                            this.drop_local(x);
                            this.goto(after);
                            this.cur = yes;
                            k(this, x, xt)?;
                            this.goto(after);
                            this.cur = after;
                            Ok(())
                        }
                        _ => {
                            let opt = this.body.tys.mk_option(item);
                            let o = this.local(opt);
                            let ax = this.take(Place::local(x), xt);
                            this.call_fn(fty, f(1), vec![ax], Place::local(o))?;
                            let (hit, miss) = this.switch_opt(&Place::local(o));
                            let after = this.block();
                            this.cur = miss;
                            this.goto(after);
                            this.cur = hit;
                            let y = this.local(item);
                            let py = this.take(Self::payload(&Place::local(o)), item);
                            this.assign(Place::local(y), Rvalue::Use(py));
                            k(this, y, item)?;
                            this.goto(after);
                            this.cur = after;
                            Ok(())
                        }
                    }
                })
            }
            K::Copied | K::Cloned => self.each(&f(0), a[0], &mut |this, r, _| {
                let y = this.local(item);
                if kd == K::Copied {
                    this.assign(Place::local(y), Rvalue::Use(Operand::Copy(Place::local(r).deref())));
                } else {
                    this.call_builtin(Builtin::Clone, vec![Operand::Copy(Place::local(r))], Place::local(y));
                }
                k(this, y, item)
            }),
            K::Enumerate => self.each(&f(0), a[0], &mut |this, x, xt| {
                let i = this.local(USIZE);
                this.assign(Place::local(i), Rvalue::Use(Operand::Copy(f(1))));
                this.assign(f(1), Rvalue::Bin(crate::ast::BinOp::Add, Operand::Copy(f(1)), Self::usize_c(1)));
                let ax = this.take(Place::local(x), xt);
                let tup = this.local(item);
                this.assign(Place::local(tup), Rvalue::TupleAgg(item, vec![Operand::Copy(Place::local(i)), ax]));
                k(this, tup, item)
            }),
            K::Peekable => {
                let slot = f(1);
                let done = self.block();
                let go = self.block();
                let (full, empty) = self.switch_opt(&slot);
                self.cur = empty;
                self.goto(go);
                self.cur = full;
                let (some, none) = self.switch_opt(&Self::payload(&slot));
                self.cur = none;
                self.goto(done);
                self.cur = some;
                let v = self.local(item);
                let pv = self.take(Self::payload(&Self::payload(&slot)), item);
                self.assign(Place::local(v), Rvalue::Use(pv));
                let sty = self.place_ty(&slot)?;
                self.none(&slot, sty);
                k(self, v, item)?;
                self.goto(go);
                self.cur = go;
                self.each(&f(0), a[0], k)?;
                self.goto(done);
                self.cur = done;
                Ok(())
            }
            K::SkipWhile => {
                let done = self.block();
                let go = self.block();
                let (flagged, open) = self.branch(Operand::Copy(f(1)));
                self.cur = flagged;
                self.goto(go);
                self.cur = open;
                let opt = self.body.tys.mk_option(item);
                let t = self.local(opt);
                self.next(itp.clone(), ty, Place::local(t), false)?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = n;
                self.goto(done);
                self.cur = s;
                let v = self.local(item);
                let pv = self.take(Self::payload(&Place::local(t)), item);
                self.assign(Place::local(v), Rvalue::Use(pv));
                k(self, v, item)?;
                self.goto(go);
                self.cur = go;
                self.each(&f(0), a[0], k)?;
                self.goto(done);
                self.cur = done;
                Ok(())
            }
            K::Skip => {
                use crate::ast::BinOp::*;
                let done = self.block();
                let go = self.block();
                let c = self.cmp(Lt, Self::usize_c(0), Operand::Copy(f(1)));
                let (skip, plain) = self.branch(c);
                self.cur = plain;
                self.goto(go);
                self.cur = skip;
                let n1 = self.local(USIZE);
                self.assign(Place::local(n1), Rvalue::Bin(Sub, Operand::Copy(f(1)), Self::usize_c(1)));
                let opt = self.body.tys.mk_option(item);
                let t = self.local(opt);
                self.nth(f(0), a[0], n1, Place::local(t))?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = n;
                self.goto(done);
                self.cur = s;
                self.drop_local(t);
                self.goto(go);
                self.cur = go;
                self.each(&f(0), a[0], k)?;
                self.goto(done);
                self.cur = done;
                Ok(())
            }
            K::Chain => {
                // `a.fold` then `b.fold`: each side is consumed (and
                // dropped) when its fold returns.
                for side in [0u32, 1] {
                    let next_side = self.block();
                    let (s, n) = self.switch_opt(&f(side));
                    self.cur = n;
                    self.goto(next_side);
                    self.cur = s;
                    self.each(&Self::payload(&f(side)), a[side as usize], k)?;
                    let sty = self.place_ty(&f(side))?;
                    self.none(&f(side), sty);
                    self.goto(next_side);
                    self.cur = next_side;
                }
                Ok(())
            }
            K::Zip => {
                // `SpecFold` for two `TrustedLen` sides: `upper` pairs
                // per round, no `None` checks, then stop unless the
                // upper bound was unknown.
                let (ia, ib) = (self.item(a[0])?, self.item(a[1])?);
                let round = self.block();
                self.goto(round);
                self.cur = round;
                let (_, hi) = self.hint(itp.clone(), ty)?;
                let (upper, more) = (self.local(USIZE), self.local(BOOL));
                let (known, unknown) = self.switch_opt(&Place::local(hi));
                let go = self.block();
                self.cur = known;
                self.assign(Place::local(upper), Rvalue::Use(Operand::Copy(Self::payload(&Place::local(hi)))));
                self.assign(Place::local(more), Rvalue::Use(Operand::Const(Const::Bool(false))));
                self.goto(go);
                self.cur = unknown;
                self.assign(Place::local(upper), Rvalue::Use(Self::usize_c(u64::MAX)));
                self.assign(Place::local(more), Rvalue::Use(Operand::Const(Const::Bool(true))));
                self.goto(go);
                self.cur = go;
                let i = self.local(USIZE);
                self.assign(Place::local(i), Rvalue::Use(Self::usize_c(0)));
                let lp = self.block();
                self.goto(lp);
                self.cur = lp;
                let c = self.cmp(crate::ast::BinOp::Lt, Operand::Copy(Place::local(i)), Operand::Copy(Place::local(upper)));
                let (body, end) = self.branch(c);
                self.cur = body;
                self.assign(Place::local(i), Rvalue::Bin(crate::ast::BinOp::Add, Operand::Copy(Place::local(i)), Self::usize_c(1)));
                let (oa, ob) = (self.body.tys.mk_option(ia), self.body.tys.mk_option(ib));
                let (ta, tb) = (self.local(oa), self.local(ob));
                self.next(f(0), a[0], Place::local(ta), false)?;
                self.next(f(1), a[1], Place::local(tb), false)?;
                let px = self.take(Self::payload(&Place::local(ta)), ia);
                let py = self.take(Self::payload(&Place::local(tb)), ib);
                let tup = self.local(item);
                self.assign(Place::local(tup), Rvalue::TupleAgg(item, vec![px, py]));
                k(self, tup, item)?;
                self.goto(lp);
                self.cur = end;
                let fin = self.block();
                let (again, stop) = self.branch(Operand::Copy(Place::local(more)));
                self.cur = again;
                self.goto(round);
                self.cur = stop;
                self.goto(fin);
                self.cur = fin;
                Ok(())
            }
            _ => Err("iterator expansion: fold path for this kind".into()),
        }
    }

    /// True when `fold` over this type pulls differently from a `next`
    /// loop (see `each`).
    fn fold_differs(&self, ty: Ty) -> bool {
        use IterKind as K;
        let Some((k, a)) = self.kind_args(ty) else { return false };
        match k {
            K::Zip => self.trusted_len(a[0]) && self.trusted_len(a[1]) && !(self.tra(a[0]) && self.tra(a[1])),
            K::Map | K::Filter | K::FilterMap | K::Inspect | K::Copied | K::Cloned | K::Enumerate | K::Peekable | K::SkipWhile | K::Skip => {
                self.fold_differs(a[0])
            }
            K::Chain => self.fold_differs(a[0]) || self.fold_differs(a[1]),
            _ => false,
        }
    }

    fn count(&mut self, itp: Place, ty: Ty, dest: Place) -> R {
        let c = self.local(USIZE);
        self.assign(Place::local(c), Rvalue::Use(Self::usize_c(0)));
        self.each(&itp, ty, &mut |this, x, _| {
            this.drop_local(x);
            this.assign(Place::local(c), Rvalue::Bin(crate::ast::BinOp::Add, Operand::Copy(Place::local(c)), Self::usize_c(1)));
            Ok(())
        })?;
        self.assign(dest, Rvalue::Use(Operand::Copy(Place::local(c))));
        Ok(())
    }

    fn last(&mut self, itp: Place, ty: Ty, dest: Place, dest_ty: Ty) -> R {
        let l = self.local(dest_ty);
        self.none(&Place::local(l), dest_ty);
        self.each(&itp, ty, &mut |this, x, item| {
            let ax = this.take(Place::local(x), item);
            this.some(&Place::local(l), dest_ty, ax);
            Ok(())
        })?;
        self.assign(dest, Rvalue::Use(Operand::Move(Place::local(l))));
        Ok(())
    }

    fn for_each(&mut self, itp: Place, ty: Ty, fpl: Place, fty: Ty) -> R {
        self.each(&itp, ty, &mut |this, x, item| {
            let ax = this.take(Place::local(x), item);
            let u = this.local(UNIT);
            this.call_fn(fty, fpl.clone(), vec![ax], Place::local(u))
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn fold(&mut self, itp: Place, ty: Ty, init: Operand, fpl: Place, fty: Ty, dest: Place, dest_ty: Ty) -> R {
        let acc = self.local(dest_ty);
        self.assign(Place::local(acc), Rvalue::Use(init));
        self.each(&itp, ty, &mut |this, x, item| {
            let aa = this.take(Place::local(acc), dest_ty);
            let ax = this.take(Place::local(x), item);
            let next = this.local(dest_ty);
            this.call_fn(fty, fpl.clone(), vec![aa, ax], Place::local(next))?;
            let an = this.take(Place::local(next), dest_ty);
            this.assign(Place::local(acc), Rvalue::Use(an));
            Ok(())
        })?;
        let aa = self.take(Place::local(acc), dest_ty);
        self.assign(dest, Rvalue::Use(aa));
        Ok(())
    }

    /// `any`, `all`, `find`, `find_map`, and `position`: pull until the
    /// closure decides, then stop (the rest stays in the iterator).
    #[allow(clippy::too_many_arguments)]
    fn search(&mut self, b: Builtin, itp: Place, ty: Ty, fpl: Place, fty: Ty, dest: Place, dest_ty: Ty) -> R {
        use Builtin as B;
        let join = self.block();
        let pos = self.local(USIZE);
        self.assign(Place::local(pos), Rvalue::Use(Self::usize_c(0)));
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        let (_, n, x, item) = self.pull(&itp, ty)?;
        match b {
            B::IterAny | B::IterAll => {
                let ax = self.take(Place::local(x), item);
                let r = self.local(BOOL);
                self.call_fn(fty, fpl, vec![ax], Place::local(r))?;
                let (yes, no) = self.branch(Operand::Copy(Place::local(r)));
                let (stop, go) = if b == B::IterAny { (yes, no) } else { (no, yes) };
                self.cur = stop;
                self.assign(dest.clone(), Rvalue::Use(Operand::Const(Const::Bool(b == B::IterAny))));
                self.goto(join);
                self.cur = go;
                self.goto(lp);
                self.cur = n;
                self.assign(dest, Rvalue::Use(Operand::Const(Const::Bool(b == B::IterAll))));
            }
            B::IterFind => {
                let rx = self.ref_to(false, Place::local(x), item);
                let r = self.local(BOOL);
                self.call_fn(fty, fpl, vec![Operand::Move(Place::local(rx))], Place::local(r))?;
                let (yes, no) = self.branch(Operand::Copy(Place::local(r)));
                self.cur = yes;
                let ax = self.take(Place::local(x), item);
                self.some(&dest, dest_ty, ax);
                self.goto(join);
                self.cur = no;
                self.drop_local(x);
                self.goto(lp);
                self.cur = n;
                self.none(&dest, dest_ty);
            }
            B::IterFindMap => {
                let ax = self.take(Place::local(x), item);
                let o = self.local(dest_ty);
                self.call_fn(fty, fpl, vec![ax], Place::local(o))?;
                let (hit, miss) = self.switch_opt(&Place::local(o));
                self.cur = hit;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(o))));
                self.goto(join);
                self.cur = miss;
                self.goto(lp);
                self.cur = n;
                self.none(&dest, dest_ty);
            }
            _ => {
                let ax = self.take(Place::local(x), item);
                let r = self.local(BOOL);
                self.call_fn(fty, fpl, vec![ax], Place::local(r))?;
                let (yes, no) = self.branch(Operand::Copy(Place::local(r)));
                self.cur = yes;
                self.some(&dest, dest_ty, Operand::Copy(Place::local(pos)));
                self.goto(join);
                self.cur = no;
                self.assign(Place::local(pos), Rvalue::Bin(crate::ast::BinOp::Add, Operand::Copy(Place::local(pos)), Self::usize_c(1)));
                self.goto(lp);
                self.cur = n;
                self.none(&dest, dest_ty);
            }
        }
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// `sum` and `product`: a fold from 0 or 1 (`-0.0` and `1.0` for
    /// floats, as Rust 1.99 does), with checked arithmetic.
    fn sum(&mut self, product: bool, itp: Place, ty: Ty, dest: Place, dest_ty: Ty) -> R {
        let zero = match self.body.tys.kind(dest_ty) {
            TyKind::Int(i) => Const::Int(u128::from(product), i),
            TyKind::Float(fl) => {
                let v: f64 = if product { 1.0 } else { -0.0 };
                Const::Float(if fl == FloatTy::F32 { u64::from((v as f32).to_bits()) } else { v.to_bits() }, fl)
            }
            _ => return Err("iterator expansion: sum into a non-numeric type".into()),
        };
        let acc = self.local(dest_ty);
        self.assign(Place::local(acc), Rvalue::Use(Operand::Const(zero)));
        let op = if product { crate::ast::BinOp::Mul } else { crate::ast::BinOp::Add };
        self.each(&itp, ty, &mut |this, x, item| {
            let v = if matches!(this.body.tys.kind(item), TyKind::Ref(..)) { Place::local(x).deref() } else { Place::local(x) };
            this.assign(Place::local(acc), Rvalue::Bin(op, Operand::Copy(Place::local(acc)), Operand::Copy(v)));
            Ok(())
        })?;
        self.assign(dest, Rvalue::Use(Operand::Copy(Place::local(acc))));
        Ok(())
    }

    /// `min`/`max` (key None) and `min_by_key`/`max_by_key`: Rust's
    /// `reduce` over `cmp::max_by`/`min_by`, so `max` keeps the last of
    /// equal items and `min` the first; the loser drops at once.
    #[allow(clippy::too_many_arguments)]
    fn min_max(&mut self, max: bool, itp: Place, ty: Ty, key: Option<(Place, Ty)>, dest: Place, dest_ty: Ty) -> R {
        let item = self.item(ty)?;
        let join = self.block();
        // `reduce`: the first item by `next`, the rest by `fold`.
        let (_, n, first, _) = self.pull(&itp, ty)?;
        let best = self.local(item);
        let a0 = self.take(Place::local(first), item);
        self.assign(Place::local(best), Rvalue::Use(a0));
        let key_ty = match &key {
            Some((fpl, fty)) => {
                let kt = self.closure_output(*fty)?;
                Some((fpl.clone(), *fty, kt))
            }
            None => None,
        };
        let best_key = match &key_ty {
            Some((fpl, fty, kt)) => {
                let k = self.local(*kt);
                let rb = self.ref_to(false, Place::local(best), item);
                self.call_fn(*fty, fpl.clone(), vec![Operand::Move(Place::local(rb))], Place::local(k))?;
                Some(k)
            }
            None => None,
        };
        self.each(&itp, ty, &mut |this, x, _| {
            let x_key = match &key_ty {
                Some((fpl, fty, kt)) => {
                    let k = this.local(*kt);
                    let rx = this.ref_to(false, Place::local(x), item);
                    this.call_fn(*fty, fpl.clone(), vec![Operand::Move(Place::local(rx))], Place::local(k))?;
                    Some(k)
                }
                None => None,
            };
            // `max_by(best, x)`: x wins unless best > x; `min_by`: x
            // wins only if best > x. The loser drops, key first.
            let (lhs, rhs, ct) = match (best_key, x_key, &key_ty) {
                (Some(bk), Some(xk), Some((_, _, kt))) => (Place::local(bk), Place::local(xk), *kt),
                _ => (Place::local(best), Place::local(x), item),
            };
            let gt = this.greater(lhs, rhs, ct)?;
            let (best_gt, best_le) = this.branch(gt);
            let (keep_best, take_x) = if max { (best_gt, best_le) } else { (best_le, best_gt) };
            let after = this.block();
            this.cur = keep_best;
            if let Some(xk) = x_key {
                this.drop_local(xk);
            }
            this.drop_local(x);
            this.goto(after);
            this.cur = take_x;
            if let (Some(bk), Some(xk)) = (best_key, x_key) {
                let kt = key_ty.as_ref().map(|k| k.2).unwrap_or(ERROR);
                this.drop_local(bk);
                let ak = this.take(Place::local(xk), kt);
                this.assign(Place::local(bk), Rvalue::Use(ak));
            }
            this.drop_local(best);
            let ax = this.take(Place::local(x), item);
            this.assign(Place::local(best), Rvalue::Use(ax));
            this.goto(after);
            this.cur = after;
            Ok(())
        })?;
        if let Some(bk) = best_key {
            self.drop_local(bk);
        }
        let ab = self.take(Place::local(best), item);
        self.some(&dest, dest_ty, ab);
        self.goto(join);
        self.cur = n;
        self.none(&dest, dest_ty);
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// The output type of a closure type.
    fn closure_output(&self, fty: Ty) -> Result<Ty, String> {
        let TyKind::Closure(def, _) = self.body.tys.kind(fty) else { return Err("iterator expansion: key fn is not a closure".into()) };
        self.p.gx.closures.get(&def).map(|e| e.output).ok_or_else(|| "iterator expansion: closure not registered".into())
    }

    /// A bool operand for `a > b` over an `Ord` type lust compares
    /// (check/iter.rs `has_total_ord`): scalars and strings, through
    /// references, and tuples lexicographically.
    fn greater(&mut self, a: Place, b: Place, ty: Ty) -> Result<Operand, String> {
        use crate::ast::BinOp::*;
        match self.body.tys.kind(ty) {
            TyKind::Int(_) | TyKind::Bool | TyKind::Char => Ok(self.cmp(Gt, Operand::Copy(a), Operand::Copy(b))),
            TyKind::Unit => Ok(Operand::Const(Const::Bool(false))),
            TyKind::Ref(_, _, inner) => {
                if inner == STR {
                    let c = self.local(BOOL);
                    self.assign(Place::local(c), Rvalue::StrCmp(Gt, Operand::Copy(a), Operand::Copy(b)));
                    return Ok(Operand::Copy(Place::local(c)));
                }
                self.greater(a.deref(), b.deref(), inner)
            }
            TyKind::Tuple(ts) => {
                // First field that differs decides; all equal is not >.
                let elems: Vec<Ty> = self.body.tys.tys_of(ts).to_vec();
                let out = self.local(BOOL);
                let join = self.block();
                for (i, &e) in elems.iter().enumerate() {
                    let (fa, fb) = (a.project(Proj::Field(i as u32)), b.project(Proj::Field(i as u32)));
                    let g = self.greater(fa.clone(), fb.clone(), e)?;
                    let (yes, no) = self.branch(g);
                    self.cur = yes;
                    self.assign(Place::local(out), Rvalue::Use(Operand::Const(Const::Bool(true))));
                    self.goto(join);
                    self.cur = no;
                    let l = self.greater(fb, fa, e)?;
                    let (less, eq) = self.branch(l);
                    self.cur = less;
                    self.assign(Place::local(out), Rvalue::Use(Operand::Const(Const::Bool(false))));
                    self.goto(join);
                    self.cur = eq;
                }
                self.assign(Place::local(out), Rvalue::Use(Operand::Const(Const::Bool(false))));
                self.goto(join);
                self.cur = join;
                Ok(Operand::Copy(Place::local(out)))
            }
            _ if self.body.tys.is_string_ty(ty) => {
                let (ra, rb) = (self.ref_to(false, a, ty), self.ref_to(false, b, ty));
                let (sa, sb) = (self.local(REF_STR), self.local(REF_STR));
                self.call_builtin(Builtin::StringAsStr, vec![Operand::Copy(Place::local(ra))], Place::local(sa));
                self.call_builtin(Builtin::StringAsStr, vec![Operand::Copy(Place::local(rb))], Place::local(sb));
                let c = self.local(BOOL);
                self.assign(Place::local(c), Rvalue::StrCmp(Gt, Operand::Copy(Place::local(sa)), Operand::Copy(Place::local(sb))));
                Ok(Operand::Copy(Place::local(c)))
            }
            _ => Err("iterator expansion: cannot compare this item type".into()),
        }
    }

    /// `collect` into `Vec<T>` (Rust's `SpecFromIter` capacity rules)
    /// or `String` (the `FromIterator` impl per item type).
    fn collect(&mut self, itp: Place, ty: Ty, dest: Place, dest_ty: Ty) -> R {
        use crate::ast::BinOp::*;
        let item = self.item(ty)?;
        let join = self.block();
        if self.body.tys.is_string_ty(dest_ty) {
            let s = self.local(STRING);
            let push = |this: &mut Self, s: Local, x: Local, item: Ty| -> R {
                let rs = this.ref_to(true, Place::local(s), STRING);
                let u = this.local(UNIT);
                let it = this.body.tys.kind(item);
                if item == CHAR {
                    this.call_builtin(Builtin::StringPush, vec![Operand::Move(Place::local(rs)), Operand::Copy(Place::local(x))], Place::local(u));
                } else if matches!(it, TyKind::Ref(_, _, c) if c == CHAR) {
                    this.call_builtin(
                        Builtin::StringPush,
                        vec![Operand::Move(Place::local(rs)), Operand::Copy(Place::local(x).deref())],
                        Place::local(u),
                    );
                } else if item == REF_STR {
                    this.call_builtin(Builtin::StringPushStr, vec![Operand::Move(Place::local(rs)), Operand::Copy(Place::local(x))], Place::local(u));
                } else {
                    let rx = this.ref_to(false, Place::local(x), STRING);
                    let sx = this.local(REF_STR);
                    this.call_builtin(Builtin::StringAsStr, vec![Operand::Copy(Place::local(rx))], Place::local(sx));
                    this.call_builtin(Builtin::StringPushStr, vec![Operand::Move(Place::local(rs)), Operand::Copy(Place::local(sx))], Place::local(u));
                    this.drop_local(x);
                }
                Ok(())
            };
            if item == STRING {
                // The first String is the buffer; the rest append.
                let (_, n, first, _) = self.pull(&itp, ty)?;
                self.assign(Place::local(s), Rvalue::Use(Operand::Move(Place::local(first))));
                self.each(&itp, ty, &mut |this, x, item| push(this, s, x, item))?;
                self.goto(join);
                self.cur = n;
                self.call_builtin(Builtin::StringNew, vec![], Place::local(s));
                self.goto(join);
            } else {
                self.call_builtin(Builtin::StringNew, vec![], Place::local(s));
                if item == CHAR || matches!(self.body.tys.kind(item), TyKind::Ref(_, _, c) if c == CHAR) {
                    // `Extend<char>` reserves the lower bound first.
                    let (lo, _) = self.hint(itp.clone(), ty)?;
                    let rs = self.ref_to(true, Place::local(s), STRING);
                    let u = self.local(UNIT);
                    self.call_builtin(Builtin::StringReserve, vec![Operand::Move(Place::local(rs)), Operand::Copy(Place::local(lo))], Place::local(u));
                }
                self.each(&itp, ty, &mut |this, x, item| push(this, s, x, item))?;
                self.goto(join);
            }
            self.cur = join;
            self.assign(dest, Rvalue::Use(Operand::Move(Place::local(s))));
            return Ok(());
        }
        let Some(elem) = self.body.tys.vec_elem(dest_ty) else { return Err("iterator expansion: collect into an unsupported type".into()) };
        let v = self.local(dest_ty);
        let with_capacity = |this: &mut Self, cap: Operand| {
            this.assign(Place::local(v), Rvalue::VecLit(elem, Vec::new()));
            let rv = this.ref_to(true, Place::local(v), dest_ty);
            let u = this.local(UNIT);
            this.call_builtin(Builtin::VecReserveExact, vec![Operand::Move(Place::local(rv)), cap], Place::local(u));
        };
        let push = |this: &mut Self, x: Local| {
            let rv = this.ref_to(true, Place::local(v), dest_ty);
            let u = this.local(UNIT);
            let ax = this.take(Place::local(x), elem);
            this.call_builtin(Builtin::VecPush, vec![Operand::Move(Place::local(rv)), ax], Place::local(u));
        };
        if self.trusted_len(ty) {
            // `with_capacity(upper)`, then every item fits.
            let (_, hi) = self.hint(itp.clone(), ty)?;
            let (s, n) = self.switch_opt(&Place::local(hi));
            self.cur = n;
            self.term(Terminator::Panic(vec![FmtPart::Lit("capacity overflow".into())]));
            self.cur = s;
            with_capacity(self, Operand::Copy(Self::payload(&Place::local(hi))));
            // `extend_trusted` writes through `for_each`, so a fold.
            self.each(&itp, ty, &mut |this, x, _| {
                push(this, x);
                Ok(())
            })?;
            self.goto(join);
        } else {
            // First item, then `max(MIN_NON_ZERO_CAP, lower + 1)`, then
            // `extend_desugared`: reserve `lower + 1` whenever full.
            let (_, n, first, _) = self.pull(&itp, ty)?;
            let (lo, _) = self.hint(itp.clone(), ty)?;
            let l1 = self.local(USIZE);
            self.call_builtin(Builtin::SaturatingAdd, vec![Operand::Copy(Place::local(lo)), Self::usize_c(1)], Place::local(l1));
            let cap = self.local(USIZE);
            let min_cap = self.min_non_zero_cap(elem)?;
            self.call_builtin(Builtin::Max, vec![Self::usize_c(min_cap), Operand::Copy(Place::local(l1))], Place::local(cap));
            with_capacity(self, Operand::Copy(Place::local(cap)));
            push(self, first);
            let lp = self.block();
            self.goto(lp);
            self.cur = n;
            self.assign(Place::local(v), Rvalue::VecLit(elem, Vec::new()));
            self.goto(join);
            self.cur = lp;
            let (_, n2, x, _) = self.pull(&itp, ty)?;
            let rv = self.ref_to(false, Place::local(v), dest_ty);
            let (len, capn) = (self.local(USIZE), self.local(USIZE));
            self.call_builtin(Builtin::VecLen, vec![Operand::Copy(Place::local(rv))], Place::local(len));
            self.call_builtin(Builtin::VecCapacity, vec![Operand::Copy(Place::local(rv))], Place::local(capn));
            let full = self.cmp(Eq, Operand::Copy(Place::local(len)), Operand::Copy(Place::local(capn)));
            let (grow, ok) = self.branch(full);
            self.cur = grow;
            let (lo2, _) = self.hint(itp.clone(), ty)?;
            let add = self.local(USIZE);
            self.call_builtin(Builtin::SaturatingAdd, vec![Operand::Copy(Place::local(lo2)), Self::usize_c(1)], Place::local(add));
            let rvm = self.ref_to(true, Place::local(v), dest_ty);
            let u = self.local(UNIT);
            self.call_builtin(Builtin::VecReserve, vec![Operand::Move(Place::local(rvm)), Operand::Copy(Place::local(add))], Place::local(u));
            self.goto(ok);
            self.cur = ok;
            push(self, x);
            self.goto(lp);
            self.cur = n2;
            self.goto(join);
        }
        self.cur = join;
        self.assign(dest, Rvalue::Use(Operand::Move(Place::local(v))));
        Ok(())
    }

    /// `RawVec::MIN_NON_ZERO_CAP` for an element type: 8 for 1-byte
    /// elements, 4 up to 1024 bytes, else 1.
    fn min_non_zero_cap(&self, elem: Ty) -> Result<u64, String> {
        let l = crate::ty::layout::layout_of_ty(&self.body.tys, self.p, elem).map_err(|_| "iterator expansion: element layout unknown".to_string())?;
        Ok(if l.size == 1 {
            8
        } else if l.size <= 1024 {
            4
        } else {
            1
        })
    }
}
