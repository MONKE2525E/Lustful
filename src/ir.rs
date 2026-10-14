// Lust IR: a small control-flow graph per function, in the style of Rust's MIR but flatter.
// The borrow checker and the C backend both read it.
use crate::ast::{BinOp, FmtSpec, UnOp};
use crate::check::Builtin;
use crate::def::LocalDefId;
use crate::diag::Span;
use crate::driver::graph::Reads;
use crate::ty::{AdtId, IntTy, Ty, Tys};

pub type Local = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Bb(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Proj {
    Deref,
    Field(u32),
    /// View an enum place as one variant, so `Field` can address that variant's fields.
    Downcast(u32),
    /// Bounds-checked Vec element. The index is in a local of type usize.
    Index(Local),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Place {
    pub local: Local,
    pub proj: Vec<Proj>,
}

impl Place {
    pub fn local(l: Local) -> Place {
        Place { local: l, proj: Vec::new() }
    }
    pub fn project(&self, p: Proj) -> Place {
        let mut proj = self.proj.clone();
        proj.push(p);
        Place { local: self.local, proj }
    }
    pub fn deref(&self) -> Place {
        self.project(Proj::Deref)
    }
}

#[derive(Clone, Debug)]
pub enum Const {
    Int(u128, IntTy),
    /// A float literal as bits (`f32` bits zero-extended).
    Float(u64, crate::ty::FloatTy),
    Bool(bool),
    Char(char),
    /// Index into the AST string table.
    Str(u32),
    Unit,
}

#[derive(Clone, Debug)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Const(Const),
}

/// One piece of a format string. `Arg` holds a reference to the value and the value's type.
#[derive(Clone, Debug)]
pub enum FmtPart {
    Lit(String),
    Arg { value: Operand, ty: Ty, debug: bool, spec: FmtSpec },
}

#[derive(Clone, Debug)]
pub enum Rvalue {
    Use(Operand),
    Ref(bool, Place),
    /// Integer arithmetic (checked in dev builds), bit operations, and scalar comparisons.
    Bin(BinOp, Operand, Operand),
    Un(UnOp, Operand),
    Cast(Operand, Ty),
    Aggregate(AdtId, u32, Vec<Operand>),
    /// `Some(x)` or `None`, of the given Option type.
    Opt(Ty, Option<Operand>),
    /// `Ok(x)` (true) or `Err(x)` (false), of the given Result type.
    Res(Ty, bool, Operand),
    VecLit(Ty, Vec<Operand>),
    VecRepeat(Ty, Operand, Operand),
    /// `a == b` for any PartialEq type. Both operands are references to `ty`.
    Eq {
        a: Operand,
        b: Operand,
        ty: Ty,
        ne: bool,
    },
    /// `a < b` (and `<=`, `>`, `>=`) for a type that orders by
    /// structure (`check::has_ord`). Both operands are references to
    /// `ty`; codegen compares through the `cmp` glue.
    Cmp {
        op: BinOp,
        a: Operand,
        b: Operand,
        ty: Ty,
    },
    /// String comparison. Both operands are `&str`.
    StrCmp(BinOp, Operand, Operand),
    /// `String + &str`.
    StringAdd(Operand, Operand),
    Format(Vec<FmtPart>),
    Discriminant(Place),
    /// A tuple value of the given type from its elements, in order (W-CORELANG, wave A).
    TupleAgg(Ty, Vec<Operand>),
    /// An array value of the given type from its elements, in order (W-CORELANG, wave A).
    /// Array repeat of a Copy element lowers to `ArrayRepeat` instead.
    ArrayAgg(Ty, Vec<Operand>),
    /// `[value; len]` of the given array type for a Copy element with len
    /// above 1 (W-CORELANG, wave A).
    ArrayRepeat(Ty, Operand, u64),
    /// A fat slice value over the whole of an array, Vec, or slice place
    /// (W-CORELANG, wave A). The result type is a slice reference type.
    SliceOf(Place),
    /// A fat slice value over a range of an array, Vec, or slice place.
    /// `hi` is the end operand when written; `inclusive` marks `..=` so the
    /// runtime helper can reject an overflowing end (W-CORELANG, wave A).
    Subslice {
        base: Place,
        lo: Operand,
        hi: Option<Operand>,
        inclusive: bool,
        /// True when the slice place is used mutably (`&mut a[..]`, a write).
        mutable: bool,
    },
    /// The element count of an array, slice, or Vec place (W-CORELANG, wave A).
    LenOf(Place),
    /// A copy of a static item's value, by index into `Program::statics`.
    StaticLoad(u32),
    /// The address of a static item, by index into `Program::statics`.
    StaticRef(u32),
    /// A function item used as a value, of the given result type: the
    /// zero-sized `FnDef`, or `FnPtr` when the use coerces it (codegen
    /// then yields the slot trampoline address). Proposed by W-CGEN
    /// for W-CORELANG's fn-pointer lowering.
    FnValue(LocalDefId, Ty),
    /// A dyn reference from a thin one (ARCH 2.8): `ptr` is `&T` or
    /// `&mut T`, `src` is `T`, and `dyn_ty` the target dyn type. The
    /// result pairs the data pointer with the vtable of (`src`, the dyn
    /// principal), which mono built and codegen emits. `ptr` may also
    /// be a moved `Box<T>` or `Rc<T>`: the result is then the owning
    /// `Box<dyn Tr>` or `Rc<dyn Tr>`, whose data pointer points at the
    /// value (inside the Rc allocation, after its two counts).
    MakeDyn { ptr: Operand, src: Ty, dyn_ty: Ty },
    /// Trait upcasting: the same data pointer, with the vtable reached
    /// by loading each super slot word index in `path` in turn.
    DynUpcast { ptr: Operand, path: Vec<u32> },
    /// One header word of a dyn reference's vtable as a `usize`: the
    /// size or the align of the value behind it (`size_of_val` and
    /// `align_of_val` on a dyn value; word indexes in `check::object`).
    DynMeta { ptr: Operand, word: u32 },
    /// `dst.write_fmt(format_args!(..))` (W-STD-B): formats the parts
    /// into `dst` (a `&mut Formatter` or `&mut String`) with a fresh
    /// Formatter over its sink, stopping at the first error; the value
    /// is the `fmt::Result`.
    WriteFmt(Operand, Vec<FmtPart>),
}

#[derive(Clone, Debug)]
pub enum StmtKind {
    Assign(Place, Rvalue),
    /// Drops the local if its drop flag says it still owns a value.
    Drop(Local),
    StorageDead(Local),
    /// A use that only the borrow checker sees. Keeps a two-phase reservation alive.
    FakeRead(Local),
    Print {
        stderr: bool,
        newline: bool,
        parts: Vec<FmtPart>,
    },
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

/// What a `Call` terminator calls: a user fn or method by local def, or a
/// builtin operation. Frozen with the `Call` terminator (docs/ARCH.md
/// section 9.2): new target forms go at the end only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CallTarget {
    Fn(LocalDefId),
    Builtin(Builtin),
    /// A registry intrinsic by id (`ty::lang::INTRINSICS`, S5): one target
    /// for the whole family; codegen emits the row's C symbol with the
    /// row's signature.
    Intrinsic(u32),
    /// A call through the function pointer value held in this local.
    /// The local's type is the `FnPtr` signature; `args` are the call
    /// arguments only. Proposed by W-CGEN for W-CORELANG.
    Indirect(Local),
    /// A call through a vtable (ARCH 2.8): `args[0]` is the dyn
    /// receiver (`&dyn Tr` or `&mut dyn Tr`, a fat pointer), and the
    /// payload is the method's word index in that receiver's vtable.
    /// The callee gets the data pointer, then `args[1..]`.
    Dyn(u32),
}

#[derive(Clone, Debug)]
pub enum Terminator {
    Goto(Bb),
    If(Operand, Bb, Bb),
    /// Jumps on an enum discriminant.
    Switch(Operand, Vec<(u32, Bb)>, Bb),
    /// A call: writes its result to `dest`, then continues at `next`.
    /// `unwind` is the cleanup successor for a panic in the callee
    /// (docs/ARCH.md section 7.2); it is `None` everywhere until W-PANIC
    /// builds cleanup edges. Calls are terminators, never rvalues, so
    /// every call already has its unwind slot.
    Call {
        target: CallTarget,
        args: Vec<Operand>,
        dest: Place,
        next: Bb,
        unwind: Option<Bb>,
    },
    Return,
    Unreachable,
    Panic(Vec<FmtPart>),
}

#[derive(Clone, Debug)]
pub struct BlockData {
    pub stmts: Vec<Stmt>,
    pub term: Terminator,
    pub term_span: Span,
}

#[derive(Clone, Debug)]
pub struct LocalDecl {
    pub ty: Ty,
    pub mutable: bool,
    /// User-visible name, for error messages. Temporaries have none.
    pub name: Option<String>,
}

/// Local 0 is the return value. Locals `1..=arg_count` are the parameters.
pub struct Body<'g> {
    pub fn_id: LocalDefId,
    pub tys: Tys<'g>,
    pub locals: Vec<LocalDecl>,
    pub blocks: Vec<BlockData>,
    pub arg_count: usize,
    #[allow(dead_code)] // Read by invalidation when it lands (W-DRIVER).
    /// The cross-item reads recorded while this body was checked
    /// (docs/ARCH.md section 8.2). Carried with the body result so the
    /// driver can store it with the checked body; record-only today.
    pub reads: Reads,
    /// Errors lowering found (a closure body place that no capture
    /// covers). Borrow checking reports them first; such a body is
    /// never generated.
    pub lower_errs: Vec<crate::diag::Diag>,
    /// `let` annotations with explicit lifetimes (W-BORROW): each local
    /// and the regioned type its annotation gives it. Borrowck relates
    /// the local's regions to it; a cached body has none (it is never
    /// borrow-checked again).
    pub annotations: Vec<(Local, Ty)>,
    /// Promoted temporaries (W-BORROW): the storage of a `&[]`, `&mut
    /// []`, or `&|..| ..` with no captures, which rustc promotes to
    /// `'static`. The value has no bytes, so such a local never dies and
    /// its borrows make no loan.
    pub promoted: Vec<Local>,
    /// The index temporaries of `a[i]` expressions. Borrowck never treats
    /// them as constant indexes (rustc's `Index`, not `ConstantIndex`):
    /// `arr[1]` reads the whole array for move checks. Only borrowck reads
    /// it; a cached body has none.
    pub index_exprs: Vec<Local>,
    /// Edges only borrowck sees, as rustc's `FalseEdge`: from the point
    /// where a match arm's pattern has matched (before its bindings) to
    /// the next arm's start, so arms after an irrefutable one are still
    /// checked. Codegen ignores them; a cached body has none.
    pub false_edges: Vec<(Bb, Bb)>,
}

impl Body<'_> {
    pub fn block(&self, b: Bb) -> &BlockData {
        &self.blocks[b.0 as usize]
    }
}
