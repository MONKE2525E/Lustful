// Lust IR: a small control-flow graph per function, in the style of Rust's MIR but flatter.
// The borrow checker and the C backend both read it.
use crate::ast::{BinOp, UnOp};
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
    Arg { value: Operand, ty: Ty, debug: bool },
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
}

impl Body<'_> {
    pub fn block(&self, b: Bb) -> &BlockData {
        &self.blocks[b.0 as usize]
    }
}
