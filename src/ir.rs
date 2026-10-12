// Lust IR: a small control-flow graph per function, in the style of Rust's MIR but flatter.
// The borrow checker and the C backend both read it.
use crate::ast::{BinOp, UnOp};
use crate::check::Builtin;
use crate::collect::FnId;
use crate::diag::Span;
use crate::types::{AdtId, IntTy, Ty, Tys};

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
    Int(u64, IntTy),
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
    VecLit(Ty, Vec<Operand>),
    VecRepeat(Ty, Operand, Operand),
    Call(FnId, Vec<Operand>),
    Builtin(Builtin, Vec<Operand>),
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

#[derive(Clone, Debug)]
pub enum Terminator {
    Goto(Bb),
    If(Operand, Bb, Bb),
    /// Jumps on an enum discriminant.
    Switch(Operand, Vec<(u32, Bb)>, Bb),
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
    pub fn_id: FnId,
    pub tys: Tys<'g>,
    pub locals: Vec<LocalDecl>,
    pub blocks: Vec<BlockData>,
    pub arg_count: usize,
}

impl Body<'_> {
    pub fn block(&self, b: Bb) -> &BlockData {
        &self.blocks[b.0 as usize]
    }
}
