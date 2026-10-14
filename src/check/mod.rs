// Type checking for one function body. Inference is local to the body: unification plus
// integer-literal variables. Output is a set of side tables that lowering reads.
// Signature collection runs before body checking, in `collect`.
pub mod any;
pub mod closure;
pub mod cells;
pub mod process;
pub mod utf8;
pub mod collect;
pub mod constfn;
pub mod convert;
pub mod defaults;
pub mod fmt;
pub mod generics;
pub mod iter;
pub mod method;
pub mod object;
pub mod obligations;
pub mod opaque;
pub mod picks;
pub mod platform;
pub mod project;
pub mod sized;
pub mod stdtypes;
pub mod usefulness;
pub mod sync;
pub mod variance;

use crate::ast::{self, BinOp, Expr, ExprId, FmtKind, FmtPiece, FmtSpec, ItemKind, MacroKind, Pat, PatId, Stmt, UnOp};
use crate::check::collect::*;
use crate::check::generics::Scope;
use crate::diag::{CtxtId, Diag, Span, not_yet, unsupported};
use crate::driver::graph::{BindingRes, Fingerprint, Head, Namespace, Reads, ReceiverForm, SigOf};
use crate::intern::{Interner, Sym};
use crate::traits::solve::{Selection, SolveCx, Solver};
use crate::ty::defs::DefKind as DefsKind;
use crate::ty::lang;
use crate::ty::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Autoref {
    None,
    Ref,
    RefMut,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Builtin {
    StringNew,
    StringFrom,
    StringWithCapacity,
    VecNew,
    VecWithCapacity,
    EnvArgs,
    ArgsCount,
    StrLen,
    StrIsEmpty,
    StrToString,
    StringLen,
    StringIsEmpty,
    StringPushStr,
    StringPush,
    StringAsStr,
    VecLen,
    VecIsEmpty,
    VecPush,
    Clone,
    ToString,
    WrappingAdd,
    WrappingSub,
    WrappingMul,
    WrappingDiv,
    WrappingRem,
    WrappingNeg,
    WrappingPow,
    WrappingShl,
    WrappingShr,
    WrappingAbs,
    CheckedAdd,
    CheckedSub,
    CheckedMul,
    CheckedDiv,
    CheckedRem,
    CheckedNeg,
    CheckedAbs,
    CheckedPow,
    CheckedShl,
    CheckedShr,
    SaturatingAdd,
    SaturatingSub,
    SaturatingMul,
    SaturatingDiv,
    SaturatingNeg,
    SaturatingAbs,
    SaturatingPow,
    OverflowingAdd,
    OverflowingSub,
    OverflowingMul,
    OverflowingDiv,
    OverflowingRem,
    OverflowingNeg,
    OverflowingAbs,
    OverflowingPow,
    OverflowingShl,
    OverflowingShr,
    CountOnes,
    CountZeros,
    LeadingZeros,
    TrailingZeros,
    LeadingOnes,
    TrailingOnes,
    RotateLeft,
    RotateRight,
    SwapBytes,
    ReverseBits,
    DivEuclid,
    RemEuclid,
    Signum,
    IsPositive,
    IsNegative,
    IsPowerOfTwo,
    FloatSqrt,
    FloatPowi,
    FloatPowf,
    FloatExp,
    FloatLn,
    FloatLog,
    FloatLog2,
    FloatLog10,
    FloatMulAdd,
    FloatFloor,
    FloatCeil,
    FloatRound,
    FloatTrunc,
    FloatFract,
    FloatAbs,
    FloatSignum,
    FloatRecip,
    FloatMin,
    FloatMax,
    FloatIsNan,
    FloatIsInfinite,
    FloatIsFinite,
    FloatIsSignPositive,
    FloatIsSignNegative,
    FloatToBits,
    FloatCopysign,
    F32FromBits,
    F64FromBits,
    CharLenUtf8,
    CharLenUtf16,
    CharIsAscii,
    CharIsAsciiPunctuation,
    CharIsAsciiGraphic,
    CharIsAsciiHexdigit,
    CharIsAsciiControl,
    CharIsDigitRadix,
    Abs,
    Pow,
    Min,
    Max,
    OptIsSome,
    OptIsNone,
    OptUnwrap,
    OptExpect,
    OptUnwrapOr,
    /// `Result` methods without closures (W-STD-A phase 3): a stopgap
    /// until the source std move of Option and Result.
    ResIsOk,
    ResIsErr,
    ResUnwrap,
    ResExpect,
    ResUnwrapErr,
    ResExpectErr,
    ResOk,
    ResErr,
    ResUnwrapOr,
    VecPop,
    VecGet,
    VecFirst,
    VecLast,
    VecContains,
    VecSwap,
    VecClear,
    VecInsert,
    VecRemove,
    VecTruncate,
    StrContains,
    StrStartsWith,
    StrEndsWith,
    StrTrim,
    StrToUppercase,
    StrToLowercase,
    StrChars,
    CharsNext,
    CharsCount,
    CharIsDigit,
    CharIsAlphabetic,
    CharIsAlphanumeric,
    CharIsWhitespace,
    CharIsUppercase,
    CharIsLowercase,
    // The Unicode forms of the char predicates (`is_alphabetic` and
    // friends; the variants above are the `is_ascii_*` forms).
    CharIsAlphabeticUnicode,
    CharIsNumericUnicode,
    CharIsAlphanumericUnicode,
    CharIsLowercaseUnicode,
    CharIsUppercaseUnicode,
    CharIsWhitespaceUnicode,
    CharIsControlUnicode,
    CharFromU32,
    CharFromDigit,
    CharToUppercase,
    CharToLowercase,
    CharToDigit,
    SliceLen,
    SliceIsEmpty,
    VecCapacity,
    VecReserve,
    VecReserveExact,
    VecShrinkToFit,
    VecShrinkTo,
    VecSwapRemove,
    VecAppend,
    VecExtendFromSlice,
    VecSplitOff,
    VecResize,
    VecDedup,
    VecReverse,
    VecFirstMut,
    VecLastMut,
    VecGetMut,
    VecAsSlice,
    VecAsMutSlice,
    SliceToVec,
    VecFrom,
    MemDrop,
    StringCapacity,
    StringReserve,
    StringReserveExact,
    StringShrinkToFit,
    StringShrinkTo,
    StringPop,
    StringRemove,
    StringInsert,
    StringInsertStr,
    StringTruncate,
    StringClear,
    StringSplitOff,
    StringAsBytes,
    StringIntoBytes,
    StrStripPrefix,
    StrStripSuffix,
    StrTrimStart,
    StrTrimEnd,
    StrReplace,
    StrRepeat,
    StrIsCharBoundary,
    BoxNew,
    BoxLeak,
    RcNew,
    RcStrongCount,
    RcWeakCount,
    RcMakeMut,
    RcGetMut,
    RcTryUnwrap,
    /// `Rc::into_inner` and `Rc::unwrap_or_clone` (W-STD-A phase 3).
    RcIntoInner,
    RcUnwrapOrClone,
    /// The `core::mem` byte-move family and `core::cmp::max`/`min`
    /// free fns (ARCH 4.4). `MemTake` only survives to lowering,
    /// which fills the freed slot with a synthesized default and
    /// calls `MemReplace`.
    MemSwap,
    MemReplace,
    MemTake,
    CmpMax,
    CmpMin,
    IterIter,
    IterIterMut,
    IterVecIntoIter,
    IterNext,
    IterMap,
    IterFilter,
    IterFilterMap,
    IterEnumerate,
    IterRev,
    IterTake,
    IterSkip,
    IterStepBy,
    IterChain,
    IterZip,
    IterCopied,
    IterCloned,
    IterTakeWhile,
    IterSkipWhile,
    IterPeekable,
    IterPeek,
    IterInspect,
    IterCount,
    IterLast,
    IterNth,
    IterAny,
    IterAll,
    IterFind,
    IterFindMap,
    IterPosition,
    IterFold,
    IterForEach,
    IterMin,
    IterMax,
    IterMinByKey,
    IterMaxByKey,
    IterCollect,
    IterSum,
    IterProduct,
    VecIterNext,
    VecIterNextBack,
    VecIterLen,
    CharsBytesLeft,
    CharsNextBack,
    /// `Default::default()` of a type whose default is built by
    /// structure (`has_default`): the `default` glue of the call's
    /// destination type.
    DefaultGlue,
    /// `Option::unwrap_or_default`: the payload, or the `default`
    /// glue's value of the payload type on `None`.
    OptUnwrapOrDefault,
    /// `core::fmt` (W-STD-B, check/fmt.rs): Formatter methods, the Debug
    /// builders (`FmtFinish` and kin serve every builder; the receiver
    /// type tells which), `write_fmt`, and `fmt` on a builtin value.
    FmtWriteStr,
    FmtWriteChar,
    FmtPad,
    FmtPadIntegral,
    FmtWidth,
    FmtPrecision,
    FmtFill,
    FmtAlternate,
    FmtSignPlus,
    FmtSignMinus,
    FmtSignAwareZeroPad,
    FmtDebugStruct,
    FmtDebugTuple,
    FmtDebugList,
    FmtDebugSet,
    FmtDebugMap,
    DsField,
    DtField,
    DlEntry,
    DmEntry,
    DmKey,
    DmValue,
    FmtFinish,
    FmtFinishNonExhaustive,
    FmtWriteFmt,
    FmtCallDisplay,
    FmtCallDebug,
    /// Conversion trait methods on builtin values (W-STD-B,
    /// check/convert.rs): `&T` unchanged, `&str` to `&[u8]`, an array
    /// to its slice, one deref (`&Box<T>` and `&&T` to `&T`), and an
    /// Rc's value.
    ConvIdent,
    ConvStrBytes,
    ConvArraySlice,
    ConvDeref,
    ConvRcInner,
    /// The cmp glue's three-way code for two references to one
    /// structurally ordered type (-1, 0, 1, or 2 for unordered), as
    /// an `i8`: `partial_cmp` and `cmp` read it once.
    CmpCode,
    /// `Option::as_ref`, `as_mut`, `take`, `replace`, and
    /// `Result::as_ref`, `as_mut` (W-STD-A phase 3).
    OptAsRef,
    OptAsMut,
    OptTake,
    OptReplace,
    ResAsRef,
    ResAsMut,
    SliceSort,
    SliceSortUnstable,
    SliceSortBy,
    SliceSortUnstableBy,
    SliceSortByKey,
    SliceSortUnstableByKey,
    SliceBinarySearch,
    SliceBinarySearchBy,
    SliceBinarySearchByKey,
    RcDowngrade,
    RcPtrEq,
    WeakNew,
    WeakUpgrade,
    WeakStrongCount,
    WeakWeakCount,
    WeakPtrEq,
    RefCellNew,
    RefCellBorrow,
    RefCellBorrowMut,
    RefCellIntoInner,
    RefCellReplace,
    RefCellSwap,
    RefCellGetMut,
    CellNew,
    CellGet,
    CellSet,
    CellReplace,
    CellIntoInner,
    CellGetMut,
    CellSwap,
    /// `Cell::take` and `RefCell::take`: replace with `T::default()`.
    CellTake,
    RefCellTake,
    /// `ExitCode::from(u8)` (check/process.rs).
    ExitCodeFrom,
    /// `Vec::into_boxed_slice`, `Box<[T]>::into_vec`, and by-value
    /// `Box<[T]>::into_iter` (a `vec::IntoIter<T>`, as in Rust 2024).
    VecIntoBoxedSlice,
    BoxSliceIntoVec,
    BoxSliceIntoIter,
    /// UTF-8 decoding (check/utf8.rs): `String::from_utf8`,
    /// `str::from_utf8`, and the methods of their errors.
    StringFromUtf8,
    StrFromUtf8,
    FromUtf8ErrorUtf8Error,
    FromUtf8ErrorAsBytes,
    FromUtf8ErrorIntoBytes,
    Utf8ErrorValidUpTo,
    Utf8ErrorErrorLen,
    /// A `std::sync` or `std::thread` call (check/sync.rs, W-THREADS).
    Sync(sync::SyncOp),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Res {
    None,
    Local(u32),
    Fn(LocalDefId),
    /// A unit variant value, a tuple-variant constructor, or a struct literal target.
    Variant(AdtId, u32),
    Builtin(Builtin),
    /// `None`, and `Some` used as a constructor.
    OptNone,
    OptSome,
    /// `Ok` and `Err` used as constructors.
    ResOk,
    ResErr,
    Method {
        f: LocalDefId,
        derefs: u8,
        autoref: Autoref,
    },
    BuiltinMethod {
        b: Builtin,
        derefs: u8,
        autoref: Autoref,
    },
    Field {
        derefs: u8,
        index: u32,
    },
    /// Operand deref counts for binary operators, compound assignment, and unary operators (`ld` only).
    Bin {
        ld: u8,
        rd: u8,
    },
    Index {
        derefs: u8,
    },
    /// A `core::intrinsics::<name>` call that passed the privilege check.
    /// The payload is the intrinsic's registry id (`ty::lang::INTRINSICS`).
    /// Only spliced shipped-library source can produce this resolution.
    Intrinsic(u32),
    /// A range index `base[lo..hi]` producing a slice place (W-CORELANG).
    SliceIndex {
        derefs: u8,
    },
    /// A static item read, by index into `Program::statics` (W-CORELANG).
    Static(u32),
    /// A compile-time usize constant: `size_of`, `align_of`, `offset_of!`.
    ConstUsize(u64),
    /// `size_of_val` of an unsized value (`[T]` or `str`): the length
    /// builtin for the argument times the element size (1 for `str`).
    SizeOfVal {
        len: Builtin,
        elem: u64,
    },
    /// A comparison trait method (`partial_cmp`, `cmp`, `eq`, `lt`,
    /// and kin) on a scalar receiver: lowering emits the scalar
    /// comparison directly, as the binary operators do. `derefs`
    /// counts autoderefs from the receiver to the scalar.
    PrimCmp {
        kind: PrimCmpKind,
        derefs: u8,
    },
    /// An operator trait method (`add`, `neg`, `add_assign`, and
    /// kin) on a scalar receiver: lowering emits the scalar
    /// operation directly, as the operators do.
    PrimOp {
        kind: PrimOpKind,
        derefs: u8,
    },
    /// `size_of_val` or `align_of_val` on a dyn value: reads this
    /// header word of the argument's vtable (`object::VT_SIZE`, `VT_ALIGN`).
    DynMeta(u32),
    /// A `core::any` operation (check/any.rs): the receiver is reached
    /// by `derefs` derefs and `autoref` as for `Method`; the type it
    /// tests or names is `Checked::generic_args[e][0]`.
    Any {
        op: any::AnyOp,
        derefs: u8,
        autoref: Autoref,
    },
    /// A binary operator through an operator trait: the trait
    /// method to call (a template until mono rewrites it through
    /// `Checked::generic_args`), with operand deref counts.
    TraitBin {
        f: LocalDefId,
        ld: u8,
        rd: u8,
    },
    /// A comparison operator through a written `PartialEq` or
    /// `PartialOrd` impl: `f` is the impl's method (a template until
    /// mono rewrites it through `Checked::generic_args`), called with
    /// both operands borrowed; `via` turns its result into the
    /// operator's answer (core's default bodies for `ne`, `lt`, and
    /// kin).
    TraitCmp {
        f: LocalDefId,
        ld: u8,
        rd: u8,
        via: CmpVia,
    },
    /// The same in method form (`a.ne(&b)`, `a.lt(&b)`): the receiver
    /// is borrowed after `derefs` derefs; the argument is `&Rhs`.
    TraitCmpMethod {
        f: LocalDefId,
        derefs: u8,
        via: CmpVia,
    },
    /// `Ord::max`, `min`, or `clamp` by core's default bodies on a
    /// receiver taken by value: compare with Self's `PartialOrd`
    /// (`f` and `via` for a written impl, by structure when `f` is
    /// None), move the answer out, and drop the other values.
    OrdPick {
        kind: OrdPickKind,
        f: Option<LocalDefId>,
        via: CmpVia,
    },
    /// A method of `core::cmp::Ordering` (`is_lt`, `reverse`, `then`,
    /// and kin) on a receiver reached through `derefs` derefs:
    /// lowering reads its variant and computes the answer.
    OrderingOp {
        kind: OrderingOpKind,
        derefs: u8,
    },
    /// A numeric `From::from` call, lowered as a cast to the
    /// call's type. Widening conversions only (checked).
    FromCast,
    /// A scalar `Default::default()` call, lowered as the zero
    /// value of the call's type.
    DefaultVal,
    /// A `for` loop through `IntoIterator`: the `into_iter` and
    /// `next` methods to call (templates until mono rewrites
    /// them through `Checked::generic_args`).
    ForTrait {
        into_iter: LocalDefId,
        next: LocalDefId,
    },
    /// A call through a function pointer value in the callee expression.
    Indirect,
    /// A `?` with no error conversion: on `Option`, or on `Result`
    /// whose error type already matches the enclosing return type.
    TryPlain,
    /// A `?` on `Result` whose error converts through this
    /// `From::from` method (a template until mono rewrites it
    /// through `Checked::generic_args`; `LocalDefId(u32::MAX)` when
    /// only param evidence proves it in a template body).
    TryFrom(LocalDefId),
    /// A `?` on `Result` whose error converts by a numeric
    /// widening cast (the `From` impls with no user fn).
    TryCast,
    /// A `?` on `Result` whose error converts through the builtin
    /// `From<&str> for String` or `From<&String> for String`: a
    /// copy into a fresh String with no user fn behind it.
    TryStringFrom,
    /// A call of a closure value (ARCH 2.9). `kind` is the Fn trait
    /// the call goes through (an `FnOnce` call consumes the callee),
    /// `derefs` the reference layers peeled off the callee. Lowering
    /// finds the body fn from the callee's closure type.
    ClosureCall {
        kind: closure::ClosureKind,
        derefs: u8,
    },
    /// A method call through a dyn receiver's vtable (ARCH 2.8):
    /// `owner` is the trait that declares the method (the principal
    /// or a supertrait, reached by its upcast path), `cand` its index
    /// in `object::object_cands` (one generic trait can be a
    /// supertrait twice: `B<u8> + B<u16>`), and `slot` the method's
    /// word index in that trait's vtable.
    DynMethod {
        owner: DefId,
        cand: u8,
        slot: u32,
        derefs: u8,
        autoref: Autoref,
    },
}

/// Which scalar comparison a `Res::PrimCmp` call computes. The
/// Adt is `core::cmp::Ordering`'s session-local index (variants
/// Less, Equal, Greater in that order).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrimCmpKind {
    /// `PartialOrd::partial_cmp` -> `Option<Ordering>`.
    Partial(AdtId),
    /// `Ord::cmp` -> `Ordering`.
    Total(AdtId),
    /// `eq`/`ne`/`lt`/`le`/`gt`/`ge` -> `bool`, the binary comparison.
    Op(ast::BinOp),
}

/// How a written comparison method answers an operator or a
/// default method (`Res::TraitCmp`, `Res::OrdPick`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpVia {
    /// The impl's own method for the operator (`eq`, `ne`, `lt`,
    /// `le`, `gt`, `ge`).
    Direct,
    /// `ne` by core's default body: the negated `eq`.
    NotEq,
    /// `lt`/`le`/`gt`/`ge` by core's default bodies: the impl's
    /// `partial_cmp`, tested for `Some(Less)` and kin.
    Partial(ast::BinOp),
}

/// Which `Ordering` method a `Res::OrderingOp` call computes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OrderingOpKind {
    IsEq,
    IsNe,
    IsLt,
    IsGt,
    IsLe,
    IsGe,
    Reverse,
    Then,
    /// `then_with(f)`: `f` is a closure called through `FnOnce`.
    ThenWith,
}

/// Which `Ord` default method a `Res::OrdPick` call runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OrdPickKind {
    Max,
    Min,
    Clamp,
}

/// Which scalar operation a `Res::PrimOp` call computes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrimOpKind {
    /// A binary operator trait method: `recv.op(rhs)`.
    Bin(ast::BinOp),
    /// A unary operator trait method: `recv.neg()` / `recv.not()`.
    Un(ast::UnOp),
    /// An assignment operator trait method: `recv.op_assign(rhs)`.
    Assign(ast::BinOp),
    /// `recv.into()` to a scalar target: the widening cast core's
    /// `From` impl is, cast to the call's type.
    IntoCast,
    /// `recv.into_iter()` on an iterator: core's blanket
    /// `impl<I: Iterator> IntoIterator for I` returns the receiver.
    IntoIterSelf,
}

/// One user `Deref` autoderef step (rustc's autoderef, ARCH 2.10) of
/// a method call receiver, a field access base, or an explicit `*w`:
/// after `before` builtin derefs of the step's input, lowering calls
/// `f` (the impl's `deref`, or `deref_mut` for a method call that
/// borrows mutably, `mutable`) on a borrow of it; the expression's
/// `Res` derefs then apply to the `&Target` (`target_ref`) it returns.
/// A place step also carries the impl's `deref_mut` (`f_mut`), which
/// lowering calls when it needs the place mutably. `args` and
/// `args_mut` instantiate generic fns (empty for plain ones). `depth`
/// orders a chain of steps (`W -> N -> M`): 0 is the outermost, which
/// applies first.
#[derive(Clone, Debug)]
pub struct DerefRecv {
    pub depth: u8,
    pub before: u8,
    pub f: LocalDefId,
    pub args: Vec<GenericArg>,
    pub f_mut: Option<LocalDefId>,
    pub args_mut: Vec<GenericArg>,
    pub mutable: bool,
    pub target_ref: Ty,
}

/// Which `Checked` table a generic `deref` fn's site fills in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DerefTable {
    Recv,
    Coerce,
}

/// A coercion applied where a value meets an expected type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Coerce {
    None,
    /// `&String` to `&str`, or `&&str` style deref coercions ending in `&str`.
    StrFromString,
    /// `&mut T` to `&T`.
    MutToShared,
    /// `&mut T` passed where `&mut T` is expected: reborrow, so the original is not moved.
    Reborrow,
    /// `&&T` (n extra references) to `&T`: copy the inner reference out.
    Deref(u8),
    /// `&[T; N]` to a slice reference; the bool is the target mutability.
    SliceFromArray(bool),
    /// `&Vec<T>` to a slice reference; the bool is the target mutability.
    SliceFromVec(bool),
    /// `&Box<T>` (possibly behind more references) to `&T` or
    /// `&mut T`: this many derefs reach the pointee place, and
    /// the bool is the target mutability.
    BoxToRef(u8, bool),
    /// An unsizing coercion to a dyn reference (ARCH 2.8): `&T` or
    /// `&mut T` to `&dyn Tr` (a new fat pointer), or `&dyn Sub` to
    /// `&dyn Super` (trait upcasting, or dropping auto traits). The
    /// payload is the target reference type.
    Unsize(Ty),
    /// A deref coercion through user `Deref` impls (`&name` to `&str`
    /// for `Name: Deref<Target = str>`): the steps are in
    /// `Checked::deref_coerce`; the payload is the target reference
    /// type.
    UserDeref(Ty),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindMode {
    Move,
    Ref(bool),
}

/// What a lone pattern identifier resolves to (see `Ctx::pat_ident`).
enum PatIdent {
    Const(u32),
    Static,
    Variant(AdtId, u32),
    Other,
}

#[derive(Clone, Copy, Debug)]
pub enum PatRes {
    None,
    /// A const item used as a pattern, by index into `Program::consts`.
    ConstItem(u32),
    /// A primitive associated const used as a pattern (`i64::MAX`):
    /// its value (the pattern type carries the width).
    PrimConst(i128),
    /// A body-local const used as a pattern, by index into `Program::body_consts`.
    BodyConst(u32),
    Binding {
        local: u32,
        mode: BindMode,
    },
    Variant(AdtId, u32),
    /// `Some(..)` (true) or `None` (false).
    Opt(bool),
    /// `Ok(..)` (true) or `Err(..)` (false).
    Res(bool),
}

#[derive(Clone)]
pub struct LocalInfo {
    pub name: Sym,
    pub ty: Ty,
    pub mutable: bool,
    pub span: Span,
}

/// The checker's output for one function. Clone: borrowck lowers each
/// closure of a fn from one check of it (`closure_reqs`).
#[derive(Clone)]
pub struct Checked<'g> {
    pub tys: Tys<'g>,
    pub expr_base: u32,
    pub pat_base: u32,
    pub expr_ty: Vec<Ty>,
    /// The const value of an expression the checker evaluated (a const item
    /// reference or an inline const block), parallel to `expr_ty`.
    pub const_exprs: Vec<Option<crate::ty::consteval::ConstValue>>,
    pub expr_res: Vec<Res>,
    pub coerce: Vec<Coerce>,
    pub pat_ty: Vec<Ty>,
    pub pat_res: Vec<PatRes>,
    /// The const value of a pattern that is a primitive associated
    /// const (`u8::MAX => ..`), parallel to `pat_res`.
    pub pat_const: Vec<Option<crate::ty::consteval::ConstValue>>,
    /// Number of implicit derefs before matching each pattern (default binding modes).
    pub pat_derefs: Vec<u8>,
    /// Generic arguments of each generic call or method call, by
    /// expression index (empty for plain calls), after zonking.
    /// Lowering resolves the template in the call's `Res` plus
    /// these args to a mono instance.
    pub generic_args: Vec<Vec<GenericArg>>,
    /// Instance requests found while checking: (template,
    /// zonked args in this body's store). Mono lifts and
    /// materializes them; the driver never reads this.
    pub inst_requests: Vec<(LocalDefId, Vec<GenericArg>)>,
    /// Trait picks of a template check (see `picks.rs`), in check
    /// order. Mono stores them for the body's other checks.
    pub trait_picks: Vec<(ExprId, picks::TraitPick)>,
    /// Vtable requests from unsizing coercions: (concrete pointee
    /// type, target dyn type), zonked. Mono builds the vtables.
    pub vtable_requests: Vec<(Ty, Ty)>,
    /// Expressions that go through user `Deref` impls (method call
    /// receivers, field access bases, explicit `*x`, index bases), by
    /// expression; a chain of impls records one entry per step (see
    /// `DerefRecv::depth`).
    pub deref_recv: Vec<(ExprId, DerefRecv)>,
    /// The steps of each `Coerce::UserDeref`, by coerced expression,
    /// outermost first.
    pub deref_coerce: Vec<(ExprId, DerefRecv)>,
    pub locals: Vec<LocalInfo>,
    /// Locals bound to the function parameters, in order (including `self`).
    pub param_locals: Vec<u32>,
    /// Every cross-item node this body read through a query function
    /// (docs/ARCH.md section 8.2). Stored with the result; nothing consumes
    /// it for invalidation yet (S7 is record-only).
    pub reads: Reads,
    /// The closure expressions of this body, in check order, zonked.
    pub closures: Vec<closure::ClosureInfo>,
    /// Every closure call and the Fn trait it goes through. Mono keeps
    /// the template's answers for its instances (`template_calls`).
    pub closure_calls: Vec<(ExprId, closure::ClosureKind)>,
    /// True when this is a closure body fn whose parent failed to
    /// check: the parent reports the errors, lowering emits nothing.
    pub poisoned: bool,
    /// The regioned type a `let` annotation with an explicit lifetime
    /// gives each binding it covers, by checker local (W-BORROW): the
    /// borrow checker relates the binding's regions to it.
    pub annotations: Vec<(u32, Ty)>,
    /// Obligations taken from this body's queue, once per take (each
    /// run round takes them all; `Obligations::work`). A work count for
    /// tests that guard against selection blow-ups.
    pub queue_work: usize,
    /// The hidden type of each `impl Trait` this body defines
    /// (`check::opaque`), by opaque def.
    pub opaque_hidden: Vec<(DefId, Ty)>,
    /// The hidden types a revealed check put in place of callee opaque
    /// types (check/opaque.rs): lowering marks the locals that hold them
    /// (`Body::opaque_locals`).
    pub revealed: Vec<Ty>,
}

impl Checked<'_> {
    pub fn ty(&self, e: ExprId) -> Ty {
        self.expr_ty[(e.0 - self.expr_base) as usize]
    }
    pub fn res(&self, e: ExprId) -> Res {
        self.expr_res[(e.0 - self.expr_base) as usize]
    }
    pub fn coerce(&self, e: ExprId) -> Coerce {
        self.coerce[(e.0 - self.expr_base) as usize]
    }
    pub fn pat_ty(&self, p: PatId) -> Ty {
        self.pat_ty[(p.0 - self.pat_base) as usize]
    }
    pub fn pat_res(&self, p: PatId) -> PatRes {
        self.pat_res[(p.0 - self.pat_base) as usize]
    }
    pub fn pat_const(&self, p: PatId) -> Option<&crate::ty::consteval::ConstValue> {
        self.pat_const[(p.0 - self.pat_base) as usize].as_ref()
    }
    pub fn const_value(&self, e: ExprId) -> Option<&crate::ty::consteval::ConstValue> {
        self.const_exprs[(e.0 - self.expr_base) as usize].as_ref()
    }
    pub fn pat_derefs(&self, p: PatId) -> u8 {
        self.pat_derefs[(p.0 - self.pat_base) as usize]
    }
    /// The user `Deref` steps of a method call's receiver, a field
    /// access base, or an explicit `*x`, outermost first.
    pub fn deref_recv(&self, e: ExprId) -> Vec<&DerefRecv> {
        let mut steps: Vec<&DerefRecv> = self.deref_recv.iter().filter(|(x, _)| *x == e).map(|(_, d)| d).collect();
        steps.sort_by_key(|d| d.depth);
        steps
    }
    /// The steps of a `Coerce::UserDeref` on `e`, outermost first.
    pub fn deref_coerce(&self, e: ExprId) -> Vec<&DerefRecv> {
        self.deref_coerce.iter().filter(|(x, _)| *x == e).map(|(_, d)| d).collect()
    }
}

struct Var {
    bound: Option<Ty>,
}

struct LoopCtx {
    break_ty: Option<Ty>,
    /// True when `break` may carry a value (a `loop` or a labeled block).
    is_loop: bool,
    /// True for a labeled block, which `continue` cannot target.
    is_block: bool,
    /// The label and its binding span; hygiene reads the span's context.
    label: Option<(Sym, Span)>,
}

struct Ctx<'p, 'a> {
    p: &'p Program<'a>,
    f: &'p FnInfo<'a>,
    /// The module this fn is defined in (root without the resolver),
    /// for field visibility checks (ARCH 1.5).
    module: crate::ty::defs::ModuleId,
    tys: Tys<'p>,
    vars: Vec<Var>,
    out: Checked<'p>,
    /// Locals by (name, hygiene context): a local a macro introduces does
    /// not bind a caller ident of the same name, and an ident the caller
    /// passes in keeps the caller's context (ARCH 6.3).
    scopes: Vec<((Sym, CtxtId), u32)>,
    /// Items declared in enclosing blocks, keyed like locals by name and
    /// hygiene context, holding stmt item indexes.
    item_scopes: Vec<Vec<((Sym, CtxtId), u32)>>,
    loops: Vec<LoopCtx>,
    errs: Vec<Diag>,
    negated_lits: Vec<ExprId>,
    /// The trait obligation queue (ARCH 2.4), run at the fixed
    /// points in `run_obligations`.
    obl: obligations::Obligations,
    /// This fn's own local id, for its scope and env.
    fid: LocalDefId,
    /// Selection state (memos, cycle stack) for this body.
    solver: Solver,
    /// Rollback trail of variable bindings, for solver probes.
    trail: Vec<u32>,
    /// The scope body annotations resolve under (with `_` markers on).
    body_scope: Scope,
    /// Generic call sites to turn into instance requests at
    /// finish: (expression index, template, args before zonking).
    generic_sites: Vec<(usize, LocalDefId, Vec<GenericArg>)>,
    /// Trait associated const reads a template check proved only
    /// by its bounds: no value is known until an instance picks
    /// the impl. `finish` gives them a zero placeholder (after
    /// the overflow lint, so no analysis reads the fake value)
    /// purely so the template body lowers for borrowck.
    abstract_consts: Vec<ExprId>,
    /// While the const evaluator runs a const fn body (`CheckCx`'s
    /// `enter_const_fn`), the Adt `Self` means there: the fn's impl
    /// type, not this body's. Saved (override, Self type) pairs restore
    /// on exit.
    const_fn_self: Option<Option<AdtId>>,
    const_fn_saved: Vec<(Option<Option<AdtId>>, Option<Ty>)>,
    /// Trait method calls whose impl is selected at finish (see
    /// `method::confirm_deferred`).
    deferred_methods: Vec<method::DeferredMethod>,
    /// Operators whose result waits on an `Output` obligation because
    /// an operand was a general variable at their first check (see
    /// `binary`).
    deferred_binops: Vec<ExprId>,
    /// Format arguments whose type was still a variable when
    /// the format check ran: (type, spec, span). The format test
    /// re-runs at finish (W-TRAITS-CORE).
    deferred_fmt: Vec<(Ty, FmtSpec, Span)>,
    /// `format_args!` expressions checked as the argument of a
    /// `write_fmt` call (check/fmt.rs); any other is a reject.
    format_args_ok: Vec<ExprId>,
    /// Element types a builtin Vec or slice method needs to be
    /// Clone (`extend_from_slice`, `resize`, `to_vec`), re-tested
    /// at finish like the format traits: the element type can
    /// still be a variable at the call.
    deferred_clone: Vec<(Ty, Span)>,
    /// Input types of `String::from` used as a value
    /// (`.map(String::from)`), re-tested at finish: lust's
    /// `String::from` takes `&str`, `char`, or `String`.
    deferred_string_from: Vec<(Ty, Span)>,
    /// `Some`, `Ok`, `Err`, `Box::new`, or `Rc::new` passed as a call
    /// argument (`keep(Some, &x)` under `F: Fn(T) -> R`): borrowck does
    /// not relate a fn item's signature at a generic Fn bound yet
    /// (W-BORROW, ARCH 5.6), so at finish one whose input type may
    /// borrow is a reject rather than a possible false accept.
    deferred_item_args: Vec<(Ty, Span)>,
    /// Element types a builtin Vec method needs to be PartialEq
    /// (`contains`, `dedup`), re-tested at finish as above.
    deferred_eq: Vec<(Ty, Span)>,
    /// Item types an iterator method needs to be Copy (`copied`),
    /// re-tested at finish as above (W-STD-A).
    deferred_copy: Vec<(Ty, Span)>,
    /// Item or key types an iterator method needs to be Ord (`min`,
    /// `max`, `min_by_key`, `max_by_key`), re-tested at finish.
    deferred_ord: Vec<(Ty, Span)>,
    /// Types a `Result` method formats with Debug in its panic message.
    deferred_debug: Vec<(Ty, Span)>,
    /// Types a `take` builds with `Default::default()`.
    deferred_default: Vec<(Ty, Span)>,
    /// Element types of Rc fns that lust only has for a sized `T`
    /// (by-value `try_unwrap` and `into_inner`, `get_mut`, and
    /// `downgrade`, whose `Weak` is a thin pointer).
    deferred_sized: Vec<(Ty, Span)>,
    /// True while normalization runs inside `unify`, to keep
    /// projection normalization from recursing into itself.
    in_norm: bool,
    /// Const inference variables (from `generics::INFER_MARKER_BASE`)
    /// to the consts they bound to.
    const_bindings: std::collections::HashMap<u32, ConstId>,
    next_const_id: u32,
    /// Closures checked so far in this body (see `check::closure`).
    closures: Vec<closure::ClosureInfo>,
    /// Return types of the closure bodies being checked, innermost last:
    /// `return` inside a closure returns from the closure.
    closure_rets: Vec<Ty>,
    /// The return type this body checks against (`defining_ret`).
    fn_ret: Ty,
    /// This body's own `impl Trait` returns: (opaque def, its args, the
    /// variable standing for the hidden type).
    own_opaques: Vec<(DefId, ArgsId, Ty)>,
    /// How this check sees the `impl Trait` values of its callees
    /// (check/opaque.rs): rigid with their bounds, or revealed.
    opaque_mode: opaque::OpaqueMode,
    /// The trait picks the opaque view of this same body recorded, which
    /// its revealed check replays (`replay_pick`).
    view_picks: crate::intern::FxMap<ExprId, picks::TraitPick>,
    /// The Fn trait each call of an opaque callable went through in the
    /// opaque view, which the revealed check keeps (a closure behind
    /// `impl FnOnce` is consumed even when it is `Fn`).
    view_calls: crate::intern::FxMap<ExprId, closure::ClosureKind>,
    /// The bounds of the callee opaque types this body has met, elaborated,
    /// after the fn's own env (`opaque::note_opaques`); empty until one.
    opaque_env: Vec<Predicate>,
    opaque_seen: Vec<Ty>,
    /// A revealed hidden type is `Copy` where its bounds do not say so:
    /// lust's borrow checker would see copies where rustc sees moves.
    opaque_copy_hazard: bool,
    /// This body's closure expressions in token order, for their defs.
    closure_order: Option<Vec<ExprId>>,
    /// The closure-argument type vars of iterator methods (`iter.rs`
    /// `fn_mut_param`) and of generic calls whose `Fn` bound takes type
    /// params (`note_closure_bounds`), each with one flag per argument:
    /// true when its outer reference is higher-ranked (`&item`). W-BORROW:
    /// the other argument regions are free; see `ClosureInfo::free_args`.
    iter_closure_args: std::collections::HashMap<u32, Vec<bool>>,
    /// W-THREADS: the closure-argument type var of each `thread::scope`
    /// call (`ClosureInfo::scope_body`).
    scope_closure_vars: Vec<u32>,
    /// W-BORROW: the closure-argument type vars of generic calls whose
    /// regioned `Fn` bound has a higher-ranked output over its one
    /// elided input lifetime (`F: Fn(&T) -> &U`), with that output's
    /// regioned type (`ClosureInfo::bound_output`).
    closure_bound_outputs: std::collections::HashMap<u32, Ty>,
    /// Scalar operators checked while both operand types were still
    /// open (a closure's `|a, b| a + b`): (expr, op, operand type).
    /// Lowering emits the builtin operator, so the types must turn out
    /// scalar by body end (see `finish`).
    open_binops: Vec<(ExprId, BinOp, Ty)>,
    /// Unsizing coercion sites, (concrete pointee, dyn type, span)
    /// before zonking; `finish` turns them into vtable requests.
    vtable_sites: Vec<(Ty, Ty, Span)>,
    /// True once an unsizing coercion made a dyn value from one that
    /// may hold a borrow (see `dyn_static_clean`).
    dyn_borrow_src: bool,
    /// The expected result type of the method call being checked, by
    /// call expression: a generic method's closure arguments read it
    /// (`expected_output_first`).
    pub(super) call_expected: Option<(ExprId, Ty)>,
    /// User `Deref` steps the method lookup is inside (a bound on
    /// `Deref` chains).
    deref_depth: u8,
    /// Generic `deref` (or `deref_mut`, the flag) fns of
    /// `out.deref_recv` entries: the entry, the template, and its impl
    /// args (zonked into the entry and requested as instances at body
    /// end).
    deref_sites: Vec<(DerefTable, usize, bool, LocalDefId, Vec<GenericArg>)>,
    /// Or-pattern alternatives being checked against the first
    /// alternative's bindings, innermost last (see the `Pat::Or`
    /// arm of `pattern_mode`).
    or_frames: Vec<OrFrame>,
    /// Bindings of the or-pattern first alternative currently
    /// being recorded, when any (see `bind_pattern_local`).
    or_log: Option<Vec<OrBind>>,
    /// Scope length at entry to each enclosing `pattern` call:
    /// bindings between the mark and the end of `scopes` belong
    /// to that one pattern and may not repeat a name.
    pat_marks: Vec<usize>,
}

/// One name bound by a pattern alternative, with the checker
/// local every alternative shares.
#[derive(Clone)]
struct OrBind {
    name: Sym,
    ctxt: CtxtId,
    local: u32,
    mode: BindMode,
    /// The binding's own type (after its mode is applied).
    ty: Ty,
    /// The `mut` of the local itself (`ref mut` lives in `mode`).
    mutable: bool,
}

/// Checking one non-first or-pattern alternative: the bindings
/// the first alternative made, which of them this alternative
/// has bound so far, and names it bound that the first did not.
struct OrFrame {
    expected: Vec<OrBind>,
    seen: Vec<bool>,
    extra: Vec<(Sym, Span)>,
}

/// The module a body checks in: the module of the def that owns
/// the body, exactly as a non-generic body in that module sees it
/// (ARCH 1.5). AST fns read `fn_module` by `LocalDefId`. Fns mono
/// appends are past that vec: an instance takes its template's
/// module, and a trait-default template (or a template with no
/// local form) takes the module its def was defined in. Closure
/// body fns never reach here (`check_fn` checks them as their
/// parent). Without resolver tables every body is in the root.
fn defining_module(p: &Program, fid: LocalDefId) -> crate::ty::defs::ModuleId {
    let root = crate::ty::defs::ROOT_MODULE;
    let Some(tables) = &p.resolved else { return root };
    // A def's defining module from the resolver table. Associated
    // defs (trait methods) are not module items, so the walk
    // climbs to their parent def (the trait), which is one.
    let module_of_def = |p: &Program, mut def: crate::def::DefId| -> crate::ty::defs::ModuleId {
        for _ in 0..4 {
            if let Some(info) = tables.def_info.get(&def) {
                return info.module;
            }
            // The parent def, or (trait methods carry none) the
            // trait the index files the def under.
            let parent = p.defs.parent_of(def).or_else(|| p.gx.index.trait_of_method(def)).or_else(|| p.gx.index.trait_of_assoc(def));
            let Some(parent) = parent else { break };
            def = parent;
        }
        root
    };
    let mut cur = fid;
    // Instances name their template directly, so this walks at
    // most one hop in practice; the bound guards only against a
    // malformed table.
    for _ in 0..8 {
        if let Some(m) = tables.fn_module.get(cur.0 as usize) {
            return *m;
        }
        if let Some(info) = p.gx.instances.get(&cur) {
            if let Some(template) = info.template_local {
                cur = template;
                continue;
            }
            return module_of_def(p, info.template_def);
        }
        return p.fn_defs.get(cur.0 as usize).map_or(root, |&def| module_of_def(p, def));
    }
    root
}

/// Type-checks one function body. A closure body fn checks as its
/// parent fn (closures share their parent's inference); the parent's
/// own entry reports any errors, so the closure fn reports none and
/// marks the result poisoned instead.
pub fn check_fn<'p, 'a>(p: &'p Program<'a>, fid: LocalDefId) -> (Checked<'p>, Vec<Diag>) {
    if let Some(def) = p.gx.closure_fns.get(&fid)
        && let Some(entry) = p.gx.closures.get(def)
    {
        let (mut ck, errs) = check_fn(p, entry.parent);
        ck.poisoned = !errs.is_empty();
        return (ck, Vec::new());
    }
    opaque::check_fn_opaque(p, fid)
}

/// One check of one fn body under an `impl Trait` mode, with the picks
/// its opaque view recorded when `mode` is `Revealed` (check/opaque.rs).
fn check_fn_mode<'p, 'a>(
    p: &'p Program<'a>,
    fid: LocalDefId,
    mode: opaque::OpaqueMode,
    view: opaque::ViewOut,
) -> (Checked<'p>, Vec<Diag>) {
    let f = p.fn_info(fid);
    let def = f.def;
    let n_exprs = (def.exprs.1 - def.exprs.0) as usize;
    let n_pats = (def.pats.1 - def.pats.0) as usize;
    let mut cx = Ctx {
        p,
        f,
        module: defining_module(p, fid),
        tys: Tys::new(&p.tys),
        vars: Vec::new(),
        out: Checked {
            tys: Tys::new(&p.tys),
            expr_base: def.exprs.0,
            pat_base: def.pats.0,
            expr_ty: vec![ERROR; n_exprs],
            const_exprs: vec![None; n_exprs],
            expr_res: vec![Res::None; n_exprs],
            coerce: vec![Coerce::None; n_exprs],
            pat_ty: vec![ERROR; n_pats],
            pat_res: vec![PatRes::None; n_pats],
            pat_const: vec![None; n_pats],
            pat_derefs: vec![0; n_pats],
            generic_args: vec![Vec::new(); n_exprs],
            inst_requests: Vec::new(),
            trait_picks: Vec::new(),
            vtable_requests: Vec::new(),
            deref_recv: Vec::new(),
            deref_coerce: Vec::new(),
            locals: Vec::new(),
            param_locals: Vec::new(),
            reads: if p.record_reads { Reads::new() } else { Reads::off() },
            closures: Vec::new(),
            closure_calls: Vec::new(),
            poisoned: false,
            annotations: Vec::new(),
            queue_work: 0,
            opaque_hidden: Vec::new(),
            revealed: Vec::new(),
        },
        scopes: Vec::new(),
        item_scopes: Vec::new(),
        loops: Vec::new(),
        errs: Vec::new(),
        negated_lits: Vec::new(),
        obl: obligations::Obligations::new(),
        fid,
        solver: Solver::new(),
        trail: Vec::new(),
        body_scope: {
            let mut sc = p.gx.fn_scopes.get(fid.0 as usize).map_or_else(Scope::default, |fs| fs.scope.clone());
            sc.infer_cell = Some(std::sync::Arc::new(std::sync::atomic::AtomicU32::new(generics::INFER_MARKER_BASE)));
            if sc.self_ty.is_none() {
                sc.self_ty = f.owner.map(|a| p.tys.get_adt_ty(a).expect("ADT types are interned during collection"));
            }
            sc
        },
        generic_sites: Vec::new(),
        abstract_consts: Vec::new(),
        const_fn_self: None,
        const_fn_saved: Vec::new(),
        deferred_methods: Vec::new(),
        deferred_binops: Vec::new(),
        deferred_fmt: Vec::new(),
        format_args_ok: Vec::new(),
        deferred_clone: Vec::new(),
        deferred_string_from: Vec::new(),
        deferred_item_args: Vec::new(),
        deferred_eq: Vec::new(),
        deferred_copy: Vec::new(),
        deferred_ord: Vec::new(),
        deferred_debug: Vec::new(),
        deferred_default: Vec::new(),
        deferred_sized: Vec::new(),
        in_norm: false,
        const_bindings: std::collections::HashMap::new(),
        next_const_id: generics::INFER_MARKER_BASE,
        closures: Vec::new(),
        closure_rets: Vec::new(),
        fn_ret: f.ret,
        own_opaques: Vec::new(),
        opaque_mode: mode,
        view_picks: view.picks,
        view_calls: view.calls,
        opaque_env: Vec::new(),
        opaque_seen: Vec::new(),
        opaque_copy_hazard: false,
        closure_order: None,
        iter_closure_args: std::collections::HashMap::new(),
        scope_closure_vars: Vec::new(),
        closure_bound_outputs: std::collections::HashMap::new(),
        open_binops: Vec::new(),
        vtable_sites: Vec::new(),
        dyn_borrow_src: false,
        call_expected: None,
        deref_depth: 0,
        deref_sites: Vec::new(),
        or_frames: Vec::new(),
        or_log: None,
        pat_marks: Vec::new(),
    };
    if let Some(sibs) = p.fn_siblings.get(&fid) {
        let layer: Vec<((Sym, CtxtId), u32)> = sibs
            .iter()
            .filter_map(|&si| {
                let name = match &p.ast.stmt_items[si as usize].kind {
                    ItemKind::Fn(d) => Some((d.name, d.name_span.ctxt)),
                    ItemKind::Const(c) => c.name.map(|n| (n, c.name_span.ctxt)),
                    ItemKind::Static(st) => Some((st.name, st.name_span.ctxt)),
                    _ => None,
                };
                name.map(|n| (n, si))
            })
            .collect();
        cx.item_scopes.push(layer);
    }
    // A template body keeps its `Param` types: the store answers
    // the structural trait queries on them from the env (`Tys::env`).
    cx.tys.env = p.gx.fn_scopes.get(fid.0 as usize).map_or(&[], |fs| fs.env.as_slice());
    let mut pi = 0;
    if let Some(sp) = &def.self_param {
        let l = cx.add_local(p.known.self_value, f.params[0], sp.mutable, sp.span);
        cx.out.param_locals.push(l);
        pi = 1;
    }
    let mut seen_params: Vec<Sym> = Vec::new();
    for param in &def.params {
        if param.pat.is_none() {
            if seen_params.contains(&param.name) {
                let name = p.name(param.name).to_string();
                cx.err("L0106", param.span, format!("`{name}` is defined more than once"), "Rename one of the parameters.");
            }
            seen_params.push(param.name);
        }
        // A plain parameter name that resolves to a const item or a
        // unit variant is a refutable pattern, not a binding (rustc
        // E0005); a static name cannot be a pattern at all.
        if param.pat.is_none() && !param.mutable {
            match cx.pat_ident(param.name) {
                PatIdent::Const(_) => {
                    cx.err(
                        "L0110",
                        param.span,
                        "refutable pattern in function argument",
                        "Rename the parameter: this name is a const item, so it would be a pattern, not a binding.",
                    );
                }
                PatIdent::Static => {
                    cx.err("L0110", param.span, "statics cannot be used as patterns", "Rename the parameter: this name is a static item.");
                }
                PatIdent::Variant(a, _) if p.adt(a).is_enum => {
                    cx.err(
                        "L0110",
                        param.span,
                        "refutable pattern in function argument",
                        "Rename the parameter: this name is an enum variant, so it would be a pattern, not a binding.",
                    );
                }
                PatIdent::Variant(a, _) => {
                    // A unit struct name as a parameter is a unit
                    // pattern: legal only against its own type.
                    let at = cx.tys.adt_ty(a);
                    if !cx.unify(at, f.params[pi]) {
                        cx.mismatch(param.span, f.params[pi], at);
                    }
                }
                _ => {}
            }
        }
        // A pattern parameter binds out of a nameless argument
        // local, like a destructuring `let` out of a temporary:
        // `param_locals` keeps it so lowering has the place, and
        // the pattern's own locals are the names the body sees.
        let l = cx.add_local(param.name, f.params[pi], param.mutable, param.span);
        cx.out.param_locals.push(l);
        if let Some(pat) = param.pat {
            let scope_before = cx.scopes.len();
            cx.pattern(pat, f.params[pi], false);
            // A name bound by two parameters is one definition
            // too many, pattern parameters included.
            for &((bound, _), _) in &cx.scopes[scope_before..].to_vec() {
                if seen_params.contains(&bound) {
                    let name = p.name(bound).to_string();
                    cx.err("L0106", param.span, format!("`{name}` is defined more than once"), "Rename one of the parameters.");
                }
                seen_params.push(bound);
            }
            if !cx.pat_always_matches(pat) {
                cx.err(
                    "L0110",
                    param.span,
                    "refutable pattern in function argument",
                    "Use a pattern that matches every value, or match in the body.",
                );
            }
        }
        pi += 1;
    }
    // A template's parameters and return value are values of their
    // types, which must be `Sized` under its env (rustc E0277): a
    // `T: ?Sized` param, or `self` in a trait default body without
    // `Self: Sized`. Collect checks the concrete forms (`[T]`, `str`).
    if cx.is_template_check() {
        let mut slots: Vec<(Ty, Span)> = Vec::new();
        let mut i = 0;
        if let Some(sp) = &def.self_param {
            slots.push((f.params[0], sp.span));
            i = 1;
        }
        for param in &def.params {
            slots.push((f.params[i], param.span));
            i += 1;
        }
        slots.push((f.ret, def.ret.map_or(def.name_span, |t| p.ast.ty_span(t))));
        for (t, span) in slots {
            if !cx.sized_ok(t) {
                let tn = cx.tn(t);
                cx.err(
                    "L0110",
                    span,
                    format!("the size for values of type `{tn}` cannot be known"),
                    "Pass the value behind a reference such as `&T`, or drop the `?Sized` bound.",
                );
            }
        }
    }
    // A declaration without a body (trait or foreign fn shape) has nothing
    // to check; the parser does not build those today.
    cx.fn_ret = cx.defining_ret();
    let ret_span = def.ret.map_or(def.name_span, |t| p.ast.ty_span(t));
    if let Some(body) = def.body {
        let fn_ret = cx.fn_ret;
        let body_ty = cx.block(body, Some(fn_ret));
        let body_span = p.ast.block(body).span;
        if let Some(tail) = p.ast.block(body).tail {
            cx.coerce_expr(tail, body_ty, fn_ret);
        } else {
            cx.coerce_at(body_ty, fn_ret, body_span, None);
        }
    }
    cx.push_opaque_bounds(ret_span);
    cx.finish();
    cx.finish_opaques(ret_span);
    cx.reject_opaque_uses();
    let Ctx { out, tys, errs, obl, .. } = cx;
    let mut out = out;
    out.tys = tys;
    out.queue_work = obl.work();
    let mut errs = errs;
    // A `const fn` body must also pass the const-context rules: the
    // const evaluator only sees the calls made from const items, so a
    // body that is never const-evaluated needs its own check.
    if f.is_const {
        let prior_errs = !errs.is_empty();
        errs.extend(constfn::check_const_fn(p, &out, f, prior_errs));
    }
    (out, errs)
}

/// True if Rust can compare two string-like operands for equality. `ld` and `rd` are the
/// reference depths of the two sides and `lk` and `rk` their base kinds (`String` or `Str`).
/// The model: peel the common reference layers (the blanket `&A == &B` impl), then require
/// one of the base impls: String==String, String==str, String==&str, str==String,
/// str==str, or &str==String.
/// A value the overflow lint knows at compile time. Integers hold the
/// value's bits in an i128: for every integer type except `u128` that
/// is also the mathematical value, and `u128` operations read the bits
/// back as a u128, so values at or above 2^127 stay exact.
#[derive(Clone, PartialEq)]
enum KVal {
    Int(i128),
    Bool(bool),
    /// A known enum discriminant: the adt and the variant index. The
    /// payload stays unknown.
    Enum(AdtId, u32),
    Agg(Vec<Option<KVal>>),
}

type KEnv = Vec<Option<KVal>>;

/// Whether a match pattern matches a known scrutinee value, when the
/// overflow lint can tell.
enum KCov {
    Yes,
    No,
    Unknown,
}

/// State of the overflow-lint walk: addressed locals, the stack of loop
/// and labeled-block frames collecting break values, and one operation to
/// leave alone (the `a = a + 1` form).
struct KLint {
    addressed: Vec<bool>,
    frames: Vec<(Option<Sym>, Vec<Option<KVal>>)>,
    suppress: Option<(ExprId, u32)>,
    /// The current path is known to be unreachable (a known branch that
    /// is taken diverges): the rest of the block is not linted.
    dead: bool,
    /// `#[allow(arithmetic_overflow)]` on the function.
    allow_arith: bool,
    /// `#[allow(unconditional_panic)]` on the function.
    allow_panic: bool,
    /// Statement-level allows in force (`#[allow(..)] let ..;`).
    stmt_allow_arith: u32,
    stmt_allow_panic: u32,
}

/// True when an attribute is `#[allow(<name>)]` (possibly one of several).
pub fn allow_attr(attr: &ast::Attr, interner: &Interner, name: &str) -> bool {
    if attr.path.len() != 1 || interner.get(attr.path[0].name) != "allow" {
        return false;
    }
    let ast::AttrInput::List(_, trees) = &attr.input else { return false };
    fn has(trees: &[crate::lexer::TokenTree], interner: &Interner, name: &str) -> bool {
        trees.iter().any(|t| match t {
            crate::lexer::TokenTree::Token(tok) => matches!(tok.tok, crate::lexer::Tok::Ident(s) if interner.get(s) == name),
            crate::lexer::TokenTree::Delim(_, inner, _) => has(inner, interner, name),
        })
    }
    has(trees, interner, name)
}

/// The name and binding span of an optional AST label.
fn label_of(label: &Option<ast::Label>) -> Option<(Sym, Span)> {
    label.map(|l| (l.name, l.span))
}

/// Maps written tuple pattern elements to field indexes. At most one `..`
/// may appear; elements after it count from the end. None on an arity
/// mismatch or a second `..`. Lowering uses the same mapping.
pub fn map_tuple_elems(ast: &crate::ast::Ast, elems: &[PatId], nfields: usize) -> Option<Vec<(usize, PatId)>> {
    let rest = elems.iter().position(|&s| matches!(ast.pat(s), Pat::Rest));
    match rest {
        None => {
            if elems.len() != nfields {
                return None;
            }
            Some(elems.iter().enumerate().map(|(i, &s)| (i, s)).collect())
        }
        Some(r) => {
            if elems[r + 1..].iter().any(|&s| matches!(ast.pat(s), Pat::Rest)) {
                return None;
            }
            let suffix = elems.len() - r - 1;
            if r + suffix > nfields {
                return None;
            }
            let mut out: Vec<(usize, PatId)> = elems[..r].iter().enumerate().map(|(i, &s)| (i, s)).collect();
            for (j, &s) in elems[r + 1..].iter().enumerate() {
                out.push((nfields - suffix + j, s));
            }
            Some(out)
        }
    }
}

fn string_eq_ok(ld: u8, lk_is_string: bool, rd: u8, rk_is_string: bool) -> bool {
    let peel = ld.min(rd);
    let (la, ra) = ((ld - peel, lk_is_string), (rd - peel, rk_is_string));
    let string = (0, true);
    let str_ = (0, false);
    let ref_str = (1, false);
    matches!(
        (la, ra),
        (a, b) if (a == string && (b == string || b == str_ || b == ref_str))
            || (a == str_ && (b == string || b == str_))
            || (a == ref_str && b == string)
    )
}

impl<'p, 'a> Ctx<'p, 'a> {
    fn err(&mut self, code: &'static str, span: Span, msg: impl Into<String>, fix: impl Into<String>) {
        self.errs.push(Diag::new(code, span, msg, fix));
    }
    fn span(&self, e: ExprId) -> Span {
        self.p.ast.expr_span(e)
    }
    fn name(&self, s: Sym) -> &str {
        self.p.name(s)
    }
    /// Type name for messages, with inference variables resolved.
    fn tn(&self, t: Ty) -> String {
        let t = self.resolve(t);
        match self.tys.kind(t) {
            TyKind::Ref(_, _, e) if matches!(self.tys.kind(e), TyKind::Dyn(..)) => ty_name(self.p, &self.tys, t),
            TyKind::Ref(_, m, e) => format!("&{}{}", if m.is_mut() { "mut " } else { "" }, self.tn(e)),
            _ => match self.tys.builtin_of(t) {
                Some(BuiltinTy::Vec) => format!("Vec<{}>", self.tn(self.tys.adt_first_ty_arg(t).unwrap_or(ERROR))),
                Some(BuiltinTy::Option) => format!("Option<{}>", self.tn(self.tys.adt_first_ty_arg(t).unwrap_or(ERROR))),
                Some(BuiltinTy::Result) => {
                    let (a, b) = self.tys.result_args(t).unwrap_or((ERROR, ERROR));
                    format!("Result<{}, {}>", self.tn(a), self.tn(b))
                }
                _ => ty_name(self.p, &self.tys, t),
            },
        }
    }
    fn ei(&self, e: ExprId) -> usize {
        (e.0 - self.out.expr_base) as usize
    }
    fn set(&mut self, e: ExprId, t: Ty) -> Ty {
        let i = self.ei(e);
        self.out.expr_ty[i] = t;
        t
    }
    fn set_res(&mut self, e: ExprId, r: Res) {
        // A method of an impl for a `'static` dyn type (`impl dyn Tr`).
        if let Res::Fn(f) | Res::Method { f, .. } | Res::TraitBin { f, .. } = r
            && self.p.gx.static_dyn_fns.contains(&f)
        {
            let span = self.span(e);
            self.obl.push(obligations::Obligation::DynStatic { span });
        }
        let i = self.ei(e);
        self.out.expr_res[i] = r;
    }
    fn add_local(&mut self, name: Sym, ty: Ty, mutable: bool, span: Span) -> u32 {
        let l = self.out.locals.len() as u32;
        self.out.locals.push(LocalInfo { name, ty, mutable, span });
        // `span` must be the binding name's own span: its context is the
        // hygiene key. Callers pass the pattern or parameter name span.
        self.scopes.push(((name, span.ctxt), l));
        l
    }
    fn lookup(&self, name: Sym, ctxt: CtxtId) -> Option<u32> {
        // The newest visible binding of this name: same context, or one a
        // body-local macro could already see at its definition (ARCH 6.3).
        self.scopes
            .iter()
            .rev()
            .find(|((n, _), l)| *n == name && crate::diag::ctxt_can_see_local(ctxt, self.out.locals[*l as usize].span))
            .map(|&(_, l)| l)
    }

    // Cross-item reads go through the section 8.2 query functions on
    // `Program`, which record into this body's read set. Bodies ask in
    // their own module (the root in single-file programs).
    /// The body item a name denotes in the enclosing blocks, innermost first.
    fn body_item_of(&self, name: Sym, ctxt: CtxtId) -> Option<crate::check::collect::BodyItem> {
        for layer in self.item_scopes.iter().rev() {
            for &(n, idx) in layer.iter().rev() {
                if n == (name, ctxt) {
                    return self.p.body_items.get(&idx).copied();
                }
            }
        }
        None
    }

    fn binding(&mut self, ns: Namespace, name: Sym) -> BindingRes {
        let p = self.p;
        let module = self.module;
        p.binding(&mut self.out.reads, module, ns, name)
    }

    /// A primitive associated const used as a pattern (`u8::MAX`,
    /// `char::MAX`): its value and type, if the path names one.
    fn primitive_const_pattern(&mut self, segs: &[ast::PathSeg]) -> Option<(crate::ty::consteval::ConstValue, Ty)> {
        use crate::ty::consteval::ConstValue;
        if segs.len() != 2 {
            return None;
        }
        let item = self.name(segs[1].name);
        if let Some(it) = self.p.known.int_ty(segs[0].name) {
            let t = int(it);
            let v = match item {
                "MAX" => crate::ty::consteval::truncate_to_int(it.max128() as i128, it),
                "MIN" => {
                    if it.signed() {
                        if it.bits() >= 128 { i128::MIN } else { -(1i128 << (it.bits() - 1)) }
                    } else {
                        0
                    }
                }
                "BITS" => return Some((ConstValue::Int(it.bits() as i128), int(IntTy::U32))),
                _ => return None,
            };
            // u128::MAX is stored as its raw bits, as in the evaluator.
            let v = if it == IntTy::U128 && item == "MAX" { -1 } else { v };
            return Some((ConstValue::Int(v), t));
        }
        if segs[0].name == self.p.known.char {
            let c = match item {
                "MAX" => char::MAX,
                "MIN" => char::MIN,
                "REPLACEMENT_CHARACTER" => char::REPLACEMENT_CHARACTER,
                _ => return None,
            };
            return Some((ConstValue::Char(c), CHAR));
        }
        None
    }

    /// What a lone identifier in a pattern resolves to through the
    /// module bindings (imports included): a const item, a static, or
    /// a unit variant or struct constructor. Anything else stays a
    /// fresh binding. The binding query records the read, so a body
    /// rechecks when the name's target changes.
    fn pat_ident(&mut self, name: Sym) -> PatIdent {
        use crate::resolve::imports::{BindState, Target};
        let p = self.p;
        if let BindingRes::Def(def) = self.binding(Namespace::Value, name) {
            let flat = p.resolved.as_ref().and_then(|t| t.def_info.get(&def)).map(|i| i.flat);
            match p.binding_kind(def) {
                Some(DefsKind::Const) => {
                    if let Some(i) = p.const_by_def(def).or_else(|| flat.and_then(|f| p.const_names.get(&f).copied())) {
                        return PatIdent::Const(i);
                    }
                }
                Some(DefsKind::Static) => {
                    if p.static_by_def(def).or_else(|| flat.and_then(|f| p.static_names.get(&f).copied())).is_some() {
                        return PatIdent::Static;
                    }
                }
                _ => {}
            }
            if let Some(a) = p.adt_by_def(def).or_else(|| flat.and_then(|f| p.type_names.get(&f).copied())) {
                if p.adt(a).is_enum {
                    // A variant import answers with the enum's def in
                    // the binding query; the raw table keeps the variant.
                    if let Some(tables) = &p.resolved
                        && let Some(BindState::One(b)) = tables.lookup(self.module, Namespace::Value, name)
                        && let Target::Variant(vdef, vname) = b.target
                        && vdef == def
                        && let Some(v) = p.adt(a).variants.iter().position(|x| x.name == vname)
                    {
                        return PatIdent::Variant(a, v as u32);
                    }
                    return PatIdent::Other;
                }
                return PatIdent::Variant(a, 0);
            }
        }
        // Without resolver tables the flat name maps answer directly.
        if let Some(&i) = p.const_names.get(&name) {
            return PatIdent::Const(i);
        }
        if p.static_names.contains_key(&name) {
            return PatIdent::Static;
        }
        if let Some(&a) = p.type_names.get(&name)
            && !p.adt(a).is_enum
        {
            return PatIdent::Variant(a, 0);
        }
        PatIdent::Other
    }

    /// Field visibility (ARCH 1.5): a private field of a struct from
    /// another module is L0510. Only resolver-built programs carry the
    /// field table; single-file programs are all one module. Every
    /// member privacy check here records a `Sig(adt)` read: that
    /// fingerprint covers the Adt's field and associated item
    /// visibility (driver/graph.rs `hash_vis_facts`), so the dirty walk
    /// rechecks this body when a visibility it asked about changes.
    fn check_field_vis(&mut self, a: AdtId, field: Sym, span: Span) {
        let p = self.p;
        // The fields of std's structs are private to std.
        if generics::is_std_adt(&p.tys, a) {
            let name = self.name(field).to_string();
            self.err("L0510", span, format!("field `{name}` is private"), "Use the type's methods instead.");
            return;
        }
        let Some(tables) = &p.resolved else { return };
        let def = p.def_of_adt(a);
        let _ = p.sig_of(&mut self.out.reads, def);
        if let Some((def_mod, fields)) = tables.field_vis.get(&def)
            && let Some(vis) = fields.get(&field)
            && !tables.visible(vis, *def_mod, self.module, p.interner)
        {
            let name = self.name(field).to_string();
            self.err(
                "L0510",
                span,
                format!("field `{name}` is private"),
                "Make the field `pub(crate)` (the smallest widening that works).",
            );
        }
    }

    /// Tuple-field visibility, like `check_field_vis` for `t.1` forms.
    fn check_tuple_field_vis(&mut self, a: AdtId, index: u32, span: Span) {
        let p = self.p;
        let Some(tables) = &p.resolved else { return };
        let def = p.def_of_adt(a);
        let _ = p.sig_of(&mut self.out.reads, def);
        if let Some((def_mod, fields)) = tables.tuple_field_vis.get(&def)
            && let Some(vis) = fields.get(index as usize)
            && !tables.visible(vis, *def_mod, self.module, p.interner)
        {
            self.err(
                "L0510",
                span,
                format!("field `{index}` is private"),
                "Make the field `pub(crate)` (the smallest widening that works).",
            );
        }
    }

    /// A tuple struct constructor is private when any of its fields is
    /// (rustc E0603), for calls and patterns alike.
    fn check_ctor_vis(&mut self, a: AdtId, span: Span) {
        let p = self.p;
        let Some(tables) = &p.resolved else { return };
        let def = p.def_of_adt(a);
        let _ = p.sig_of(&mut self.out.reads, def);
        if let Some((def_mod, fields)) = tables.tuple_field_vis.get(&def)
            && fields.iter().any(|vis| !tables.visible(vis, *def_mod, self.module, p.interner))
        {
            let name = p.display_path(p.adt(a).name);
            self.err(
                "L0510",
                span,
                format!("tuple struct constructor `{name}` is private"),
                "Make every field `pub(crate)`, or add a public constructor function.",
            );
        }
    }

    /// Inherent method visibility for a method call on a user type.
    fn check_method_vis(&mut self, base: Ty, name: Sym, span: Span) {
        if let Some(a) = self.tys.local_adt(base) {
            self.check_assoc_vis(a, name, "method", span);
        }
    }

    /// Inherent associated item visibility: a method call, or a
    /// `Self::item` or `Type::item` path that check resolves. The
    /// resolver checks written type paths as well; `Self` paths reach
    /// only this check. `what` names the item kind in the message.
    fn check_assoc_vis(&mut self, a: AdtId, name: Sym, what: &str, span: Span) {
        let p = self.p;
        let Some(tables) = &p.resolved else { return };
        let def = p.def_of_adt(a);
        let _ = p.sig_of(&mut self.out.reads, def);
        if let Some(items) = tables.assoc_vis.get(&def)
            && let Some((vis, def_mod)) = items.get(&name)
            && !tables.visible(vis, *def_mod, self.module, p.interner)
        {
            self.err(
                "L0510",
                span,
                format!("{what} `{}` is private", self.name(name)),
                format!("Make the {what} `pub(crate)` (the smallest widening that works)."),
            );
        }
    }

    /// Visibility of an `impl dyn Tr` method a call picked (rustc E0624):
    /// its written visibility, from the module of its impl. The method's
    /// `Sig` read covers both, so a warm caller rechecks when either moves.
    fn check_dyn_method_vis(&mut self, f: LocalDefId, span: Span) {
        let p = self.p;
        let Some(tables) = &p.resolved else { return };
        let _ = p.sig_of(&mut self.out.reads, p.def_id(f));
        let info = p.fn_info(f);
        let vis = crate::resolve::imports::vis_from_ast(&info.def.vis, p.interner);
        if !tables.visible(&vis, defining_module(p, f), self.module, p.interner) {
            self.err(
                "L0510",
                span,
                format!("method `{}` is private", self.name(info.name)),
                "Make the method `pub(crate)` (the smallest widening that works).",
            );
        }
    }

    /// The tuple struct a value binding names as a constructor, if it names one.
    fn tuple_struct_ctor(&mut self, name: Sym) -> Option<AdtId> {
        // `Self(..)` in an impl of a tuple struct (its args are the
        // impl's, see `self_path_args`).
        if name == self.p.known.self_type {
            return self.self_adt().filter(|&a| !self.p.adt(a).is_enum && self.p.adt(a).variants[0].shape == VariantShape::Tuple);
        }
        match self.binding(Namespace::Value, name) {
            BindingRes::Def(def) => match self.p.adt_by_def(def) {
                Some(a) if !self.p.adt(a).is_enum && self.p.adt(a).variants[0].shape == VariantShape::Tuple => Some(a),
                _ => None,
            },
            _ => None,
        }
    }

    /// The `fn(params) -> ret` pointer type for a signature.
    fn fn_ptr_ty(&mut self, params: &[Ty], ret: Ty) -> Ty {
        let inputs = self.tys.intern_tys(params);
        let sig =
            self.tys.intern_sig(crate::ty::Binder::plain(crate::ty::FnSig { inputs, output: ret, is_unsafe: false, extern_c: false }));
        self.tys.intern(TyKind::FnPtr(sig))
    }

    /// The zero-sized fn-item type of a fn used as a value. A generic
    /// fn named by a plain path instantiates as a call does (turbofish
    /// args or fresh variables, bounds queued, the site recorded for
    /// mono), and its `FnDef` carries those args. Qualified paths
    /// (`<S as Tr>::mk`) to generic fns are not supported yet.
    fn fn_value_ty(&mut self, e: ExprId, f: LocalDefId, span: Span) -> Ty {
        if let Some(Some(tmpl)) = self.p.gx.fn_templates.get(f.0 as usize).cloned() {
            if !matches!(self.p.ast.expr(e), Expr::Path(_)) {
                self.errs.push(not_yet("L0614", span, "generic functions as values through a qualified path"));
                return ERROR;
            }
            let explicit = self.explicit_call_args(e);
            let (_, _, args) = self.instantiate_template(e, f, &tmpl.generics, &explicit, span);
            self.unify_written_self(e, f, &args, span);
            let args = self.tys.intern_args(&args);
            return self.tys.intern(TyKind::FnDef(self.p.def_id(f), args));
        }
        self.unify_written_self(e, f, &[], span);
        self.tys.intern(TyKind::FnDef(self.p.def_id(f), EMPTY_ARGS))
    }

    /// An inherent fn as a value through a qualified path (`<W<u16>>::get`):
    /// a generic impl's fn instantiates as on a plain path, with the
    /// written Self type fixing the impl's params.
    fn inherent_qpath_fn_value(&mut self, e: ExprId, f: LocalDefId, base: Ty, span: Span) -> Ty {
        let p = self.p;
        if p.gx.fn_templates.get(f.0 as usize).is_none_or(|t| t.is_none()) {
            return self.fn_value_ty(e, f, span);
        }
        let Some(self_tmpl) = p.gx.fn_scopes.get(f.0 as usize).and_then(|s| s.scope.self_ty) else {
            self.errs.push(not_yet("L0614", span, "generic functions as values through a qualified path"));
            return ERROR;
        };
        let t = self.fn_value_ty_prefixed(e, f, &[], span);
        if let TyKind::FnDef(_, args) = self.kind(t) {
            let args: Vec<GenericArg> = self.tys.args(args).to_vec();
            let self_ty = subst(&mut self.tys, self_tmpl, &args);
            if !self.unify(self_ty, base) {
                self.mismatch(span, base, self_ty);
            }
        }
        t
    }

    /// `fn_value_ty` for a fn whose leading generic args are already
    /// known (a trait fn through a qualified path: the selected impl's
    /// args); the fn's own params come from the path's turbofish
    /// (`<S as Tr>::conv::<u32>`), else fresh variables.
    fn fn_value_ty_prefixed(&mut self, e: ExprId, f: LocalDefId, prefix: &[GenericArg], span: Span) -> Ty {
        let Some(Some(tmpl)) = self.p.gx.fn_templates.get(f.0 as usize).cloned() else {
            return self.tys.intern(TyKind::FnDef(self.p.def_id(f), EMPTY_ARGS));
        };
        let mut explicit: Vec<Option<GenericArg>> = prefix.iter().map(|&g| Some(g)).collect();
        if let Expr::QPath { segs, .. } = self.p.ast.expr(e)
            && let Some(last) = segs.last()
        {
            for t in last.type_args() {
                explicit.push(Some(GenericArg::Ty(self.resolve_written(t))));
            }
        }
        let (_, _, args) = self.instantiate_template(e, f, &tmpl.generics, &explicit, span);
        let args = self.tys.intern_args(&args);
        self.tys.intern(TyKind::FnDef(self.p.def_id(f), args))
    }

    /// The type of a unit struct used as a value. A generic one (const
    /// params only: rustc rejects an unused type param) takes its args
    /// from the path's turbofish (`S::<7>`) or fresh variables, with its
    /// bounds queued, as the tuple constructor below does.
    fn unit_value_ty(&mut self, e: ExprId, a: AdtId, span: Span) -> Ty {
        let p = self.p;
        let generics = p.gx.adt_generics[a.0 as usize].clone();
        if generics.params.is_empty() {
            return self.tys.adt_ty(a);
        }
        let args = match p.ast.expr(e) {
            Expr::Path(segs) => self.value_path_args(a, segs, span),
            _ => self.fresh_args(&generics),
        };
        if !generics.predicates.is_empty() {
            self.push_predicates(&generics.predicates, &args, span);
        }
        self.tys.mk_adt(p.def_of_adt(a), &args)
    }

    /// The callable-item type of a tuple struct or tuple variant
    /// constructor used as a value. It is an `FnDef` over the Adt def
    /// with the variant index as its first (const) argument, so a later
    /// call through the value can decode which constructor it is. A
    /// generic Adt's args follow (`.map(W)`): from the path's turbofish
    /// or fresh variables, with the Adt's bounds queued, as a call of
    /// the constructor does.
    fn ctor_value_ty(&mut self, e: ExprId, a: AdtId, v: u32, span: Span) -> Ty {
        let p = self.p;
        let c = self.tys.intern_const(ConstKind::Int(v as u128));
        let mut args = vec![GenericArg::Const(c)];
        let generics = p.gx.adt_generics[a.0 as usize].clone();
        if !generics.params.is_empty() {
            let gen_args = match p.ast.expr(e) {
                Expr::Path(segs) => self.value_path_args(a, segs, span),
                _ => self.fresh_args(&generics),
            };
            if !generics.predicates.is_empty() {
                self.push_predicates(&generics.predicates, &gen_args, span);
            }
            args.extend(gen_args);
        }
        let args = self.tys.intern_args(&args);
        self.tys.intern(TyKind::FnDef(p.def_of_adt(a), args))
    }

    /// The item type of a builtin constructor or std fn used as a value
    /// (`.map(Some)`, `Result::Err`, `.map(Rc::new)`,
    /// `.map(String::from)`): an `FnDef` over the builtin Adt def.
    /// `Some`, `Ok`, and `Err` put the variant first as a const arg
    /// (Some 1, Ok 0, Err 1), then the Adt's args; `Box::new`,
    /// `Rc::new`, and `String::from` have their one input type. Args
    /// come from the turbofish or fresh variables. `builtin_item_res`
    /// decodes the item.
    fn builtin_item_value(&mut self, e: ExprId, r: Res, segs: &[ast::PathSeg], span: Span) -> Ty {
        let b = self.tys.builtins();
        let (def, variant) = match r {
            Res::OptSome => (b.option, Some(1)),
            Res::ResOk => (b.result, Some(0)),
            Res::ResErr => (b.result, Some(1)),
            Res::Builtin(Builtin::BoxNew) => (b.boxed, None),
            Res::Builtin(Builtin::RcNew) => (b.rc, None),
            _ => (b.string, None),
        };
        let tys = if def == b.string {
            // `From::from` has no params of its own: the input is open
            // until a use fixes it, then it must be a form lust's
            // `String::from` takes (checked at finish).
            if segs.iter().any(|s| !s.type_args().is_empty()) {
                self.err("L0107", span, "`String::from` takes no generic arguments", "Remove the generic arguments.");
            }
            let t = self.new_var(false);
            self.deferred_string_from.push((t, span));
            vec![t]
        } else if variant.is_none() && segs.last().is_some_and(|s| !s.type_args().is_empty()) {
            // `Box::new` and `Rc::new` have no params of their own; the
            // element type goes on the type (`Box::<u8>::new`).
            self.err("L0107", span, "this associated function takes no generic arguments", "Write the type's argument instead: `Box::<T>::new`.");
            vec![self.new_var(false)]
        } else {
            let n = if def == b.result { 2 } else { 1 };
            match self.builtin_ctor_args(segs, n, span) {
                Some(a) => a,
                None => (0..n).map(|_| self.new_var(false)).collect(),
            }
        };
        self.set_res(e, r);
        let mut args: Vec<GenericArg> = variant.map(|v| GenericArg::Const(self.tys.intern_const(ConstKind::Int(v)))).into_iter().collect();
        args.extend(tys.into_iter().map(GenericArg::Ty));
        let args = self.tys.intern_args(&args);
        self.tys.intern(TyKind::FnDef(def, args))
    }

    /// The call a builtin item over a builtin Adt def makes (see
    /// `builtin_item_value`), with the item's (params, return).
    fn builtin_item_res(&mut self, def: DefId, args: ArgsId) -> Option<(Res, Vec<Ty>, Ty)> {
        let b = self.tys.builtins();
        let a: Vec<Ty> = self.tys.args(args).iter().filter_map(|g| g.as_ty()).collect();
        Some(match a.as_slice() {
            &[t] if def == b.option => (Res::OptSome, vec![t], self.tys.mk_option(t)),
            &[t, e] if def == b.result && self.ctor_variant(args) == 0 => (Res::ResOk, vec![t], self.tys.mk_result(t, e)),
            &[t, e] if def == b.result => (Res::ResErr, vec![e], self.tys.mk_result(t, e)),
            &[t] if def == b.boxed => (Res::Builtin(Builtin::BoxNew), vec![t], self.tys.mk_boxed(t)),
            &[t] if def == b.rc => (Res::Builtin(Builtin::RcNew), vec![t], self.tys.mk_rc(t)),
            &[t] if def == b.string => (Res::Builtin(Builtin::StringFrom), vec![t], STRING),
            _ => return None,
        })
    }

    /// The variant a constructor `FnDef` type names, from its const arg.
    fn ctor_variant(&self, args: ArgsId) -> u32 {
        match self.tys.args(args).first() {
            Some(GenericArg::Const(c)) => match self.tys.const_kind(*c) {
                ConstKind::Int(v) => v as u32,
                _ => 0,
            },
            _ => 0,
        }
    }

    /// The (params, return) signature of a callable type: a fn pointer,
    /// a fn item, or a constructor item.
    fn callable_sig(&mut self, t: Ty) -> Option<(Vec<Ty>, Ty)> {
        let p = self.p;
        match self.kind(t) {
            TyKind::FnPtr(sig) => {
                let s = self.tys.sig(sig).value;
                Some((self.tys.tys_of(s.inputs).to_vec(), s.output))
            }
            TyKind::FnDef(def, args) => {
                if let Some((_, params, ret)) = self.builtin_item_res(def, args) {
                    return Some((params, ret));
                }
                if let Some(a) = p.adt_by_def(def) {
                    let v = self.ctor_variant(args);
                    let variant = &p.adt(a).variants[v as usize];
                    // A generic Adt's args follow the variant (see
                    // `ctor_value_ty`).
                    let adt_args: Vec<GenericArg> = self.tys.args(args).iter().skip(1).copied().collect();
                    if adt_args.is_empty() {
                        let params = variant.fields.iter().map(|f| f.ty).collect();
                        return Some((params, self.tys.adt_ty(a)));
                    }
                    let fields: Vec<Ty> = variant.fields.iter().map(|f| f.ty).collect();
                    let params = fields.into_iter().map(|t| self.subst_settled(t, &adt_args)).collect();
                    Some((params, self.tys.mk_adt(def, &adt_args)))
                } else {
                    let f = p.local_def(def.hash)?;
                    let fargs: Vec<GenericArg> = self.tys.args(args).to_vec();
                    match p.sig_of(&mut self.out.reads, def) {
                        SigOf::Fn(info) if fargs.is_empty() => Some((info.params.clone(), p.ret_view(f))).map(|(ps, r)| (ps, self.callee_ret(r))),
                        // A generic fn item: its signature under the
                        // item's args (see `fn_value_ty`).
                        SigOf::Fn(info) => {
                            let params = info.params.iter().map(|&t| self.subst_settled(t, &fargs)).collect();
                            Some((params, self.subst_settled(info.ret, &fargs)))
                        }
                        _ => None,
                    }
                }
            }
            _ => None,
        }
    }

    /// rustc's LUB of two fn or constructor items: the same item (args
    /// that unify) keeps its zero-sized type, and only differing items
    /// reify to a fn pointer. Unifies the args when it answers true.
    fn same_fn_item(&mut self, a: Ty, b: Ty) -> bool {
        let (a, b) = (self.resolve(a), self.resolve(b));
        let (TyKind::FnDef(da, _), TyKind::FnDef(db, _)) = (self.kind(a), self.kind(b)) else { return false };
        if da != db {
            return false;
        }
        let snap = self.snapshot_vars();
        if self.unify(a, b) {
            return true;
        }
        self.rollback_vars(snap);
        false
    }

    /// True when `t` is a plain fn's item type (not a constructor), so it
    /// coerces to a function pointer backed by a slot trampoline.
    fn is_fn_item(&self, t: Ty) -> bool {
        match self.kind(t) {
            TyKind::FnDef(def, _) => self.p.is_fn_item_def(def),
            _ => false,
        }
    }

    /// The free fn a value binding names, if it names one.
    fn binding_fn(&mut self, name: Sym) -> Option<LocalDefId> {
        match self.binding(Namespace::Value, name) {
            BindingRes::Def(def) if self.p.binding_kind(def) == Some(DefsKind::Fn) => self.p.local_def(def.hash),
            _ => None,
        }
    }

    // ---------- Obligations (ARCH 2.4) ----------

    /// Binds one inference variable, recording it on the probe
    /// trail so solver probes can roll back (see `SolveCx`).
    fn bind_var(&mut self, var: u32, t: Ty) {
        self.trail.push(var);
        self.vars[var as usize].bound = Some(t);
    }

    /// A probe snapshot of the variable bindings (see `SolveCx`).
    fn snapshot_vars(&mut self) -> usize {
        <Self as SolveCx>::snapshot(self)
    }

    /// Rolls variable bindings back to a probe snapshot.
    fn rollback_vars(&mut self, snap: usize) {
        <Self as SolveCx>::rollback(self, snap);
    }

    /// True when a fn item's signature unifies with a fn pointer type
    /// (binding inference variables on either side). A failed probe
    /// rolls its bindings back.
    fn fn_item_ptr_unifies(&mut self, item: Ty, ptr: Ty) -> bool {
        let Some((params, ret)) = self.callable_sig(item) else { return false };
        let fp = self.fn_ptr_ty(&params, ret);
        let snap = self.snapshot_vars();
        if self.unify(fp, ptr) {
            return true;
        }
        self.rollback_vars(snap);
        false
    }

    /// How many obligations wait, for probe rollback.
    fn obl_len(&self) -> usize {
        self.obl.len()
    }

    /// Drops obligations queued since an `obl_len` snapshot.
    fn obl_truncate(&mut self, len: usize) {
        self.obl.truncate(len);
    }

    /// A fresh const inference variable.
    fn fresh_const_var(&mut self) -> ConstId {
        let id = self.next_const_id;
        self.next_const_id += 1;
        self.tys.intern_const(ConstKind::Infer(id))
    }

    /// The const a const inference variable bound to, if any.
    fn resolve_const(&self, c: ConstId) -> ConstId {
        match self.tys.const_kind(c) {
            ConstKind::Infer(id) if id >= generics::INFER_MARKER_BASE => self.const_bindings.get(&id).copied().unwrap_or(c),
            _ => c,
        }
    }

    /// Unifies two consts, binding a const inference variable. The
    /// binding goes on the probe trail (its id is at or above
    /// `INFER_MARKER_BASE`, never a type variable index), so a rolled
    /// back probe drops it like a type binding.
    fn unify_const(&mut self, a: ConstId, b: ConstId) -> bool {
        let (a, b) = (self.resolve_const(a), self.resolve_const(b));
        if a == b {
            return true;
        }
        match (self.tys.const_kind(a), self.tys.const_kind(b)) {
            (ConstKind::Infer(x), _) if x >= generics::INFER_MARKER_BASE => {
                self.const_bindings.insert(x, b);
                self.trail.push(x);
                true
            }
            (_, ConstKind::Infer(x)) if x >= generics::INFER_MARKER_BASE => {
                self.const_bindings.insert(x, a);
                self.trail.push(x);
                true
            }
            _ => false,
        }
    }

    /// Fresh instantiation arguments for one generics list, by
    /// parameter kind (used for Adt applications at literals).
    fn fresh_args(&mut self, generics: &Generics) -> Vec<GenericArg> {
        generics
            .params
            .iter()
            .map(|param| match param.kind {
                ParamKind::Type => GenericArg::Ty(self.new_var(false)),
                ParamKind::Lifetime => GenericArg::Lifetime(Region::Erased),
                ParamKind::Const(_) => GenericArg::Const(self.fresh_const_var()),
            })
            .collect()
    }

    /// The user Adt and args a non-generic type alias names (`type EA =
    /// E<u8>;`): value paths and patterns through the alias (`EA::A(3)`,
    /// `SA { .. }`) build or match that Adt at those args. None when
    /// `name` is not such an alias.
    fn alias_adt(&mut self, name: Sym) -> Option<(AdtId, Vec<GenericArg>)> {
        let p = self.p;
        if p.aliases.is_empty() {
            return None;
        }
        let flat = match self.binding(Namespace::Type, name) {
            BindingRes::Def(def) => p.resolved.as_ref().and_then(|t| t.def_info.get(&def)).map_or(name, |i| i.flat),
            _ => name,
        };
        let &t = p.aliases.get(&flat)?;
        let (d, args) = p.tys.adt_parts(t)?;
        let a = p.adt_by_def(d)?;
        Some((a, p.tys.args(args).to_vec()))
    }

    /// `alias_adt` for the type segment of a value path, generic
    /// aliases too: a generic alias's body under the segment's type
    /// args (`A::<u8>::make`), fresh variables when none are written
    /// (`type A<T> = S<T>; A::make(5)`), and the defaults of the
    /// missing ones otherwise. The bool is true for a generic alias,
    /// whose written args are its own, not the Adt's.
    fn alias_adt_seg(&mut self, seg: &ast::PathSeg, span: Span) -> Option<(AdtId, Vec<GenericArg>, bool)> {
        if let Some((a, args)) = self.alias_adt(seg.name) {
            return Some((a, args, false));
        }
        let p = self.p;
        if p.gx.generic_aliases.is_empty() {
            return None;
        }
        let flat = match self.binding(Namespace::Type, seg.name) {
            BindingRes::Def(def) => p.resolved.as_ref().and_then(|t| t.def_info.get(&def)).map_or(seg.name, |i| i.flat),
            _ => return None,
        };
        let la = p.gx.generic_aliases.get(&flat)?.clone();
        let written = seg.type_args();
        if written.len() > la.type_params.len() {
            self.err("L0107", span, format!("this alias takes {} type argument(s)", la.type_params.len()), "Write one type per parameter.");
            return None;
        }
        let mut body = generics::Scope {
            alias_lifetimes: la.lifetimes.iter().map(|&n| (n, Region::Erased)).collect(),
            alias_depth: 1,
            ..Default::default()
        };
        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
        for (i, &(name, default)) in la.type_params.iter().enumerate() {
            // rustc infers every param when no args are written, and
            // takes the missing ones' defaults otherwise (E0107 when one
            // has none).
            let t = match (written.get(i), default) {
                (Some(&w), _) => self.resolve_written(w),
                _ if written.is_empty() => self.new_var(false),
                (None, Some(d)) => generics::resolve_scoped(p.ast, p.interner, p.known, &cx, &mut self.tys, d, &body).ok()?,
                (None, None) => {
                    self.err("L0107", span, format!("this alias takes {} type argument(s)", la.type_params.len()), "Write one type per parameter.");
                    return None;
                }
            };
            body.param_tys.push((name, t));
        }
        let t = generics::resolve_scoped(p.ast, p.interner, p.known, &cx, &mut self.tys, la.ty, &body).ok()?;
        let (d, args) = self.tys.adt_parts(t)?;
        let a = p.adt_by_def(d)?;
        Some((a, self.tys.args(args).to_vec(), true))
    }

    /// The args of a value path through `Self` (`Self::V(..)`, `Self {
    /// .. }`, `Self(..)`, `Self::N` in patterns too): `Self` names the
    /// impl's Self type with its own args, never a fresh application of
    /// the Adt (rustc E0308 for `Self::V(5u16)` in `impl<T> G<T>`).
    /// None when the path's type segment is not `Self` or `Self` is not
    /// an application of `a`.
    fn self_path_args(&mut self, a: AdtId, segs: &[ast::PathSeg], span: Span) -> Option<Vec<GenericArg>> {
        let p = self.p;
        let ty_seg = &segs[segs.len().saturating_sub(2)];
        if ty_seg.name != p.known.self_type {
            return None;
        }
        let st = self.resolve(self.body_scope.self_ty?);
        let (d, args) = self.tys.adt_parts(st)?;
        if d != p.def_of_adt(a) {
            return None;
        }
        let args = self.tys.args(args).to_vec();
        if segs.iter().any(|s| s.has_args()) {
            self.err(
                "L0110",
                span,
                "type arguments are not allowed on a path through `Self`",
                "Remove the `::<..>` part: `Self` already names the impl's type with its arguments.",
            );
            return Some(self.error_args(&p.gx.adt_generics[a.0 as usize].clone()));
        }
        Some(args)
    }

    /// The generic args of a value path that names user Adt `a` (a
    /// struct, or an enum through one of its variants): args written on
    /// the type segment or the variant segment, with the defaults of
    /// omitted trailing params. With no args written every param gets a
    /// fresh variable, as rustc infers them there (defaults never apply).
    fn value_path_args(&mut self, a: AdtId, segs: &[ast::PathSeg], span: Span) -> Vec<GenericArg> {
        let p = self.p;
        if let Some(args) = self.self_path_args(a, segs, span) {
            return args;
        }
        // A path through an alias of a generic Adt builds the Adt at the
        // alias's args: fixed ones (`type EA = E<u8>; EA::A(3)`), or a
        // generic alias's at the segment's args (`A::<u8>::make`).
        if let Some((aa, args, generic)) = self.alias_adt_seg(&segs[segs.len().saturating_sub(2)], span)
            && p.def_of_adt(aa) == p.def_of_adt(a)
            && !args.is_empty()
        {
            let stray = if generic { segs.len() >= 2 && segs[segs.len() - 1].has_args() } else { segs.iter().any(|s| s.has_args()) };
            if stray {
                self.err("L0105", span, "these generic arguments do not belong here", "Write the type's arguments on the alias only: `A::<u8>::name`.");
                return self.error_args(&p.gx.adt_generics[a.0 as usize].clone());
            }
            return args;
        }
        let generics = p.gx.adt_generics[a.0 as usize].clone();
        let n = segs.len();
        let written_on: Vec<&ast::PathSeg> = segs[n.saturating_sub(2)..].iter().filter(|s| s.has_args()).collect();
        let seg = match written_on.as_slice() {
            [] => return self.fresh_args(&generics),
            [one] => *one,
            _ => {
                self.err(
                    "L0110",
                    span,
                    "type arguments are not allowed on both the type and the variant",
                    "Write the arguments on one segment only.",
                );
                return self.error_args(&generics);
            }
        };
        let ast::GenericArgs::Angle(written) = &seg.args else {
            self.err("L0110", span, "parenthesized arguments are only for Fn traits", "Use angle arguments.");
            return self.error_args(&generics);
        };
        let mut args: Vec<GenericArg> = Vec::new();
        for (i, w) in written.iter().filter(|w| !matches!(w, ast::GenericArg::Lifetime(_))).enumerate() {
            let is_const = matches!(generics.params.get(i).map(|g| g.kind), Some(ParamKind::Const(_)));
            let arg = match w {
                ast::GenericArg::Type(t) if !is_const => Some(GenericArg::Ty(self.resolve_written(*t))),
                // As on a call path (`S::<true>` is a bool, `S::<{ -1 }>`
                // a negative int), then the written form's type.
                ast::GenericArg::Const(e) => {
                    let g = self.const_call_arg(*e);
                    if let (GenericArg::Const(c), Some(ParamKind::Const(t))) = (g, generics.params.get(i).map(|g| g.kind))
                        && let Some(want) = generics::ConstScalar::of(&self.tys, t)
                    {
                        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                        let typed = generics::check_const_expr_ty(
                            p.ast,
                            p.interner,
                            p.known,
                            &cx,
                            &mut self.tys,
                            &self.body_scope,
                            *e,
                            c,
                            want,
                            span,
                            "this const argument",
                        );
                        if let Err(d) = typed {
                            self.errs.push(d);
                            return self.error_args(&generics);
                        }
                    }
                    Some(g)
                }
                ast::GenericArg::Type(t) => match p.ast.ty(*t) {
                    ast::TyExpr::Path(ps) if ps.len() == 1 => match self.const_param(ps[0].name) {
                        Some((pi, _, val)) => Some(GenericArg::Const(self.tys.intern_const(val.unwrap_or(ConstKind::Param(pi))))),
                        None => crate::check::collect::named_const_kind(p.ast, p.interner, p.known, ps[0].name)
                            .map(|k| GenericArg::Const(self.tys.intern_const(k))),
                    },
                    _ => None,
                },
                _ => None,
            };
            match arg {
                Some(g) => args.push(g),
                None => {
                    self.err(
                        "L0110",
                        span,
                        "this generic argument form is not supported here",
                        "Write a type, or a literal const argument.",
                    );
                    return self.error_args(&generics);
                }
            }
        }
        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
        let g_ast = crate::check::defaults::type_generics(p.ast, &cx, p.adt(a).name);
        let min = g_ast.map_or(generics.params.len(), crate::check::defaults::required);
        if args.len() < min || args.len() > generics.params.len() {
            self.err(
                "L0105",
                span,
                format!(
                    "`{}` takes {} generic argument(s) but {} were given",
                    p.display_path(p.adt(a).name),
                    generics.params.len(),
                    args.len()
                ),
                "Write one argument per parameter, or leave them all out to infer them.",
            );
            return self.error_args(&generics);
        }
        if let Some(g) = g_ast
            && let Err(d) = crate::check::defaults::fill(
                p.ast,
                p.interner,
                p.known,
                &cx,
                &mut self.tys,
                &generics::Scope::default(),
                g,
                None,
                &mut args,
                span,
            )
        {
            self.errs.push(d);
            return self.error_args(&generics);
        }
        if !self.check_const_args(&generics, &args, span) {
            return self.error_args(&generics);
        }
        args
    }

    /// Args for a generics list after a reported error: the error type
    /// for every type param, so no second error follows from them.
    fn error_args(&mut self, generics: &Generics) -> Vec<GenericArg> {
        generics
            .params
            .iter()
            .map(|param| match param.kind {
                ParamKind::Lifetime => GenericArg::Lifetime(Region::Erased),
                ParamKind::Const(_) => GenericArg::Const(self.fresh_const_var()),
                ParamKind::Type => GenericArg::Ty(ERROR),
            })
            .collect()
    }

    /// This body's elaborated param env.
    fn env(&self) -> &'p [Predicate] {
        self.p.gx.fn_scopes.get(self.fid.0 as usize).map_or(&[], |fs| &fs.env)
    }

    /// The env selection and normalization use: `env()`, plus the bounds
    /// of the callee opaque types met so far (`opaque::note_opaques`).
    fn solve_env(&self) -> std::borrow::Cow<'p, [Predicate]> {
        if self.opaque_env.is_empty() { std::borrow::Cow::Borrowed(self.env()) } else { std::borrow::Cow::Owned(self.opaque_env.clone()) }
    }

    /// Normalizes one type here (section 2.5) through this body's
    /// solver. The solver state is taken out for the call because
    /// the context itself is the `SolveCx`.
    fn normalize_here(&mut self, t: Ty) -> Ty {
        if !self.tys.flags(t).contains_projection() {
            return t;
        }
        let p = self.p;
        self.note_opaques(t);
        let env = self.solve_env();
        let mut solver = std::mem::take(&mut self.solver);
        let out = crate::traits::solve::normalize(&mut solver, self, &p.gx.index, &env, t);
        self.solver = solver;
        out
    }

    /// Selects evidence for one trait obligation, with the
    /// structural answers of sections 2.7 (`Sized`, auto traits)
    /// and the derive-family queries ahead of the general solver
    /// where they are exact. Commits bindings on success, like
    /// `Solver::select`.
    fn select_obligation(&mut self, tr: TraitRef) -> Selection {
        self.select_obligation_at(tr, Span::default(), 0)
    }

    /// `select_obligation` at one nesting depth: a confirmed
    /// impl's nested predicates are queued at depth + 1, so a
    /// self-referential impl (`impl<X> T for Vec<X> where
    /// Vec<X>: T`) overflows through the queue (section 2.4
    /// step 7) instead of looping. Synchronous callers pass the
    /// span to blame and depth 0.
    fn select_obligation_at(&mut self, tr: TraitRef, span: Span, depth: u16) -> Selection {
        let p = self.p;
        let lang = &p.gx.lang;
        // Projections in the trait ref normalize first: an
        // associated bound like `<Local2 as IntoIter>::It: Iter`
        // selects against the concrete iterator type.
        let tr = {
            let raw: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
            let normed: Vec<GenericArg> = raw
                .iter()
                .map(|&g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(self.normalize_here(t)),
                    other => other,
                })
                .collect();
            let args = self.tys.intern_args(&normed);
            TraitRef { args, ..tr }
        };
        let self_ty = self.deep(self.tys.args(tr.args)[0].as_ty().unwrap_or(ERROR));
        if tr.def == lang.sized {
            // A general variable may still become `[T]`, `str`, a dyn
            // type, or a `?Sized` param's stand-in (`f(s)` runs this
            // queue before the argument unifies): keep the obligation
            // until the variable is known.
            if matches!(self.tys.kind(self_ty), TyKind::Infer(v) if !v.is_int() && !v.is_float()) {
                return Selection::Ambiguous;
            }
            return if self.sized_ok(self_ty) { Selection::ParamEvidence(usize::MAX) } else { Selection::NoImpl };
        }
        // An open input for a scalar Self has several scalar `From`
        // impls in core, not just the reflexive record: a pick of
        // `From<T> for T` (or no pick) then defers until inference
        // names the input (`T: Into<i64>` must not make `T` an i64).
        let mut defer_reflexive_from = false;
        // Numeric `From` obligations are widening casts, with no
        // impl behind them in this subset's lang records.
        if tr.def == lang.from
            && let Some(input) = self.tys.args(tr.args).get(1).and_then(|g| g.as_ty())
        {
            let input = self.deep(input);
            if Self::numeric_from_ok(self.kind(input), self.kind(self_ty)) {
                return Selection::ParamEvidence(usize::MAX);
            }
            let (ik, sk) = (self.kind(input), self.kind(self_ty));
            if let Some(sel) = self.lit_from_select(input, ik, self_ty, sk) {
                return sel;
            }
            defer_reflexive_from =
                matches!(ik, TyKind::Infer(_)) && matches!(sk, TyKind::Int(_) | TyKind::Float(_) | TyKind::Char | TyKind::Infer(_));
            if matches!(self.kind(input), TyKind::Int(_) | TyKind::Float(_) | TyKind::Char | TyKind::Bool)
                && matches!(self.kind(self_ty), TyKind::Int(_) | TyKind::Float(_) | TyKind::Char | TyKind::Bool)
            {
                return Selection::NoImpl;
            }
        }
        if lang.is_auto(tr.def) {
            match self.auto_holds(tr.def, self_ty) {
                Some(true) => return Selection::ParamEvidence(usize::MAX),
                Some(false) => return Selection::NoImpl,
                None => {}
            }
        }
        // The object candidate (ARCH 2.8): `dyn P` implements `P` and
        // every supertrait of `P`, with no impl behind it; calls go
        // through the vtable.
        if let Some(pr) = object::principal_of(&self.tys, self_ty) {
            let want = object::with_self(&mut self.tys, tr, DYN_SELF);
            let want = TraitRef { bindings: EMPTY_BINDINGS, ..want };
            let holds = if pr.def == want.def {
                self.unify_args(pr.args, want.args)
            } else {
                object::upcast_path(p, &mut self.tys, pr, want).is_some()
            };
            if holds {
                return Selection::ParamEvidence(usize::MAX);
            }
        }
        // An `impl Trait` Self proves its bounds (check/opaque.rs).
        for g in self.tys.args(tr.args).to_vec() {
            if let GenericArg::Ty(t) = g {
                let t = self.deep(t);
                self.note_opaques(t);
            }
        }
        let env = self.solve_env();
        let mut solver = std::mem::take(&mut self.solver);
        let snap = self.snapshot_vars();
        let sel = solver.select(self, &p.gx.index, &env, tr);
        self.solver = solver;
        let lang_pick =
            matches!(&sel, Selection::Impl { id, .. } if p.gx.index.get(*id).synthetic == crate::traits::index::Synthetic::Lang);
        if defer_reflexive_from && (lang_pick || sel == Selection::NoImpl) {
            self.rollback_vars(snap);
            return Selection::Ambiguous;
        }
        if sel == Selection::NoImpl && self.derive_query_holds(tr.def, self_ty) {
            return Selection::ParamEvidence(usize::MAX);
        }
        // An impl for a `'static` dyn type (`impl X for dyn Tr`).
        if let Selection::Impl { id, .. } = &sel
            && p.gx.static_dyn_impls.contains(&p.gx.index.get(*id).def)
        {
            self.obl.push(obligations::Obligation::DynStatic { span });
        }
        if let Selection::Impl { nested, .. } = &sel {
            if depth >= 64 {
                return Selection::Overflow;
            }
            for pred in nested.clone() {
                match pred {
                    Predicate::Trait(b) if b.count == 0 => self.obl.push_trait_at(b.value, span, depth + 1),
                    Predicate::AssocEq(b) if b.count == 0 => self.obl.push(obligations::Obligation::AssocEq { eq: b.value, span }),
                    Predicate::TypeOutlives(ty, Region::Static) => self.obl.push(obligations::Obligation::TypeStatic { ty, span }),
                    _ => {}
                }
            }
        }
        sel
    }

    /// The derive-family structural queries, for types the impl
    /// index has no record for (tuples, arrays, slices, refs).
    /// User and builtin Adts answer through the solver instead.
    fn derive_query_holds(&mut self, trait_def: DefId, self_ty: Ty) -> bool {
        let p = self.p;
        let lang = &p.gx.lang;
        match self.tys.kind(self_ty) {
            TyKind::Tuple(_) | TyKind::Array(..) | TyKind::Slice(_) | TyKind::Ref(..) | TyKind::RawPtr(..) => {}
            TyKind::Closure(..) if trait_def == lang.copy || trait_def == lang.clone => {}
            _ => return false,
        }
        if trait_def == lang.copy {
            is_copy(p, &self.tys, self_ty)
        } else if trait_def == lang.clone {
            self.record_glue_reads(trait_def, self_ty);
            has_clone(p, &self.tys, self_ty)
        } else if trait_def == lang.debug {
            has_debug(p, &self.tys, self_ty)
        } else if trait_def == lang.partial_eq || trait_def == lang.eq {
            self.record_glue_reads(trait_def, self_ty);
            has_eq(p, &self.tys, self_ty)
        } else if trait_def == lang.partial_ord {
            has_ord(p, &self.tys, self_ty)
        } else if trait_def == lang.ord {
            has_total_ord(p, &self.tys, self_ty)
        } else if trait_def == lang.hash {
            has_hash(p, &self.tys, self_ty)
        } else if trait_def == lang.default {
            self.record_glue_reads(trait_def, self_ty);
            has_default(p, &self.tys, self_ty)
        } else {
            false
        }
    }

    /// `Sized` by structure (section 2.7 basics): a parameter is
    /// sized when the env says so; an Adt when its fields are,
    /// with an unsized last field making the Adt unsized.
    fn sized_ok(&mut self, t: Ty) -> bool {
        let t = self.normalize_here(t);
        match self.tys.kind(t) {
            TyKind::Str | TyKind::Slice(_) | TyKind::Dyn(..) => false,
            TyKind::Param(p) => self.env().iter().any(|pred| {
                matches!(pred, Predicate::Trait(b) if b.value.def == self.p.gx.lang.sized
                    && self.tys.args(b.value.args)[0].as_ty().is_some_and(|s| matches!(self.tys.kind(s), TyKind::Param(q) if q == p)))
            }),
            TyKind::Projection(..) => true,
            TyKind::Infer(_) => true,
            // A tuple is as sized as its last element; the others
            // must be sized for the tuple to be well-formed at all.
            TyKind::Tuple(ts) => match self.tys.tys_of(ts).last() {
                Some(&e) => self.sized_ok(e),
                None => true,
            },
            TyKind::Array(..) => true,
            _ => {
                if let Some(a) = self.tys.local_adt(t) {
                    // Only a last field can be unsized. Without a
                    // materialized instance, `local_adt` answers with the
                    // template, whose fields are over its own params:
                    // substitute this application's args first.
                    let p = self.p;
                    let args: Vec<GenericArg> = self.tys.adt_parts(t).map(|(_, a)| self.tys.args(a).to_vec()).unwrap_or_default();
                    let lasts: Vec<Ty> = p.adt(a).variants.iter().filter_map(|v| v.fields.last().map(|f| f.ty)).collect();
                    lasts.into_iter().all(|f| {
                        let f = if args.is_empty() { f } else { subst(&mut self.tys, f, &args) };
                        let f = self.normalize_here(f);
                        self.sized_ok(f)
                    })
                } else {
                    crate::check::collect::is_sized_ty(&self.tys, t)
                }
            }
        }
    }

    /// An auto trait by structure (section 2.7). None when the
    /// answer needs the param env or inference to move first.
    fn auto_holds(&mut self, trait_def: DefId, t: Ty) -> Option<bool> {
        let mut seen: Vec<(DefId, Ty)> = Vec::new();
        self.auto_inner(trait_def, t, &mut seen)
    }

    fn auto_inner(&mut self, trait_def: DefId, t: Ty, seen: &mut Vec<(DefId, Ty)>) -> Option<bool> {
        let t = self.deep(t);
        // The answer reads the fields of every Adt in `t` (their
        // layouts' fingerprints cover nested field types).
        self.p.record_layout_reads(&mut self.out.reads, &self.tys, t);
        self.note_opaques(t);
        let env = self.solve_env();
        crate::check::collect::auto_structural(self.p, &mut self.tys, &env, trait_def, t, seen)
    }

    /// W-BORROW: for each `Fn`-family bound whose self type is a param the
    /// call instantiates with an inference var (a closure argument's
    /// expected type), records how the closure's arguments get their
    /// regions (`ClosureInfo::free_args`): an input that is a type param
    /// or projection is free (the caller's type); `&` over one has a
    /// higher-ranked outer reference (the bound writes it), unless the
    /// callee's regioned bound (`fn_bounds`, `RegionSig::fn_bounds`)
    /// names that lifetime (`&'static Message`, `&'a T`: free, and
    /// borrowck ties it); any other input with regions makes every
    /// argument higher-ranked (no entry).
    fn note_closure_bounds(&mut self, preds: &[Predicate], subst_args: &[GenericArg], fn_bounds: &[crate::borrowck::FnBound]) {
        let p = self.p;
        for pred in preds {
            let Predicate::Trait(b) = pred else { continue };
            if b.count != 0 || !p.gx.lang.is_fn_family(b.value.def) {
                continue;
            }
            let args: Vec<GenericArg> = p.tys.args(b.value.args).to_vec();
            let (Some(self_t), Some(inputs)) = (args.first().and_then(|g| g.as_ty()), args.get(1).and_then(|g| g.as_ty())) else { continue };
            let TyKind::Param(j) = p.tys.kind(self_t) else { continue };
            let Some(target) = subst_args.get(j.0 as usize).and_then(|g| g.as_ty()) else { continue };
            let target = self.resolve(target);
            let TyKind::Infer(v) = self.kind(target) else { continue };
            let TyKind::Tuple(ts) = p.tys.kind(inputs) else { continue };
            let opaque = |t: Ty| matches!(p.tys.kind(t), TyKind::Param(_) | TyKind::Projection(..)) || !bound_type_has_regions(p, t);
            let n_in = p.tys.tys_of(ts).len();
            let bound = fn_bounds.iter().find(|b| b.param == j.0 && b.inputs.len() == n_in);
            let regioned = bound.map(|b| b.inputs.as_slice());
            if let Some(b) = bound
                && let Some(out) = b.output
            {
                let (mut ins, mut outs) = (Vec::new(), Vec::new());
                for &t in &b.inputs {
                    crate::borrowck::regions_of(&p.tys, t, &mut ins);
                }
                crate::borrowck::regions_of(&p.tys, out, &mut outs);
                if matches!(ins[..], [Region::Bound(_)]) && outs.iter().any(|r| matches!(r, Region::Bound(_))) {
                    self.closure_bound_outputs.insert(v.0, out);
                }
            }
            let named_ref = |i: usize| {
                regioned.and_then(|ins| ins.get(i)).is_some_and(|&rt| matches!(p.tys.kind(rt), TyKind::Ref(Region::Static | Region::Param(_), _, _)))
            };
            let mut flags = Vec::new();
            let mut ok = true;
            for (i, &t) in p.tys.tys_of(ts).iter().enumerate() {
                match p.tys.kind(t) {
                    TyKind::Ref(_, _, inner) if opaque(inner) && named_ref(i) => flags.push(false),
                    TyKind::Ref(_, _, inner) if opaque(inner) => flags.push(true),
                    _ if opaque(t) => flags.push(false),
                    _ => ok = false,
                }
            }
            if ok {
                self.iter_closure_args.insert(v.0, flags);
            }
        }
    }

    /// Pushes the predicates of one instantiated item bound set:
    /// trait predicates as obligations, equalities as `AssocEq`
    /// obligations.
    fn push_predicates(&mut self, preds: &[Predicate], subst_args: &[GenericArg], span: Span) {
        self.push_predicates_with(preds, subst_args, span, &[]);
    }

    /// `push_predicates` for a fn template whose region signature keeps
    /// its `Fn` bounds with regions (`note_closure_bounds`).
    fn push_predicates_with(&mut self, preds: &[Predicate], subst_args: &[GenericArg], span: Span, fn_bounds: &[crate::borrowck::FnBound]) {
        self.note_closure_bounds(preds, subst_args, fn_bounds);
        let mut out: Vec<obligations::Obligation> = Vec::new();
        for &pred in preds {
            let pred = crate::traits::index::subst_predicate(&mut self.tys, pred, subst_args);
            match pred {
                Predicate::Trait(b) if b.count == 0 => out.push(obligations::Obligation::Trait { trait_ref: b.value, span, depth: 0 }),
                Predicate::AssocEq(b) if b.count == 0 => out.push(obligations::Obligation::AssocEq { eq: b.value, span }),
                Predicate::TypeOutlives(ty, Region::Static) => out.push(obligations::Obligation::TypeStatic { ty, span }),
                _ => {}
            }
        }
        // Elaborate so supertraits and binding equalities are
        // proved too, then queue the lot.
        let p = self.p;
        let traits_only: Vec<Predicate> =
            preds.iter().map(|&pred| crate::traits::index::subst_predicate(&mut self.tys, pred, subst_args)).collect();
        let elaborated = generics::elaborate_env(&mut self.tys, &p.gx.index, &traits_only);
        let mut queued = out;
        for pred in elaborated {
            match pred {
                Predicate::Trait(b) if b.count == 0 => {
                    if !queued.iter().any(|o| matches!(o, obligations::Obligation::Trait { trait_ref, .. } if *trait_ref == b.value)) {
                        queued.push(obligations::Obligation::Trait { trait_ref: b.value, span, depth: 0 });
                    }
                }
                Predicate::AssocEq(b) if b.count == 0 => {
                    if !queued.iter().any(|o| matches!(o, obligations::Obligation::AssocEq { eq, .. } if *eq == b.value)) {
                        queued.push(obligations::Obligation::AssocEq { eq: b.value, span });
                    }
                }
                _ => {}
            }
        }
        for o in queued {
            self.obl.push(o);
        }
    }

    /// Runs the obligation queue (the 2.4 run points). With
    /// `hard`, anything left is an error; without, unresolved
    /// obligations stay queued for the next point.
    fn run_obligations(&mut self, hard: bool) {
        if self.obl.is_empty() {
            return;
        }
        // A fixpoint over rounds: nested obligations and bindings
        // from one round can settle the next.
        for _round in 0..128 {
            let work = self.obl.take();
            if work.is_empty() {
                break;
            }
            let mut pending: Vec<obligations::Obligation> = Vec::new();
            let mut progress = false;
            for ob in work {
                // What a selection queues and binds, to tell a repeat (below).
                let (queued, trail, vars, consts) = (self.obl.len(), self.trail.len(), self.vars.len(), self.next_const_id);
                match ob {
                    obligations::Obligation::AssocEq { eq, span } => {
                        if self.prove_assoc_eq(eq, span) {
                            progress = true;
                        } else {
                            pending.push(ob);
                        }
                    }
                    obligations::Obligation::DynStatic { .. } | obligations::Obligation::TypeStatic { .. } => pending.push(ob),
                    obligations::Obligation::Trait { trait_ref, span, depth } => match self.select_obligation_at(trait_ref, span, depth) {
                        Selection::Impl { id, args, unbound, .. } => {
                            if !unbound.is_empty() && self.still_unbound(&unbound, trait_ref) {
                                // A re-queued obligation that selects the same impl with the
                                // same args again binds only the probe's fresh variables and
                                // queues copies of the nested predicates its last selection
                                // queued: no progress. Counting it ran every run point to the
                                // round cap and grew the queue each round.
                                let bound_old = self.trail.get(trail..).unwrap_or(&[]).iter().any(|&v| {
                                    if v >= generics::INFER_MARKER_BASE { v < consts } else { (v as usize) < vars }
                                });
                                if self.obl.note_requeued(trait_ref, span, depth, id, &args) || bound_old {
                                    progress = true;
                                } else {
                                    self.obl.truncate(queued);
                                }
                                pending.push(ob);
                            } else {
                                progress = true;
                            }
                        }
                        Selection::ParamEvidence(_) | Selection::Builtin => {
                            progress = true;
                            self.prove_bindings(trait_ref, span);
                        }
                        Selection::Ambiguous => pending.push(ob),
                        Selection::NoImpl => {
                            progress = true;
                            let tn = self.tn(self.tys.args(trait_ref.args)[0].as_ty().unwrap_or(ERROR));
                            let tr_name = self.trait_name(trait_ref.def);
                            self.err("L0612", span, format!("no impl of `{tr_name}` for `{tn}`"), "Add the impl, or change the bound.");
                        }
                        Selection::Overflow => {
                            progress = true;
                            self.err(
                                "L0611",
                                span,
                                "trait selection overflowed: the obligations recurse too deeply",
                                "Simplify the impls or bounds involved.",
                            );
                        }
                    },
                }
            }
            for ob in pending {
                self.obl.push(ob);
            }
            if !progress {
                break;
            }
        }
        if hard && !self.obl.is_empty() {
            let mut dyn_static: Vec<Span> = Vec::new();
            let mut type_static: Vec<(Ty, Span)> = Vec::new();
            for ob in self.obl.take() {
                match ob {
                    obligations::Obligation::DynStatic { span } => dyn_static.push(span),
                    obligations::Obligation::TypeStatic { ty, span } => type_static.push((ty, span)),
                    obligations::Obligation::Trait { trait_ref, span, .. } => {
                        // One last try now that literal fallbacks and
                        // late bindings have run: an impl with a
                        // still-unbound parameter is the step-4
                        // error, everything else is annotation.
                        match self.select_obligation(trait_ref) {
                            Selection::Impl { unbound, .. } if !unbound.is_empty() => {
                                self.err(
                                    "L0613",
                                    span,
                                    "an impl parameter is not known from the trait inputs",
                                    "Rewrite the impl so every parameter follows from the trait reference or an associated equality.",
                                );
                            }
                            Selection::Impl { .. } | Selection::ParamEvidence(_) | Selection::Builtin => {}
                            Selection::NoImpl => {
                                let tn = self.tn(self.tys.args(trait_ref.args)[0].as_ty().unwrap_or(ERROR));
                                let tr_name = self.trait_name(trait_ref.def);
                                self.err("L0612", span, format!("no impl of `{tr_name}` for `{tn}`"), "Add the impl, or change the bound.");
                            }
                            _ => {
                                self.err(
                                    "L0610",
                                    span,
                                    "type annotations needed: this trait obligation could not be resolved",
                                    "Annotate the types involved so one impl is picked.",
                                );
                            }
                        }
                    }
                    obligations::Obligation::AssocEq { span, .. } => {
                        self.err(
                            "L0610",
                            span,
                            "type annotations needed: an associated type could not be resolved",
                            "Annotate the types involved, or name the associated type in the bound.",
                        );
                    }
                }
            }
            self.check_dyn_static(dyn_static);
            self.check_type_static(type_static);
        }
    }

    /// Reports the `'static` bounds that do not hold (see
    /// `static_bound_err`). Concrete instances skip them, as they skip
    /// `check_dyn_static`: the template check proved each bound over
    /// its params, and the caller proved the params' bounds.
    fn check_type_static(&mut self, items: Vec<(Ty, Span)>) {
        if items.is_empty() || matches!(self.p.gx.fn_class.get(self.fid.0 as usize), Some(generics::FnClass::Instance)) {
            return;
        }
        let mut seen: Vec<Span> = Vec::new();
        for (ty, span) in items {
            let ty = self.deep(ty);
            if seen.contains(&span) {
                continue;
            }
            if let Some((code, msg)) = self.static_bound_err(ty, 0) {
                seen.push(span);
                self.err(code, span, msg, "Use a type that lives for `'static` here, or add a `'static` bound to the type parameter.");
            }
        }
    }

    /// Why `t` may fail a `'static` bound, as far as lust can tell. A
    /// type parameter needs a `'static` bound in the env (L0612, rustc
    /// E0310); a dyn type needs a `'static` object lifetime, and a
    /// reference to one a written `&'static` (L0705). Other references
    /// pass: lust erases their lifetimes, a known gap shared with every
    /// non-dyn reference. A type that nests past the walk limit is
    /// L0705: nothing is proved there.
    fn static_bound_err(&mut self, t: Ty, depth: u32) -> Option<(&'static str, String)> {
        let p = self.p;
        if depth > object::LIFETIME_WALK_LIMIT {
            return Some(("L0705", "this type nests too deeply for lust to prove that it lives for `'static`".to_string()));
        }
        let in_args = |cx: &mut Self, a: ArgsId| {
            let args: Vec<GenericArg> = cx.tys.args(a).to_vec();
            args.into_iter().filter_map(|g| g.as_ty()).find_map(|e| cx.static_bound_err(e, depth + 1))
        };
        match self.tys.kind(t) {
            TyKind::Param(_) | TyKind::Projection(..) => {
                if self.env().iter().any(|pred| matches!(pred, Predicate::TypeOutlives(x, Region::Static) if *x == t)) {
                    return None;
                }
                let name = match self.tys.kind(t) {
                    TyKind::Param(ParamId(i)) => p
                        .gx
                        .fn_templates
                        .get(self.fid.0 as usize)
                        .and_then(|t| t.as_ref())
                        .and_then(|t| t.generics.params.get(i as usize))
                        .map(|d| p.name(d.name).to_string()),
                    _ => None,
                };
                let name = name.unwrap_or_else(|| self.tn(t));
                Some(("L0612", format!("the type `{name}` may not live long enough: this needs it to be `'static`")))
            }
            TyKind::Dyn(..) => {
                if !object::dyn_is_static(p, &self.tys, t) {
                    return Some(("L0705", format!("lust cannot prove that `{}` lives for `'static`, which this bound requires", self.tn(t))));
                }
                let pr = object::principal_of(&self.tys, t)?;
                in_args(self, pr.args)
            }
            TyKind::Ref(r, _, e) => {
                if r != Region::Static && object::mentions_dyn(&self.tys, e) {
                    return Some(("L0705", format!("lust cannot prove that `{}` lives for `'static`, which this bound requires", self.tn(t))));
                }
                self.static_bound_err(e, depth + 1)
            }
            TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => self.static_bound_err(e, depth + 1),
            TyKind::Tuple(ts) => {
                let ts: Vec<Ty> = self.tys.tys_of(ts).to_vec();
                ts.into_iter().find_map(|e| self.static_bound_err(e, depth + 1))
            }
            // A closure's args are its captures' field types.
            TyKind::Adt(_, a) | TyKind::Closure(_, a) | TyKind::FnDef(_, a) | TyKind::Opaque(_, a) => in_args(self, a),
            _ => None,
        }
    }

    /// Binds the integer and float variables still free in a pending
    /// obligation to i32 and f64 (see `finish`).
    fn literal_fallback_in_obligations(&mut self) {
        let pending = self.obl.take();
        for ob in &pending {
            let mut tys: Vec<Ty> = Vec::new();
            let args = match ob {
                obligations::Obligation::Trait { trait_ref, .. } => trait_ref.args,
                obligations::Obligation::AssocEq { eq, .. } => {
                    tys.push(eq.ty);
                    eq.trait_args
                }
                obligations::Obligation::DynStatic { .. } => continue,
                obligations::Obligation::TypeStatic { ty, .. } => {
                    self.default_literal_vars(*ty);
                    continue;
                }
            };
            tys.extend(self.tys.args(args).iter().filter_map(|g| g.as_ty()));
            for t in tys {
                self.default_literal_vars(t);
            }
        }
        for ob in pending {
            self.obl.push(ob);
        }
    }

    /// `literal_fallback_in_obligations` for one type.
    fn default_literal_vars(&mut self, t: Ty) {
        let t = self.resolve(t);
        if !self.tys.flags(t).contains_infer() {
            return;
        }
        match self.tys.kind(t) {
            TyKind::Infer(v) if v.is_int() => self.bind_var(v.index(), I32),
            TyKind::Infer(v) if v.is_float() => {
                let f = self.tys.float_ty(FloatTy::F64);
                self.bind_var(v.index(), f);
            }
            TyKind::Ref(_, _, e) | TyKind::Slice(e) | TyKind::Array(e, _) | TyKind::RawPtr(_, e) => self.default_literal_vars(e),
            TyKind::Tuple(ts) => {
                for e in self.tys.tys_of(ts).to_vec() {
                    self.default_literal_vars(e);
                }
            }
            TyKind::Adt(_, a) | TyKind::Projection(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) => {
                for g in self.tys.args(a).to_vec() {
                    if let Some(e) = g.as_ty() {
                        self.default_literal_vars(e);
                    }
                }
            }
            _ => {}
        }
    }

    /// Reports the uses that need a `'static` dyn object lifetime when
    /// this body cannot give them one (see `dyn_static_clean`). Concrete
    /// instances skip it: their caller proved the bound that picked the
    /// impl, and their params are the caller's types.
    fn check_dyn_static(&mut self, mut spans: Vec<Span>) {
        if spans.is_empty() || matches!(self.p.gx.fn_class.get(self.fid.0 as usize), Some(generics::FnClass::Instance)) {
            return;
        }
        if self.dyn_static_clean() {
            return;
        }
        // A probe re-selection records no span; the call site does.
        if spans.iter().any(|&s| s != Span::default()) {
            spans.retain(|&s| s != Span::default());
        } else {
            spans = vec![self.f.def.name_span];
        }
        spans.dedup();
        for span in spans {
            self.err(
                "L0705",
                span,
                "this use needs a `dyn` value that lives for `'static`, and lust cannot prove that here",
                "Make the `dyn` value `'static` (`&'static dyn Tr` or `dyn Tr + 'static`), or write `impl dyn Tr + '_` for an impl that takes any lifetime.",
            );
        }
    }

    /// True when every dyn value in this body may have a `'static` object
    /// lifetime, which rustc's inference could then pick: no parameter
    /// (other than the `'static` `self` of an `impl dyn Tr` method) and
    /// no callee's declared return type holds a dyn type with an erased
    /// object lifetime, and no unsizing coercion starts from a value that
    /// may hold a borrow.
    fn dyn_static_clean(&mut self) -> bool {
        let p = self.p;
        if self.dyn_borrow_src {
            return false;
        }
        let skip_self = usize::from(self.f.def.self_param.is_some() && p.gx.static_dyn_fns.contains(&self.fid));
        if self.f.params.iter().skip(skip_self).any(|&t| object::has_erased_dyn(p, &p.tys, t)) {
            return false;
        }
        // A dyn value that flows into the return type invariantly gets
        // the caller's object lifetime (`Option<&mut dyn Tr>`).
        if object::has_erased_dyn_invariant(p, &p.tys, self.f.ret) {
            return false;
        }
        // A closure's parameter and return lifetimes are its caller's.
        for i in 0..self.closures.len() {
            let sig: Vec<Ty> = self.closures[i].inputs.iter().copied().chain([self.closures[i].output]).collect();
            for t in sig {
                let t = self.deep(t);
                if object::has_erased_dyn(p, &self.tys, t) {
                    return false;
                }
            }
        }
        for i in 0..self.out.expr_res.len() {
            let erased = match self.out.expr_res[i] {
                Res::Fn(f) | Res::Method { f, .. } | Res::TraitBin { f, .. } => object::has_erased_dyn(p, &p.tys, p.fn_info(f).ret),
                // A `dyn Fn` call returns its `Output`: the call's type.
                Res::DynMethod { owner, .. } if p.gx.lang.is_fn_family(owner) => {
                    let t = self.deep(self.out.expr_ty[i]);
                    object::has_erased_dyn(p, &self.tys, t)
                }
                Res::DynMethod { owner, slot, .. } => {
                    let info = p.gx.dyn_infos.get(&owner);
                    let m =
                        info.and_then(|info| (0..info.methods.len()).find(|&j| info.method_slot(j) == slot).map(|j| info.methods[j].def));
                    m.and_then(|d| p.gx.trait_methods.get(&d)).is_none_or(|tm| object::has_erased_dyn(p, &p.tys, tm.ret))
                }
                Res::Indirect => {
                    let e = ExprId(self.out.expr_base + i as u32);
                    let Expr::Call { callee, .. } = p.ast.expr(e) else { continue };
                    let ct = self.out.expr_ty[self.ei(*callee)];
                    let ct = self.deep(ct);
                    object::has_erased_dyn(p, &self.tys, ct)
                }
                _ => continue,
            };
            if erased {
                return false;
            }
        }
        true
    }

    /// True while any of `unbound` still names a free variable in
    /// the confirmed selection (checked through the obligation,
    /// whose args the probe bound).
    fn still_unbound(&mut self, unbound: &[ParamId], _tr: TraitRef) -> bool {
        !unbound.is_empty()
    }

    /// Proves one associated equality by normalization. False
    /// when the projection does not normalize yet. A template's
    /// rigid projection (params, no inference variable) is its own
    /// normal form: it unifies as it is.
    fn prove_assoc_eq(&mut self, eq: AssocEqData, span: Span) -> bool {
        let proj = self.tys.intern(TyKind::Projection(AssocId(eq.assoc), eq.trait_args));
        let normed = self.normalize_here(proj);
        let want = self.normalize_here(eq.ty);
        let flags = self.tys.flags(normed);
        let rigid = flags.contains_param() && !flags.contains_infer();
        if matches!(self.tys.kind(normed), TyKind::Projection(..)) && normed != want && !rigid {
            return false;
        }
        if !self.unify(normed, want) {
            let (a, b) = (self.tn(want), self.tn(normed));
            self.err(
                "L0110",
                span,
                format!("associated type mismatch: expected `{a}`, found `{b}`"),
                "Change the binding or the impl's associated type.",
            );
        }
        true
    }

    /// Proves the bindings written on an obligation that the
    /// param env answered (the impl path proves them in its
    /// probe already).
    fn prove_bindings(&mut self, tr: TraitRef, span: Span) {
        let bindings: Vec<(DefId, GenericArg)> = self.tys.bindings(tr.bindings).to_vec();
        for (assoc, ga) in bindings {
            if let GenericArg::Ty(want) = ga {
                let eq = AssocEqData { assoc, trait_args: tr.args, ty: want };
                if !self.prove_assoc_eq(eq, span) {
                    self.obl.push(obligations::Obligation::AssocEq { eq, span });
                }
            }
        }
    }

    /// The display name of a trait def, for obligation errors.
    fn trait_name(&self, def: DefId) -> String {
        self.p.gx.index.trait_record(def).map_or_else(|| "?".to_string(), |r| self.p.display_path(r.name))
    }

    /// Replaces `_` markers in one resolved written type with
    /// fresh body variables (distinct per marker).
    fn instantiate_infers(&mut self, t: Ty) -> Ty {
        self.instantiate_inner(t, &mut std::collections::HashMap::new())
    }

    fn instantiate_inner(&mut self, t: Ty, map: &mut std::collections::HashMap<u32, Ty>) -> Ty {
        match self.tys.kind(t) {
            TyKind::Infer(v) if v.index() >= generics::INFER_MARKER_BASE => {
                if let Some(&u) = map.get(&v.index()) {
                    return u;
                }
                let u = self.new_var(false);
                map.insert(v.index(), u);
                u
            }
            _ if !self.tys.flags(t).contains_infer() => t,
            TyKind::Ref(r, m, e) => {
                let e = self.instantiate_inner(e, map);
                self.tys.intern(TyKind::Ref(r, m, e))
            }
            TyKind::Slice(e) => {
                let e = self.instantiate_inner(e, map);
                self.tys.intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.instantiate_inner(e, map);
                self.tys.intern(TyKind::Array(e, n))
            }
            TyKind::Tuple(ts) => {
                let old: Vec<Ty> = self.tys.tys_of(ts).to_vec();
                let new: Vec<Ty> = old.iter().map(|&e| self.instantiate_inner(e, map)).collect();
                let ts = self.tys.intern_tys(&new);
                self.tys.intern(TyKind::Tuple(ts))
            }
            TyKind::Adt(d, a) => {
                let a = self.instantiate_args(a, map);
                self.tys.intern(TyKind::Adt(d, a))
            }
            TyKind::Projection(d, a) => {
                let a = self.instantiate_args(a, map);
                self.tys.intern(TyKind::Projection(d, a))
            }
            TyKind::FnDef(d, a) => {
                let a = self.instantiate_args(a, map);
                self.tys.intern(TyKind::FnDef(d, a))
            }
            _ => t,
        }
    }

    fn instantiate_args(&mut self, a: ArgsId, map: &mut std::collections::HashMap<u32, Ty>) -> ArgsId {
        let old: Vec<GenericArg> = self.tys.args(a).to_vec();
        let new: Vec<GenericArg> = old
            .iter()
            .map(|&g| match g {
                GenericArg::Ty(e) => GenericArg::Ty(self.instantiate_inner(e, map)),
                other => other,
            })
            .collect();
        self.tys.intern_args(&new)
    }

    // ---------- Inference ----------

    fn new_var(&mut self, int: bool) -> Ty {
        self.vars.push(Var { bound: None });
        let id = self.vars.len() as u32 - 1;
        self.tys.intern(TyKind::Infer(InferId(id, if int { InferKind::Int } else { InferKind::General })))
    }
    /// A fresh float-literal variable: binds only to a float type,
    /// defaults to f64 at body end.
    fn new_float_var(&mut self) -> Ty {
        self.vars.push(Var { bound: None });
        let id = self.vars.len() as u32 - 1;
        self.tys.intern(TyKind::Infer(InferId(id, InferKind::Float)))
    }
    /// Follows variable bindings at the top level only.
    fn resolve(&self, mut t: Ty) -> Ty {
        while let TyKind::Infer(v) = self.tys.kind(t) {
            match self.vars[v.index() as usize].bound {
                Some(b) => t = b,
                None => return t,
            }
        }
        t
    }
    fn kind(&self, t: Ty) -> TyKind {
        self.tys.kind(self.resolve(t))
    }
    /// Fully resolves a type, interning new structural types as needed. Unbound integer
    /// variables become i32.
    fn zonk(&mut self, t: Ty) -> Ty {
        self.rebuild(t, true)
    }
    /// Resolves variables at every depth, keeping unbound ones. Trait queries need this.
    fn deep(&mut self, t: Ty) -> Ty {
        self.rebuild(t, false)
    }
    /// The shared walk of `zonk` and `deep` over the structural kinds a body can form.
    /// A type with no inference variable anywhere (the cached flag) is returned as is,
    /// so the common signature types cost one flag read. With `zonk`, an unbound
    /// variable is defaulted (integer variables to i32, others to the error type).
    fn rebuild(&mut self, t: Ty, zonk: bool) -> Ty {
        let t = self.resolve(t);
        match self.tys.kind(t) {
            TyKind::Infer(v) => {
                if !zonk {
                    return t;
                }
                let d = if v.is_int() {
                    I32
                } else if v.is_float() {
                    self.tys.float_ty(FloatTy::F64)
                } else {
                    ERROR
                };
                self.bind_var(v.index(), d);
                d
            }
            TyKind::Array(e, n) if matches!(self.tys.const_kind(n), ConstKind::Infer(id) if id >= generics::INFER_MARKER_BASE) => {
                let e = self.rebuild(e, zonk);
                let n = self.resolve_const(n);
                self.tys.intern(TyKind::Array(e, n))
            }
            _ if !self.tys.flags(t).contains_infer() => t,
            TyKind::Ref(r, m, e) => {
                let e = self.rebuild(e, zonk);
                self.tys.intern(TyKind::Ref(r, m, e))
            }
            TyKind::Slice(e) => {
                let e = self.rebuild(e, zonk);
                self.tys.intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.rebuild(e, zonk);
                let n = self.resolve_const(n);
                self.tys.intern(TyKind::Array(e, n))
            }
            TyKind::Tuple(ts) => {
                let old: Vec<Ty> = self.tys.tys_of(ts).to_vec();
                let new: Vec<Ty> = old.iter().map(|&e| self.rebuild(e, zonk)).collect();
                let ts = self.tys.intern_tys(&new);
                self.tys.intern(TyKind::Tuple(ts))
            }
            TyKind::Adt(d, a) => {
                // Rebuild each type arg in place: the new list is allocated only
                // when some arg actually changes (the common deep() case does not).
                let n = self.tys.args(a).len();
                let mut new: Option<Vec<GenericArg>> = None;
                for i in 0..n {
                    let g = self.tys.args(a)[i];
                    let g2 = match g {
                        GenericArg::Ty(e) => GenericArg::Ty(self.rebuild(e, zonk)),
                        GenericArg::Const(c) => GenericArg::Const(self.resolve_const(c)),
                        other => other,
                    };
                    if g2 != g {
                        let v = new.get_or_insert_with(|| self.tys.args(a).to_vec());
                        v[i] = g2;
                    } else if let Some(v) = &mut new {
                        v[i] = g2;
                    }
                }
                match new {
                    None => t,
                    Some(v) => {
                        let a = self.tys.intern_args(&v);
                        self.tys.intern(TyKind::Adt(d, a))
                    }
                }
            }
            TyKind::RawPtr(m, e) => {
                let e = self.rebuild(e, zonk);
                self.tys.intern(TyKind::RawPtr(m, e))
            }
            TyKind::Projection(d, a) => {
                let a = self.rebuild_args(a, zonk);
                self.tys.intern(TyKind::Projection(d, a))
            }
            TyKind::FnDef(d, a) => {
                let a = self.rebuild_args(a, zonk);
                self.tys.intern(TyKind::FnDef(d, a))
            }
            TyKind::Closure(d, a) => {
                let a = self.rebuild_args(a, zonk);
                self.tys.intern(TyKind::Closure(d, a))
            }
            TyKind::Opaque(d, a) => {
                let a = self.rebuild_args(a, zonk);
                self.tys.intern(TyKind::Opaque(d, a))
            }
            TyKind::Dyn(b, r) => {
                let mut bounds = self.tys.dyn_bounds(b).clone();
                if let Some(pr) = &mut bounds.principal {
                    pr.value.args = self.rebuild_args(pr.value.args, zonk);
                    let old: Vec<(DefId, GenericArg)> = self.tys.bindings(pr.value.bindings).to_vec();
                    if !old.is_empty() {
                        let new: Vec<(DefId, GenericArg)> = old
                            .into_iter()
                            .map(|(d, g)| match g {
                                GenericArg::Ty(t) => (d, GenericArg::Ty(self.rebuild(t, zonk))),
                                g => (d, g),
                            })
                            .collect();
                        pr.value.bindings = self.tys.intern_bindings(&new);
                    }
                }
                let b = self.tys.intern_dyn_bounds(bounds);
                self.tys.intern(TyKind::Dyn(b, r))
            }
            TyKind::FnPtr(sig) => {
                let b = self.tys.sig(sig);
                let old: Vec<Ty> = self.tys.tys_of(b.value.inputs).to_vec();
                let new: Vec<Ty> = old.iter().map(|&e| self.rebuild(e, zonk)).collect();
                let inputs = self.tys.intern_tys(&new);
                let output = self.rebuild(b.value.output, zonk);
                let sig = self.tys.intern_sig(Binder { count: b.count, value: FnSig { inputs, output, ..b.value } });
                self.tys.intern(TyKind::FnPtr(sig))
            }
            _ => t,
        }
    }

    fn rebuild_args(&mut self, a: ArgsId, zonk: bool) -> ArgsId {
        let old: Vec<GenericArg> = self.tys.args(a).to_vec();
        let new: Vec<GenericArg> = old
            .iter()
            .map(|&g| match g {
                GenericArg::Ty(e) => GenericArg::Ty(self.rebuild(e, zonk)),
                GenericArg::Const(c) => GenericArg::Const(self.resolve_const(c)),
                other => other,
            })
            .collect();
        self.tys.intern_args(&new)
    }

    fn unify(&mut self, a: Ty, b: Ty) -> bool {
        let (a, b) = (self.resolve(a), self.resolve(b));
        if a == b {
            return true;
        }
        // Inside its defining body an `impl Trait` is its hidden type (a
        // recursive call returns it too), as in rustc.
        if !self.own_opaques.is_empty() {
            let (ma, mb) = (self.map_own_opaque(a), self.map_own_opaque(b));
            if ma != a || mb != b {
                return self.unify(ma, mb);
            }
        }
        // A projection that normalizes now unifies through its
        // normal form (section 2.5). Only when its args hold no
        // inference variable: selection inside probes already
        // handles the open case, and normalizing there would loop.
        if !self.in_norm {
            let na = if matches!(self.tys.kind(a), TyKind::Projection(..)) && !self.tys.flags(a).contains_infer() {
                self.in_norm = true;
                let n = self.normalize_here(a);
                self.in_norm = false;
                n
            } else {
                a
            };
            let nb = if matches!(self.tys.kind(b), TyKind::Projection(..)) && !self.tys.flags(b).contains_infer() {
                self.in_norm = true;
                let n = self.normalize_here(b);
                self.in_norm = false;
                n
            } else {
                b
            };
            if na != a || nb != b {
                return self.unify(na, nb);
            }
        }
        match (self.tys.kind(a), self.tys.kind(b)) {
            (TyKind::Error, _) | (_, TyKind::Error) => true,
            (TyKind::Infer(v), TyKind::Infer(w)) => {
                // Bind the general variable to the constrained one, so
                // the int or float constraint survives. An int variable
                // never unifies with a float variable.
                if (v.is_int() && w.is_float()) || (v.is_float() && w.is_int()) {
                    return false;
                }
                if (v.is_int() || v.is_float()) && !w.is_int() && !w.is_float() {
                    self.bind_var(w.index(), a);
                } else {
                    self.bind_var(v.index(), b);
                }
                true
            }
            (TyKind::Infer(v), k) | (k, TyKind::Infer(v)) => {
                if v.is_int() && !matches!(k, TyKind::Int(_)) {
                    return false;
                }
                if v.is_float() && !matches!(k, TyKind::Float(_)) {
                    return false;
                }
                let other = if matches!(self.tys.kind(a), TyKind::Infer(_)) { b } else { a };
                if self.occurs(v.index(), other) {
                    return false;
                }
                self.bind_var(v.index(), other);
                true
            }
            // Regions do not take part in this equality: every region is `Erased`
            // until milestone 6 gives them their own solver (ARCH 5).
            (TyKind::Ref(_, m, x), TyKind::Ref(_, n, y)) => m == n && self.unify(x, y),
            (TyKind::Adt(d, x), TyKind::Adt(e, y)) => d == e && self.unify_args(x, y),
            (TyKind::Tuple(x), TyKind::Tuple(y)) => {
                self.tys.tys_of(x).len() == self.tys.tys_of(y).len()
                    && (0..self.tys.tys_of(x).len()).all(|i| {
                        let (u, v) = (self.tys.tys_of(x)[i], self.tys.tys_of(y)[i]);
                        self.unify(u, v)
                    })
            }
            (TyKind::Slice(x), TyKind::Slice(y)) => self.unify(x, y),
            (TyKind::Array(x, n), TyKind::Array(y, m)) => self.unify_const(n, m) && self.unify(x, y),
            (TyKind::RawPtr(m, x), TyKind::RawPtr(n, y)) => m == n && self.unify(x, y),
            (TyKind::Projection(d, x), TyKind::Projection(e, y)) => d == e && self.unify_args(x, y),
            (TyKind::FnDef(d, x), TyKind::FnDef(e, y)) => d == e && self.unify_args(x, y),
            (TyKind::Closure(d, x), TyKind::Closure(e, y)) => d == e && self.unify_args(x, y),
            (TyKind::Opaque(d, x), TyKind::Opaque(e, y)) => d == e && self.unify_args(x, y),
            // Fn pointers unify part by part. Their binders hold only
            // elided (late-bound) regions, which are erased here.
            (TyKind::FnPtr(x), TyKind::FnPtr(y)) => {
                let (sx, sy) = (self.tys.sig(x).value, self.tys.sig(y).value);
                let n = self.tys.tys_of(sx.inputs).len();
                if sx.is_unsafe != sy.is_unsafe || sx.extern_c != sy.extern_c || n != self.tys.tys_of(sy.inputs).len() {
                    return false;
                }
                for i in 0..n {
                    let (u, v) = (self.tys.tys_of(sx.inputs)[i], self.tys.tys_of(sy.inputs)[i]);
                    if !self.unify(u, v) {
                        return false;
                    }
                }
                self.unify(sx.output, sy.output)
            }
            // Two dyn types are equal when the principals and the written
            // auto traits are; regions are erased here, as for references.
            (TyKind::Dyn(x, _), TyKind::Dyn(y, _)) => {
                let (bx, by) = (self.tys.dyn_bounds(x).clone(), self.tys.dyn_bounds(y).clone());
                match (bx.principal, by.principal) {
                    (Some(px), Some(py)) => {
                        bx.auto == by.auto
                            && px.value.def == py.value.def
                            && self.unify_args(px.value.args, py.value.args)
                            && self.unify_bindings(px.value.bindings, py.value.bindings)
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }
    /// Two binding lists (`Output = R` of a `dyn Fn`) unify when they
    /// bind the same items, in order, to types that unify.
    fn unify_bindings(&mut self, a: BindingsId, b: BindingsId) -> bool {
        if a == b {
            return true;
        }
        let (a, b) = (self.tys.bindings(a).to_vec(), self.tys.bindings(b).to_vec());
        a.len() == b.len()
            && a.iter().zip(&b).all(|(&(da, ga), &(db, gb))| {
                da == db
                    && match (ga, gb) {
                        (GenericArg::Ty(x), GenericArg::Ty(y)) => self.unify(x, y),
                        (x, y) => x == y,
                    }
            })
    }
    /// Two generic argument lists unify element by element, in declared order.
    /// Type args unify; lifetime and const args must already be equal. Indexed
    /// reads only, so the common one-element `Vec<T>` case allocates nothing.
    fn unify_args(&mut self, a: ArgsId, b: ArgsId) -> bool {
        let n = self.tys.args(a).len();
        if n != self.tys.args(b).len() {
            return false;
        }
        for i in 0..n {
            let ok = match (self.tys.args(a)[i], self.tys.args(b)[i]) {
                (GenericArg::Ty(x), GenericArg::Ty(y)) => self.unify(x, y),
                (GenericArg::Const(x), GenericArg::Const(y)) => self.unify_const(x, y),
                (x, y) => x == y,
            };
            if !ok {
                return false;
            }
        }
        true
    }
    fn occurs(&self, v: u32, t: Ty) -> bool {
        match self.kind(t) {
            TyKind::Infer(w) => w.index() == v,
            TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => self.occurs(v, e),
            TyKind::Adt(_, a) => (0..self.tys.args(a).len()).any(|i| match self.tys.args(a)[i].as_ty() {
                Some(e) => self.occurs(v, e),
                None => false,
            }),
            TyKind::Tuple(ts) => {
                let n = self.tys.tys_of(ts).len();
                (0..n).any(|i| {
                    let e = self.tys.tys_of(ts)[i];
                    self.occurs(v, e)
                })
            }
            TyKind::Dyn(b, _) => match self.tys.dyn_bounds(b).principal {
                Some(pr) => self.tys.args(pr.value.args).to_vec().into_iter().any(|g| g.as_ty().is_some_and(|e| self.occurs(v, e))),
                None => false,
            },
            TyKind::FnPtr(sig) => {
                let s = self.tys.sig(sig).value;
                self.tys.tys_of(s.inputs).to_vec().into_iter().chain([s.output]).any(|e| self.occurs(v, e))
            }
            TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => {
                self.tys.args(a).to_vec().into_iter().any(|g| g.as_ty().is_some_and(|e| self.occurs(v, e)))
            }
            _ => false,
        }
    }
    /// True when `field` is the unsized field of the newtype `outer`,
    /// directly or through nested newtypes (W-SHIM coercion in shipped
    /// std source).
    fn newtype_field_of(&self, outer: Ty, field: Ty) -> bool {
        let mut t = outer;
        while let TyKind::Adt(d, _) = self.kind(t) {
            let Some(f) = self.tys.unsized_field(d) else { return false };
            if f == field {
                return true;
            }
            t = f;
        }
        false
    }
    fn mismatch(&mut self, span: Span, expected: Ty, found: Ty) {
        let (e, f) = (self.tn(expected), self.tn(found));
        let fix = if e == "&str" && f == "String" {
            "Borrow it: write `&value` or `value.as_str()`.".to_string()
        } else if e == "String" && f == "&str" {
            "Convert it: write `value.to_string()`.".to_string()
        } else if f.starts_with('&') && e == f[1..] {
            "Dereference it with `*value`, or clone it if the type is not Copy.".to_string()
        } else if e.starts_with('&') && f == e[1..] {
            "Borrow it with `&value`.".to_string()
        } else {
            format!("Change the value to type `{e}`, or change the expected type.")
        };
        self.err("L0110", span, format!("mismatched types: expected `{e}`, found `{f}`"), fix);
    }
    /// Checks `found` against `expected` at a coercion site. Records the coercion on `e`.
    fn coerce_at(&mut self, found: Ty, expected: Ty, span: Span, e: Option<ExprId>) -> bool {
        // ARCH 2.4 run point: the obligation queue runs at coercion sites.
        self.run_obligations(false);
        let (fk, ek) = (self.kind(found), self.kind(expected));
        if fk == TyKind::Never {
            return true;
        }
        // Count reference layers, for deref coercions.
        let depth = |cx: &Self, mut t: Ty| {
            let mut n = 0u8;
            while let TyKind::Ref(_, _, inner) = cx.kind(t) {
                t = inner;
                n += 1;
            }
            (n, t)
        };
        let (fd, fbase) = depth(self, found);
        let (ed, _) = depth(self, expected);
        // The mutability a deref coercion through a smart pointer
        // may hand out: the reference directly on a `Box` bounds
        // it; an `Rc` never hands out `&mut`.
        let box_ref_mut = |cx: &Self| -> Option<bool> {
            let mut t = found;
            loop {
                match cx.kind(t) {
                    TyKind::Ref(_, m, inner) => {
                        let inner = cx.resolve(inner);
                        if cx.tys.boxed_elem(inner).is_some() {
                            return Some(m.is_mut());
                        }
                        if cx.tys.rc_elem(inner).is_some() {
                            return Some(false);
                        }
                        t = inner;
                    }
                    _ => return None,
                }
            }
        };
        // A reference to a dyn type is an unsizing target: rustc commits
        // to unsizing there and never tries a deref coercion (`&&S` to
        // `&dyn Tr` needs `&S: Tr`), so neither does this.
        let dyn_target = matches!(ek, TyKind::Ref(_, _, y) if matches!(self.kind(y), TyKind::Dyn(..)));
        let c = match (fk, ek) {
            (TyKind::Ref(..), TyKind::Ref(_, Mut::Shared, s))
                if self.kind(s) == TyKind::Str && self.tys.is_string_ty(self.resolve(fbase)) =>
            {
                Coerce::StrFromString
            }
            (TyKind::Ref(..), TyKind::Ref(_, Mut::Shared, s))
                if self.kind(s) == TyKind::Str
                    && self.tys.smart_elem(self.resolve(fbase)).is_some_and(|e| self.tys.is_string_ty(self.resolve(e))) =>
            {
                Coerce::StrFromString
            }
            // Not for a dyn target: rustc commits to unsizing there
            // (`&Box<S>` to `&dyn Tr` needs `Box<S>: Tr`, E0277).
            (TyKind::Ref(..), TyKind::Ref(_, em, y))
                if ed == 1
                    && !dyn_target
                    && box_ref_mut(self).is_some_and(|bm| !em.is_mut() || bm)
                    && {
                        // An exact match wins over a deref
                        // coercion (as in the `Deref` arm below):
                        // `&Rc<T>` against `&Rc<T>` must not
                        // become `&T` by binding through the box.
                        let snap_vars = self.snapshot_vars();
                        let obl_len = self.obl_len();
                        let exact = self.unify(found, expected);
                        self.rollback_vars(snap_vars);
                        self.obl_truncate(obl_len);
                        !exact
                    }
                    && self.tys.smart_elem(self.resolve(fbase)).is_some_and(|e| self.unify(e, y)) =>
            {
                Coerce::BoxToRef(fd + 1, em.is_mut())
            }
            (TyKind::Ref(..), TyKind::Ref(_, Mut::Shared, _))
                if !dyn_target && fd > ed && {
                    // An exact structural match wins over a deref
                    // coercion: `&&S` against `&T` binds `T = &S`,
                    // never `T = S` through `*`. rustc coerces only
                    // when the types do not already unify, so try
                    // the plain unify first (rolled back; the
                    // fallback arm redoes it for real).
                    let snap_vars = self.snapshot_vars();
                    let obl_len = self.obl_len();
                    let exact = self.unify(found, expected);
                    self.rollback_vars(snap_vars);
                    self.obl_truncate(obl_len);
                    !exact && {
                        let mut t = found;
                        for _ in 0..fd - ed {
                            if let TyKind::Ref(_, _, inner) = self.kind(t) {
                                t = inner;
                            }
                        }
                        matches!(self.kind(t), TyKind::Ref(_, Mut::Shared, _)) && self.unify(t, expected)
                    }
                } =>
            {
                let mut t = found;
                for _ in 0..fd - ed {
                    if let TyKind::Ref(_, _, inner) = self.kind(t) {
                        t = inner;
                    }
                }
                self.dyn_regions(t, expected, false, span);
                Coerce::Deref(fd - ed)
            }
            // A dyn target takes the unsizing arm below even when the
            // types already unify: it checks the object lifetimes.
            (TyKind::Ref(_, Mut::Mut, x), TyKind::Ref(_, Mut::Shared, y)) if !dyn_target && self.unify(x, y) => {
                self.dyn_regions(x, y, false, span);
                Coerce::MutToShared
            }
            (TyKind::Ref(_, Mut::Mut, x), TyKind::Ref(_, Mut::Mut, y)) if !dyn_target && self.unify(x, y) => {
                self.dyn_regions(x, y, true, span);
                Coerce::Reborrow
            }
            (TyKind::Ref(_, fm, x), TyKind::Ref(_, em, y))
                if matches!(self.kind(y), TyKind::Slice(_))
                    && (!em.is_mut() || fm.is_mut())
                    && match self.kind(x) {
                        TyKind::Array(xe, _) => match self.kind(y) {
                            TyKind::Slice(ye) => self.unify(xe, ye),
                            _ => false,
                        },
                        _ => false,
                    } =>
            {
                if let (TyKind::Array(xe, _), TyKind::Slice(ye)) = (self.kind(x), self.kind(y)) {
                    self.dyn_regions(xe, ye, em.is_mut(), span);
                }
                Coerce::SliceFromArray(em.is_mut())
            }
            (TyKind::Ref(_, fm, x), TyKind::Ref(_, em, y))
                if matches!(self.kind(y), TyKind::Slice(_))
                    && (!em.is_mut() || fm.is_mut())
                    && match self
                        .tys
                        .vec_elem(self.resolve(x))
                        .or_else(|| self.tys.smart_elem(self.resolve(x)).and_then(|b| self.tys.vec_elem(self.resolve(b))))
                    {
                        Some(xe) => match self.kind(y) {
                            TyKind::Slice(ye) => self.unify(xe, ye),
                            _ => false,
                        },
                        None => false,
                    } =>
            {
                if let (Some(xe), TyKind::Slice(ye)) = (self.tys.vec_elem(self.resolve(x)), self.kind(y)) {
                    self.dyn_regions(xe, ye, em.is_mut(), span);
                }
                Coerce::SliceFromVec(em.is_mut())
            }
            // Shipped std source only (W-SHIM): a reference to the field
            // of an unsized newtype is a reference to the newtype, as
            // std's pointer casts make it (`&OsStr` to `&Path`, `&[u8]`
            // to `&OsStr`). Both have one C form, so the value stays.
            (TyKind::Ref(_, fm, x), TyKind::Ref(_, em, y))
                if (!em.is_mut() || fm.is_mut())
                    && self.p.shipped_crate_at(span) == Some(crate::ty::lang::ShippedCrate::Std)
                    && self.newtype_field_of(self.resolve(y), self.resolve(x)) =>
            {
                if let Some(e) = e {
                    self.set(e, expected);
                }
                Coerce::None
            }
            // A plain fn item coerces to a function pointer with the
            // same signature (the value materializes as its trampoline).
            (TyKind::FnDef(..), TyKind::FnPtr(_)) if self.is_fn_item(found) && self.fn_item_ptr_unifies(found, expected) => {
                // The expression now has the pointer type, so lowering
                // materializes the trampoline value for it.
                if let Some(e) = e {
                    self.set(e, expected);
                }
                Coerce::None
            }
            (TyKind::Ref(_, fm, x), TyKind::Ref(_, em, y))
                if dyn_target && (!em.is_mut() || fm.is_mut()) && !matches!(self.kind(x), TyKind::Infer(v) if !v.is_int() && !v.is_float()) =>
            {
                match self.unsize_coercion(x, y, found, expected, span, e) {
                    Some(c) => c,
                    None => return false,
                }
            }
            // `Box<T>` to `Box<dyn Tr>` and `Rc<T>` to `Rc<dyn Tr>`: an
            // owning unsizing, under the rules of the reference form.
            (TyKind::Adt(..), TyKind::Adt(..)) if let Some((x, y)) = self.owning_unsize_parts(found, expected) => {
                match self.unsize_coercion(x, y, found, expected, span, e) {
                    Some(c) => c,
                    None => return false,
                }
            }
            _ => {
                if !self.unify(found, expected) {
                    // A deref coercion through user `Deref` impls (`&name`
                    // where `&str` is wanted).
                    if let (Some(ex), TyKind::Ref(_, fm, _), TyKind::Ref(_, em, y)) = (e, fk, ek)
                        && (!em.is_mut() || fm.is_mut())
                        && let Some(c) = self.user_deref_coercion(ex, found, y, em.is_mut(), span)
                    {
                        let i = self.ei(ex);
                        self.out.coerce[i] = c;
                        return true;
                    }
                    if self.coerce_deep(found, expected, e) {
                        // The whole value now has the expected type; the
                        // inner coercions recorded on its parts build it.
                        if let Some(e) = e {
                            self.set(e, expected);
                        }
                        return true;
                    }
                    self.mismatch(span, expected, found);
                    return false;
                }
                self.dyn_regions(found, expected, false, span);
                Coerce::None
            }
        };
        if let Some(e) = e {
            let i = self.ei(e);
            self.out.coerce[i] = c;
        }
        true
    }

    /// The object lifetime checks of a coercion whose types unified
    /// (`unify` ignores regions; see `check::object`). A `'static`
    /// object lifetime the found type lacks needs proof: a `DynStatic`
    /// obligation. Under `&mut`, `*mut`, a user Adt (lust computes no
    /// variance), a fn pointer, or trait args (`invariant`), the object
    /// lifetimes must match; and a written `&'static` reference to a
    /// dyn value cannot come from a shorter one. lust cannot prove
    /// either, so both are L0705.
    fn dyn_regions(&mut self, found: Ty, expected: Ty, invariant: bool, span: Span) {
        let (f, e) = (self.deep(found), self.deep(expected));
        // A dyn type's principal args do not reach the type flags, so the
        // signature check runs first.
        if let Some(why) = self.sig_static_mismatch(f, e, invariant, 0) {
            self.err("L0110", span, why, "Write `&'static` in both types, or elide it in both.");
            return;
        }
        if !self.tys.flags(f).contains_static_region() && !self.tys.flags(e).contains_static_region() {
            return;
        }
        let mut need_static = false;
        match self.region_walk(f, e, invariant, &mut need_static, 0) {
            Some(why) => self.err(
                "L0705",
                span,
                why,
                "Use the same object lifetime on both sides, or drop the `'static` bound from the `dyn` type.",
            ),
            None if need_static => self.obl.push(obligations::Obligation::DynStatic { span }),
            None => {}
        }
    }

    /// `dyn_regions` over two unified types, in parallel. Sets
    /// `need_static` for a `'static` object lifetime that needs proof;
    /// returns the reason when the regions cannot match, or when the
    /// types nest past the walk limit (nothing is proved there).
    fn region_walk(&mut self, f: Ty, e: Ty, invariant: bool, need_static: &mut bool, depth: u32) -> Option<String> {
        let p = self.p;
        if f == e {
            return None;
        }
        if depth > object::LIFETIME_WALK_LIMIT {
            return Some("these types nest too deeply for lust to check their object lifetimes".to_string());
        }
        match (self.tys.kind(f), self.tys.kind(e)) {
            (TyKind::Dyn(bf, _), TyKind::Dyn(be, _)) => {
                let (fs, es) = (object::dyn_is_static(p, &self.tys, f), object::dyn_is_static(p, &self.tys, e));
                if es && !fs {
                    *need_static = true;
                } else if fs && !es && invariant {
                    return Some(format!(
                        "`{}` and `{}` must have the same object lifetime here, and lust cannot prove that",
                        self.tn(f),
                        self.tn(e)
                    ));
                }
                match (self.tys.dyn_bounds(bf).principal, self.tys.dyn_bounds(be).principal) {
                    (Some(pf), Some(pe)) if pf.value.def == pe.value.def => self.args_walk(pf.value.args, pe.value.args, true, need_static, depth),
                    _ => None,
                }
            }
            (TyKind::Ref(rf, _, xf), TyKind::Ref(re, me, xe)) => {
                // Only `&'static dyn Tr` is checked here; a `&'static` in a
                // fn pointer type or `dyn Fn` sugar (`Scope::static_refs`)
                // is the borrow checker's.
                let to_dyn = matches!(self.tys.kind(xe), TyKind::Dyn(..));
                if to_dyn && re == Region::Static && rf != Region::Static {
                    return Some(format!("lust cannot prove that this reference lives for `'static`, which `{}` requires", self.tn(e)));
                }
                if to_dyn && rf == Region::Static && re != Region::Static && invariant {
                    return Some(format!("`{}` and `{}` must have the same lifetime here, and lust cannot prove that", self.tn(f), self.tn(e)));
                }
                self.region_walk(xf, xe, invariant || me.is_mut(), need_static, depth + 1)
            }
            (TyKind::RawPtr(_, xf), TyKind::RawPtr(me, xe)) => self.region_walk(xf, xe, invariant || me.is_mut(), need_static, depth + 1),
            (TyKind::Slice(xf), TyKind::Slice(xe)) | (TyKind::Array(xf, _), TyKind::Array(xe, _)) => {
                self.region_walk(xf, xe, invariant, need_static, depth + 1)
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                let (a, b) = (self.tys.tys_of(a).to_vec(), self.tys.tys_of(b).to_vec());
                a.into_iter().zip(b).find_map(|(x, y)| self.region_walk(x, y, invariant, need_static, depth + 1))
            }
            // `Option`, `Result`, and `Vec` are covariant.
            (TyKind::Adt(df, af), TyKind::Adt(de, ae)) if df == de => {
                let covariant = matches!(self.tys.builtin_of(f), Some(BuiltinTy::Option | BuiltinTy::Result | BuiltinTy::Vec));
                self.args_walk(af, ae, invariant || !covariant, need_static, depth)
            }
            (TyKind::FnPtr(sf), TyKind::FnPtr(se)) => {
                let (sf, se) = (self.tys.sig(sf).value, self.tys.sig(se).value);
                let (inf, ine) = (self.tys.tys_of(sf.inputs).to_vec(), self.tys.tys_of(se.inputs).to_vec());
                inf.into_iter()
                    .chain([sf.output])
                    .zip(ine.into_iter().chain([se.output]))
                    .find_map(|(x, y)| self.region_walk(x, y, true, need_static, depth + 1))
            }
            (TyKind::FnDef(df, af), TyKind::FnDef(de, ae))
            | (TyKind::Closure(df, af), TyKind::Closure(de, ae))
            | (TyKind::Opaque(df, af), TyKind::Opaque(de, ae))
                if df == de =>
            {
                self.args_walk(af, ae, true, need_static, depth)
            }
            _ => None,
        }
    }

    /// W-BORROW: a fn pointer type or `dyn Fn*` sugar may write `&'static`
    /// (`Scope::static_refs`); every other region there is late-bound.
    /// `found` fits `expected` only when it is at least as general: no
    /// `'static` input where `expected` takes any lifetime, and no
    /// late-bound output where `expected` returns `'static` (rustc E0308;
    /// under `invariant`, the two must agree). Walks two unified types in
    /// parallel to the signatures in them.
    fn sig_static_mismatch(&mut self, f: Ty, e: Ty, invariant: bool, depth: u32) -> Option<String> {
        if f == e || depth > object::LIFETIME_WALK_LIMIT {
            return None;
        }
        let sigs = |this: &mut Self, t: Ty| -> Option<(Vec<Ty>, Ty)> {
            match this.tys.kind(t) {
                TyKind::FnPtr(s) => {
                    let s = this.tys.sig(s).value;
                    Some((this.tys.tys_of(s.inputs).to_vec(), s.output))
                }
                TyKind::Dyn(..) => {
                    let (_, tuple, out) = this.dyn_fn_parts(t)?;
                    let ins = match this.tys.kind(tuple) {
                        TyKind::Tuple(ts) => this.tys.tys_of(ts).to_vec(),
                        _ => Vec::new(),
                    };
                    Some((ins, out))
                }
                _ => None,
            }
        };
        if let (Some((fi, fo)), Some((ei, eo))) = (sigs(self, f), sigs(self, e)) {
            for (x, y) in fi.into_iter().zip(ei) {
                if let Some(why) = self.sig_pos_mismatch(x, y, true, invariant, f, e) {
                    return Some(why);
                }
            }
            return self.sig_pos_mismatch(fo, eo, false, invariant, f, e);
        }
        match (self.tys.kind(f), self.tys.kind(e)) {
            (TyKind::Ref(_, _, x), TyKind::Ref(_, m, y)) | (TyKind::RawPtr(_, x), TyKind::RawPtr(m, y)) => {
                self.sig_static_mismatch(x, y, invariant || m.is_mut(), depth + 1)
            }
            (TyKind::Slice(x), TyKind::Slice(y)) | (TyKind::Array(x, _), TyKind::Array(y, _)) => self.sig_static_mismatch(x, y, invariant, depth + 1),
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                let (a, b) = (self.tys.tys_of(a).to_vec(), self.tys.tys_of(b).to_vec());
                a.into_iter().zip(b).find_map(|(x, y)| self.sig_static_mismatch(x, y, invariant, depth + 1))
            }
            (TyKind::Adt(df, af), TyKind::Adt(de, ae)) if df == de => {
                let covariant = matches!(self.tys.builtin_of(f), Some(BuiltinTy::Option | BuiltinTy::Result | BuiltinTy::Vec | BuiltinTy::Boxed | BuiltinTy::Rc));
                let (a, b) = (self.tys.args(af).to_vec(), self.tys.args(ae).to_vec());
                a.into_iter().zip(b).find_map(|(x, y)| match (x.as_ty(), y.as_ty()) {
                    (Some(x), Some(y)) => self.sig_static_mismatch(x, y, invariant || !covariant, depth + 1),
                    _ => None,
                })
            }
            _ => None,
        }
    }

    /// One input (`input`) or the output of two signatures in parallel
    /// (`sig_static_mismatch`): their `&'static` and late-bound
    /// references, place by place.
    fn sig_pos_mismatch(&mut self, x: Ty, y: Ty, input: bool, invariant: bool, f: Ty, e: Ty) -> Option<String> {
        match (self.tys.kind(x), self.tys.kind(y)) {
            (TyKind::Ref(rx, _, xi), TyKind::Ref(ry, _, yi)) => {
                let (sx, sy) = (rx == Region::Static, ry == Region::Static);
                let bad = if invariant { sx != sy } else if input { sx && !sy } else { sy && !sx };
                if bad {
                    return Some(format!("`{}` is not as general as `{}`: their `'static` references differ", self.tn(f), self.tn(e)));
                }
                self.sig_pos_mismatch(xi, yi, input, invariant, f, e)
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                let (a, b) = (self.tys.tys_of(a).to_vec(), self.tys.tys_of(b).to_vec());
                a.into_iter().zip(b).find_map(|(p, q)| self.sig_pos_mismatch(p, q, input, invariant, f, e))
            }
            (TyKind::Slice(p), TyKind::Slice(q)) | (TyKind::Array(p, _), TyKind::Array(q, _)) => self.sig_pos_mismatch(p, q, input, invariant, f, e),
            (TyKind::Adt(dx, ax), TyKind::Adt(dy, ay)) if dx == dy => {
                let (a, b) = (self.tys.args(ax).to_vec(), self.tys.args(ay).to_vec());
                a.into_iter().zip(b).find_map(|(p, q)| match (p.as_ty(), q.as_ty()) {
                    (Some(p), Some(q)) => self.sig_pos_mismatch(p, q, input, true, f, e),
                    _ => None,
                })
            }
            _ => None,
        }
    }

    fn args_walk(&mut self, a: ArgsId, b: ArgsId, invariant: bool, need_static: &mut bool, depth: u32) -> Option<String> {
        let (a, b) = (self.tys.args(a).to_vec(), self.tys.args(b).to_vec());
        a.into_iter().zip(b).find_map(|(x, y)| match (x.as_ty(), y.as_ty()) {
            (Some(x), Some(y)) => self.region_walk(x, y, invariant, need_static, depth + 1),
            _ => None,
        })
    }
    /// Structural equality with inference variables as wildcards.
    fn ty_matchish(&self, a: Ty, b: Ty) -> bool {
        let (a, b) = (self.resolve(a), self.resolve(b));
        if a == b {
            return true;
        }
        match (self.tys.kind(a), self.tys.kind(b)) {
            (TyKind::Infer(_), _) | (_, TyKind::Infer(_)) => true,
            (TyKind::Ref(_, _, x), TyKind::Ref(_, _, y)) => self.ty_matchish(x, y),
            (TyKind::Slice(x), TyKind::Slice(y)) | (TyKind::Array(x, _), TyKind::Array(y, _)) => self.ty_matchish(x, y),
            (TyKind::Tuple(xs), TyKind::Tuple(ys)) => {
                let (xs, ys) = (self.tys.tys_of(xs), self.tys.tys_of(ys));
                xs.len() == ys.len() && xs.iter().zip(ys).all(|(&x, &y)| self.ty_matchish(x, y))
            }
            (TyKind::Adt(d, x), TyKind::Adt(e, y)) => {
                d == e
                    && self.tys.args(x).len() == self.tys.args(y).len()
                    && self.tys.args(x).iter().zip(self.tys.args(y)).all(|(x, y)| match (x, y) {
                        (GenericArg::Ty(x), GenericArg::Ty(y)) => self.ty_matchish(*x, *y),
                        _ => x == y,
                    })
            }
            _ => false,
        }
    }

    /// True when a reference coercion (unsize to a slice, `&String` to
    /// `&str`, `&mut` to `&`) takes `f` to `e`. Pure: no unification.
    fn ref_coercible(&self, f: Ty, e: Ty) -> bool {
        let (TyKind::Ref(_, fm, x), TyKind::Ref(_, em, y)) = (self.kind(f), self.kind(e)) else { return false };
        if em.is_mut() && !fm.is_mut() {
            return false;
        }
        match self.kind(y) {
            TyKind::Slice(ye) => match self.kind(x) {
                TyKind::Array(xe, _) | TyKind::Slice(xe) => self.ty_matchish(xe, ye),
                _ => self
                    .tys
                    .vec_elem(self.resolve(x))
                    .or_else(|| self.tys.smart_elem(self.resolve(x)).and_then(|b| self.tys.vec_elem(self.resolve(b))))
                    .is_some_and(|xe| self.ty_matchish(xe, ye)),
            },
            TyKind::Str => {
                self.tys.is_string_ty(self.resolve(x))
                    || self.tys.smart_elem(self.resolve(x)).is_some_and(|e| self.tys.is_string_ty(self.resolve(e)))
            }
            _ => self.ty_matchish(x, y) || self.tys.smart_elem(self.resolve(x)).is_some_and(|e| self.ty_matchish(e, y)),
        }
    }

    /// True when the fn item to fn pointer coercion takes `f` to `e`.
    /// Pure: no unification (the same test `coerce_at` applies).
    fn fn_coercible(&mut self, f: Ty, e: Ty) -> bool {
        matches!(self.kind(e), TyKind::FnPtr(_))
            && self.is_fn_item(f)
            && self.callable_sig(f).is_some_and(|(params, ret)| self.fn_ptr_ty(&params, ret) == self.resolve(e))
    }

    /// Coercion inside an aggregate value whose producer is in hand: a
    /// tuple literal, or a one-argument variant call such as `Some(&v)`
    /// where `&[u8]` is wanted. The inner coercions record on the inner
    /// expressions, so lowering applies them while building the value.
    /// Other shapes keep the plain type-mismatch error.
    fn coerce_deep(&mut self, found: Ty, expected: Ty, e: Option<ExprId>) -> bool {
        let Some(e) = e else { return false };
        let span = self.span(e);
        match (self.kind(found), self.kind(expected)) {
            (TyKind::Tuple(xs), TyKind::Tuple(ys)) => {
                let Expr::Tuple(elems) = self.p.ast.expr(e) else { return false };
                let (xs, ys) = (self.tys.tys_of(xs).to_vec(), self.tys.tys_of(ys).to_vec());
                if xs.len() != ys.len() || elems.len() != xs.len() {
                    return false;
                }
                if !xs.iter().zip(&ys).all(|(&x, &y)| self.ty_matchish(x, y) || self.ref_coercible(x, y) || self.fn_coercible(x, y)) {
                    return false;
                }
                elems.iter().zip(xs.iter().zip(&ys)).all(|(&el, (&x, &y))| self.coerce_at(x, y, span, Some(el)))
            }
            (TyKind::Adt(df, af), TyKind::Adt(de, ae)) if df == de => {
                let (fa, ea) = (self.tys.args(af).to_vec(), self.tys.args(ae).to_vec());
                if fa.len() != ea.len() || fa.len() != 1 {
                    return false;
                }
                let (Some(x), Some(y)) = (fa[0].as_ty(), ea[0].as_ty()) else { return false };
                if !self.ref_coercible(x, y) && !self.fn_coercible(x, y) {
                    return false;
                }
                // The producer must be a one-argument variant call
                // (`Some(..)`), whose argument carries the coercion.
                let Expr::Call { args, .. } = self.p.ast.expr(e) else { return false };
                if args.len() != 1 || !matches!(self.out.expr_res[self.ei(e)], Res::Variant(..) | Res::OptSome) {
                    return false;
                }
                let inner_found = self.out.expr_ty[self.ei(args[0])];
                self.coerce_at(inner_found, y, span, Some(args[0]))
            }
            _ => false,
        }
    }

    fn coerce_expr(&mut self, e: ExprId, found: Ty, expected: Ty) -> bool {
        let span = self.span(e);
        self.coerce_at(found, expected, span, Some(e))
    }

    /// The Self type of the only impl of `trait_def` for an integer (or
    /// float) type, if exactly one such impl exists and no blanket impl
    /// could also take the literal.
    fn literal_impl_ty(&self, trait_def: DefId, float: bool) -> Option<Ty> {
        let index = &self.p.gx.index;
        let mut found: Option<Ty> = None;
        for &id in index.impls_of_trait(trait_def) {
            let t = index.get(id).self_ty(&self.p.tys);
            match self.p.tys.kind(t) {
                TyKind::Int(_) if !float => {}
                TyKind::Float(_) if float => {}
                TyKind::Param(_) => return None,
                _ => continue,
            }
            if found.is_some_and(|f| f != t) {
                return None;
            }
            found = Some(t);
        }
        found
    }

    /// The unsizing coercion from a reference to `x` to a reference to
    /// the dyn type `y` (ARCH 2.8). A dyn source upcasts (the target
    /// principal is the source's or a supertrait of it) or drops auto
    /// traits; a sized source must implement the principal and every
    /// written auto trait, which are queued as obligations, and becomes
    /// a vtable request. Reports the error and returns None when the
    /// coercion cannot apply.
    fn unsize_coercion(&mut self, x: Ty, y: Ty, found: Ty, expected: Ty, span: Span, e: Option<ExprId>) -> Option<Coerce> {
        let p = self.p;
        let (mut x, y) = (self.deep(x), self.deep(y));
        let to = object::principal_of(&self.tys, y)?;
        // A written `&'static dyn Tr` target: lust tracks no reference
        // lifetimes, so only a borrow of a static item (or a reference
        // already typed `&'static`) proves it.
        if matches!(self.kind(expected), TyKind::Ref(Region::Static, ..))
            && !matches!(self.kind(found), TyKind::Ref(Region::Static, ..))
            && !e.is_some_and(|e| self.static_borrow(e))
        {
            let tn = self.tn(expected);
            self.err(
                "L0705",
                span,
                format!("lust cannot prove that this reference lives for `'static`, which `{tn}` requires"),
                "Borrow a `static` item here, or use `&(dyn Tr + 'static)` (a shorter reference to a `'static` object).",
            );
            return None;
        }
        // A numeric literal behind the coercion (`&3 as &dyn Tr`): as in
        // rustc, the one impl of the trait for a type of that kind
        // decides it, and otherwise the literal falls back to i32 (f64).
        if let TyKind::Infer(v) = self.tys.kind(x)
            && (v.is_int() || v.is_float())
        {
            let fallback = if v.is_int() { I32 } else { self.tys.float_ty(FloatTy::F64) };
            let t = self.literal_impl_ty(to.def, v.is_float()).unwrap_or(fallback);
            self.unify(x, t);
            x = t;
        }
        let want = match self.tys.kind(y) {
            TyKind::Dyn(b, _) => self.tys.dyn_bounds(b).auto,
            _ => AutoTraits::default(),
        };
        // A `'static` target: written (`+ 'static`), or implied by a
        // `'static` bound on the principal or one of its supertraits.
        let to_static = object::dyn_is_static(p, &self.tys, y);
        if let Some(from) = object::principal_of(&self.tys, x) {
            let have = object::dyn_auto(p, &self.tys, x);
            let auto_ok = (!want.send || have.send) && (!want.sync || have.sync) && (!want.unpin || have.unpin);
            let path_ok = if from.def == to.def {
                self.unify_args(from.args, to.args) && self.unify_bindings(from.bindings, to.bindings)
            } else {
                object::upcast_path(p, &mut self.tys, from, to).is_some()
            };
            if !auto_ok || !path_ok {
                self.mismatch(span, expected, found);
                return None;
            }
            // W-BORROW: `dyn Fn(&'static T)` is not as general as `dyn
            // Fn(&T)` (rustc E0308; `sig_static_mismatch`).
            if from.def == to.def
                && let Some(why) = self.sig_static_mismatch(x, y, false, 0)
            {
                self.err("L0110", span, why, "Write `&'static` in both types, or elide it in both.");
                return None;
            }
            if to_static && !object::dyn_is_static(p, &self.tys, x) {
                self.obl.push(obligations::Obligation::DynStatic { span });
            }
            return Some(Coerce::Unsize(expected));
        }
        if !self.sized_ok(x) {
            let tn = self.tn(x);
            self.err(
                "L0110",
                span,
                format!("the size for values of type `{tn}` cannot be known, so it cannot become a `dyn` value"),
                "Only a sized type converts to `&dyn Trait`; pass a reference to a sized value.",
            );
            return None;
        }
        // The source of a `'static` target must be `'static` itself; a
        // type param passes with a `'static` bound in the env.
        let borrows = if to_static { object::may_borrow_in(p, &self.tys, self.env(), x) } else { object::may_borrow(p, &self.tys, x) };
        if !to_static && borrows {
            self.dyn_borrow_src = true;
        }
        // An instance replays its template, which proved this under the
        // env's `'static` bounds (a `T: 'static` arg may be `&'static str`).
        let instance = matches!(p.gx.fn_class.get(self.fid.0 as usize), Some(generics::FnClass::Instance));
        if to_static && borrows && !instance {
            let tn = self.tn(x);
            self.err(
                "L0705",
                span,
                format!("lust cannot prove that `{tn}` lives for `'static`, which this `dyn` type requires"),
                "Use a type without references here, or drop the `'static` bound from the `dyn` type or its trait.",
            );
            return None;
        }
        let lang = p.gx.lang;
        // A `dyn Fn(A) -> R` value (ARCH 2.9): a closure (its body fn is
        // the vtable's call entry), a fn item, or a fn pointer; `R` is its
        // `Output`. A type param with an Fn bound (`hooks.push(Box::new(f))`
        // for `f: F`) checks here and builds the vtable in each instance.
        // A tuple constructor there is not supported yet.
        if lang.is_fn_family(to.def) {
            let fn_value = match self.kind(x) {
                TyKind::FnDef(def, _) => p.is_fn_item_def(def),
                TyKind::Closure(..) | TyKind::Param(_) | TyKind::FnPtr(_) => true,
                _ => false,
            };
            if !fn_value {
                let tn = self.tn(x);
                self.errs.push(generics::dyn_not_yet(span, &format!("a `dyn` Fn value made from `{tn}` (closures, fn items, and fn pointers only)")));
                return None;
            }
            let tr = object::with_self(&mut self.tys, to, x);
            for (assoc, g) in self.tys.bindings(to.bindings).to_vec() {
                if let GenericArg::Ty(ty) = g {
                    self.obl.push(obligations::Obligation::AssocEq { eq: AssocEqData { assoc, trait_args: tr.args, ty }, span });
                }
            }
        }
        let tr = object::with_self(&mut self.tys, to, x);
        self.obl.push_trait_at(tr, span, 0);
        for (on, def) in [(want.send, lang.send), (want.sync, lang.sync), (want.unpin, lang.unpin)] {
            if on {
                let args = self.tys.intern_args(&[GenericArg::Ty(x)]);
                self.obl.push_trait_at(TraitRef { def, args, bindings: EMPTY_BINDINGS }, span, 0);
            }
        }
        let y = object::erase_dyn_region(&mut self.tys, y);
        self.vtable_sites.push((x, y, span));
        Some(Coerce::Unsize(expected))
    }
    /// A method found through a user `Deref` impl of the receiver
    /// (rustc's autoderef, ARCH 2.10; `SmallVec` derefs to `[T]`): when
    /// nothing answers on `base` (the receiver after `before` builtin
    /// derefs) and `base` has a written `Deref` impl, the call checks
    /// on `&Target`, through `DerefMut` when it borrows mutably, and
    /// lowering calls the impl's fn first (`Checked::deref_recv`).
    /// None when no such impl applies.
    #[allow(clippy::too_many_arguments)]
    fn method_via_user_deref(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        before: u8,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        expected: Option<Ty>,
    ) -> Option<Ty> {
        let lang = self.p.gx.lang;
        if self.deref_depth >= 4 || self.tys.local_adt(base).is_none() {
            return None;
        }
        let (f, target, impl_args) = self.user_deref_fn(lang.deref, base, "deref", name_span)?;
        let depth = self.deref_depth;
        let tref = self.tys.mk_ref(false, target);
        self.deref_depth += 1;
        let ret = self.method_call_with_rt(e, recv, tref, name, name_span, args, turbofish, expected);
        self.deref_depth -= 1;
        let mutable = match self.out.expr_res[self.ei(e)] {
            Res::Method { autoref, .. } | Res::BuiltinMethod { autoref, .. } | Res::DynMethod { autoref, .. } => autoref == Autoref::RefMut,
            // The lookup on the target failed and reported why.
            Res::None => return Some(ret),
            _ => {
                self.errs.push(not_yet("L0820", name_span, "this method through a user `Deref` impl"));
                return Some(ERROR);
            }
        };
        let (f, impl_args) = if mutable {
            match self.user_deref_fn(lang.deref_mut, base, "deref_mut", name_span) {
                Some((g, _, a)) => (g, a),
                None => {
                    let tn = self.tn(base);
                    self.err(
                        "L0308",
                        name_span,
                        format!("cannot borrow data in a dereference of `{tn}` as mutable"),
                        format!("Implement `DerefMut` for `{tn}`."),
                    );
                    return Some(ERROR);
                }
            }
        } else {
            (f, impl_args)
        };
        let target_ref = self.tys.mk_ref(mutable, target);
        let idx = self.out.deref_recv.len();
        self.out.deref_recv.push((e, DerefRecv { depth, before, f, args: Vec::new(), f_mut: None, args_mut: Vec::new(), mutable, target_ref }));
        if self.p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
            self.deref_sites.push((DerefTable::Recv, idx, false, f, impl_args));
        }
        Some(ret)
    }

    /// One user `Deref` step of a place (a field access through it, or
    /// an explicit `*w`): records the impl's `deref`, and its
    /// `deref_mut` when `DerefMut` holds, for `e` after `before`
    /// builtin derefs; lowering picks by the place's use. Returns the
    /// target type; None when `base` has no written `Deref` impl.
    fn record_place_deref(&mut self, e: ExprId, base: Ty, before: u8, span: Span) -> Option<Ty> {
        let lang = self.p.gx.lang;
        if self.tys.local_adt(base).is_none() {
            return None;
        }
        let (f, target, args) = self.user_deref_fn(lang.deref, base, "deref", span)?;
        let (f_mut, args_mut) = match self.user_deref_fn(lang.deref_mut, base, "deref_mut", span) {
            Some((g, _, a)) => (Some(g), a),
            None => (None, Vec::new()),
        };
        let target_ref = self.tys.mk_ref(false, target);
        let idx = self.out.deref_recv.len();
        // Place steps record outermost first.
        let depth = self.out.deref_recv.iter().filter(|(x, _)| *x == e).count() as u8;
        self.out.deref_recv.push((e, DerefRecv { depth, before, f, args: Vec::new(), f_mut, args_mut: Vec::new(), mutable: false, target_ref }));
        let is_template = |cx: &Self, f: LocalDefId| cx.p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some());
        if is_template(self, f) {
            self.deref_sites.push((DerefTable::Recv, idx, false, f, args));
        }
        if let Some(g) = f_mut
            && is_template(self, g)
        {
            self.deref_sites.push((DerefTable::Recv, idx, true, g, args_mut));
        }
        Some(target)
    }

    /// A deref coercion through user `Deref` impls (rustc's coercion
    /// autoderef): from `found` (a reference to a user type, through
    /// any reference layers) by one or more impl steps to `&y` (`&mut
    /// y` through `DerefMut` when `mutable`). Records the steps on `e`
    /// and returns the coercion; None when no chain reaches `y`
    /// (nothing is bound then).
    fn user_deref_coercion(&mut self, e: ExprId, found: Ty, y: Ty, mutable: bool, span: Span) -> Option<Coerce> {
        let lang = self.p.gx.lang;
        let mut t = self.resolve(found);
        let mut before = 0u8;
        while let TyKind::Ref(_, _, inner) = self.kind(t) {
            t = self.resolve(inner);
            before += 1;
        }
        if before == 0 || self.tys.local_adt(t).is_none() {
            return None;
        }
        // (before, fn, args, target) per step.
        let mut steps: Vec<(u8, LocalDefId, Vec<GenericArg>, Ty)> = Vec::new();
        let snap = self.snapshot_vars();
        let obl_len = self.obl_len();
        for _ in 0..4 {
            let (trait_def, fname) = if mutable { (lang.deref_mut, "deref_mut") } else { (lang.deref, "deref") };
            if self.tys.local_adt(t).is_none() {
                break;
            }
            let Some((f, _, args)) = self.user_deref_fn(trait_def, t, fname, span) else { break };
            // `deref_mut` returns `&mut Target`: the target is the
            // same as `deref`'s.
            let Some((_, target, _)) = self.user_deref_fn(lang.deref, t, "deref", span) else { break };
            steps.push((before, f, args, target));
            let inner_snap = self.snapshot_vars();
            if self.unify(target, y) {
                let idx0 = self.out.deref_coerce.len();
                for (i, (b, f, args, target)) in steps.into_iter().enumerate() {
                    let target_ref = self.tys.mk_ref(mutable, target);
                    let template = self.p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some());
                    self.out.deref_coerce.push((
                        e,
                        DerefRecv { depth: i as u8, before: b, f, args: Vec::new(), f_mut: None, args_mut: Vec::new(), mutable, target_ref },
                    ));
                    if template {
                        self.deref_sites.push((DerefTable::Coerce, idx0 + i, false, f, args));
                    }
                }
                return Some(Coerce::UserDeref(self.tys.mk_ref(mutable, y)));
            }
            self.rollback_vars(inner_snap);
            t = target;
            before = 1;
        }
        self.rollback_vars(snap);
        self.obl_truncate(obl_len);
        None
    }

    /// The written impl of `Deref` (or `DerefMut`) for `base`: its
    /// `fname` fn, the target type, and the impl args. None for no
    /// impl or a core one.
    fn user_deref_fn(&mut self, trait_def: DefId, base: Ty, fname: &str, span: Span) -> Option<(LocalDefId, Ty, Vec<GenericArg>)> {
        use crate::traits::index::Synthetic;
        let p = self.p;
        let args = self.tys.intern_args(&[GenericArg::Ty(base)]);
        let tr = TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS };
        let Selection::Impl { id, args: impl_args, .. } = self.select_obligation_at(tr, span, 0) else { return None };
        let rec = p.gx.index.get(id).clone();
        if rec.synthetic != Synthetic::None {
            return None;
        }
        let f = rec.items.iter().copied().find_map(|d| p.local_def(d.hash).filter(|&l| p.name(p.fn_info(l).name) == fname))?;
        let ret = p.fn_info(f).ret;
        let ret = if impl_args.is_empty() { ret } else { subst(&mut self.tys, ret, &impl_args) };
        let ret = self.normalize_here(ret);
        let TyKind::Ref(_, _, target) = self.kind(ret) else { return None };
        let target = self.resolve(target);
        if matches!(self.kind(target), TyKind::Infer(_) | TyKind::Error) {
            return None;
        }
        Some((f, target, impl_args))
    }

    /// rustc's expected inputs for a closure argument: a generic call
    /// that returns its own type variable (`fn with<R>(f: impl FnOnce()
    /// -> R) -> R`) under an expected type fixes that variable first, so
    /// a closure body that needs its output type sees it (`let s: u32 =
    /// with(|| v.iter().sum())`). Only for a bare variable with a closure
    /// argument and no dyn in the expectation, where the result could
    /// still coerce (rustc's own expectation is not binding there).
    pub(super) fn expected_output_first(&mut self, ret: Ty, expected: Option<Ty>, args: &[ExprId]) {
        let Some(want) = expected else { return };
        if !matches!(self.kind(ret), TyKind::Infer(v) if !v.is_int() && !v.is_float())
            || !args.iter().any(|&a| matches!(self.p.ast.expr(a), Expr::Closure { .. }))
        {
            return;
        }
        let want = self.deep(want);
        if object::mentions_dyn(&self.tys, want) || matches!(self.kind(want), TyKind::Infer(_) | TyKind::Never | TyKind::Error) {
            return;
        }
        let snap = self.snapshot_vars();
        let obl_len = self.obl_len();
        if !self.unify(ret, want) {
            self.rollback_vars(snap);
            self.obl_truncate(obl_len);
        }
    }

    /// The pointees of an owning unsizing (`Box<T>` to `Box<dyn Tr>`,
    /// `Rc<T>` to `Rc<dyn Tr>`, ARCH 2.8): the same smart pointer on
    /// both sides, a dyn target, and a known source.
    fn owning_unsize_parts(&self, found: Ty, expected: Ty) -> Option<(Ty, Ty)> {
        let (f, e) = (self.resolve(found), self.resolve(expected));
        let (x, y) = match (self.tys.boxed_elem(f), self.tys.boxed_elem(e)) {
            (Some(x), Some(y)) => (x, y),
            _ => (self.tys.rc_elem(f)?, self.tys.rc_elem(e)?),
        };
        let (x, y) = (self.resolve(x), self.resolve(y));
        let known = !matches!(self.kind(x), TyKind::Infer(v) if !v.is_int() && !v.is_float());
        (known && matches!(self.kind(y), TyKind::Dyn(..))).then_some((x, y))
    }

    /// True when `e` borrows a static item (`&S0`): the one reference
    /// lust knows lives for `'static`.
    fn static_borrow(&self, e: ExprId) -> bool {
        match self.p.ast.expr(e) {
            Expr::Ref { raw: false, expr, .. } => matches!(self.out.expr_res[self.ei(*expr)], Res::Static(_)),
            _ => false,
        }
    }

    fn expect_expr(&mut self, e: ExprId, expected: Ty) -> Ty {
        let t = self.expr(e, Some(expected));
        self.coerce_expr(e, t, expected);
        t
    }

    // ---------- Blocks and statements ----------

    fn block(&mut self, b: ast::BlockId, expected: Option<Ty>) -> Ty {
        let block = self.p.ast.block(b);
        let scope = self.scopes.len();
        {
            let mut layer: Vec<((Sym, CtxtId), u32)> = Vec::new();
            for stmt in &block.stmts {
                if let Stmt::Item(idx) = stmt {
                    if let Some(name) = match &self.p.ast.stmt_items[*idx as usize].kind {
                        ItemKind::Fn(d) => Some((d.name, d.name_span.ctxt)),
                        ItemKind::Const(c) => c.name.map(|n| (n, c.name_span.ctxt)),
                        ItemKind::Static(st) => Some((st.name, st.name_span.ctxt)),
                        _ => None,
                    } {
                        layer.push((name, *idx));
                    }
                }
            }
            self.item_scopes.push(layer);
        }
        let mut diverges = false;
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let { pat, ty, init, els, .. } => {
                    let ty_ann = ty;
                    let annotated = ty.filter(|&t| generics::names_lifetime(self.p.ast, self.p.interner, t));
                    let declared = ty.map(|t| if annotated.is_some() { self.resolve_annotation(t) } else { self.resolve_written(t) });
                    let ty = match (declared, init) {
                        (Some(d), Some(init)) => {
                            let t = self.expr(*init, Some(d));
                            self.coerce_expr(*init, t, d);
                            if self.kind(t) == TyKind::Never {
                                diverges = true;
                            }
                            d
                        }
                        (Some(d), None) => d,
                        (None, Some(init)) => {
                            let t = self.expr(*init, None);
                            if self.kind(t) == TyKind::Never {
                                diverges = true;
                            }
                            t
                        }
                        (None, None) => self.new_var(false),
                    };
                    // The `else` block runs when the pattern does not
                    // match, so it is checked before the pattern binds
                    // anything (its names are not in scope there), and
                    // it must diverge, as in Rust.
                    if let Some(els_b) = els {
                        let et = self.block(*els_b, None);
                        if self.kind(et) != TyKind::Never {
                            self.err(
                                "L0110",
                                self.p.ast.block(*els_b).span,
                                "the `else` block of a `let...else` must diverge",
                                "End it with `return`, `break`, `continue`, or a panic.",
                            );
                        }
                    }
                    // A local is a value: a written type must be
                    // `Sized` when the let stores one, by an
                    // initializer or a by-value binding (`let x:
                    // str;`). A bare `let _: str;` stores nothing.
                    if let Some(w) = declared.and(*ty_ann)
                        && (init.is_some() || self.pat_binds_value(*pat))
                    {
                        self.require_sized(ty, self.p.ast.ty_span(w));
                    }
                    match self.p.ast.pat(*pat) {
                        // A plain name that resolves to a const, static,
                        // or unit path is a pattern, not a fresh binding:
                        // check it like any destructuring let, which
                        // rejects it as refutable where rustc does.
                        Pat::Binding { name, mutable: false, by_ref: false }
                            if self.lookup(*name, self.p.ast.pat_span(*pat).ctxt).is_none()
                                && !matches!(self.pat_ident(*name), PatIdent::Other) =>
                        {
                            if init.is_none() {
                                let s = self.p.ast.pat_span(*pat);
                                self.errs.push(unsupported(s, "destructuring in `let` without an initializer"));
                            } else {
                                // A `let...else` allows refutable
                                // patterns, like a match arm does.
                                self.pattern(*pat, ty, els.is_some());
                                if !self.pat_always_matches(*pat) {
                                    let s = self.p.ast.pat_span(*pat);
                                    if els.is_none() {
                                        self.err(
                                            "L0110",
                                            s,
                                            "refutable pattern in local binding",
                                            "Use `match`, `if let`, or `let...else` for a pattern that can fail.",
                                        );
                                    }
                                }
                            }
                        }
                        Pat::Binding { name, mutable, by_ref } => {
                            let (name, mutable, by_ref) = (*name, *mutable, *by_ref);
                            let lty = if by_ref { self.tys.mk_ref(mutable, ty) } else { ty };
                            // The binding's hygiene key is the pattern name's
                            // own context, not the `let` keyword's (ARCH 6.3).
                            let l = self.add_local(name, lty, mutable && !by_ref, self.p.ast.pat_span(*pat));
                            let pi = (pat.0 - self.out.pat_base) as usize;
                            self.out.pat_ty[pi] = ty;
                            let mode = if by_ref { BindMode::Ref(mutable) } else { BindMode::Move };
                            self.out.pat_res[pi] = PatRes::Binding { local: l, mode };
                        }
                        Pat::Wild => {
                            let pi = (pat.0 - self.out.pat_base) as usize;
                            self.out.pat_ty[pi] = ty;
                        }
                        _ => {
                            if init.is_none() {
                                let s = self.p.ast.pat_span(*pat);
                                self.errs.push(unsupported(s, "destructuring in `let` without an initializer"));
                            } else {
                                // A `let...else` allows refutable
                                // patterns, like a match arm does.
                                self.pattern(*pat, ty, els.is_some());
                                if !self.pat_always_matches(*pat) {
                                    let s = self.p.ast.pat_span(*pat);
                                    if els.is_none() {
                                        self.err(
                                            "L0110",
                                            s,
                                            "refutable pattern in local binding",
                                            "Use `match`, `if let`, or `let...else` for a pattern that can fail.",
                                        );
                                    }
                                }
                            }
                        }
                    }
                    if let Some(t) = annotated {
                        self.record_annotation(*pat, t);
                    }
                }
                // Body items and statement macros are rejected by the parser today.
                Stmt::Item(_) | Stmt::Macro { .. } => {}
                Stmt::Expr { expr, semi, .. } => {
                    let t = self.expr(*expr, if *semi { None } else { Some(UNIT) });
                    if self.kind(t) == TyKind::Never {
                        diverges = true;
                    } else if !semi && !self.unify(t, UNIT) {
                        let s = self.span(*expr);
                        self.err("L0110", s, format!("expected `()`, found `{}`", self.tn(t)), "Add a `;` after this expression.");
                    }
                }
            }
        }
        let t = match block.tail {
            Some(tail) => self.expr(tail, expected),
            None if diverges => NEVER,
            None => UNIT,
        };
        self.scopes.truncate(scope);
        self.item_scopes.pop();
        t
    }

    /// A `let` annotation that names a lifetime (W-BORROW): resolved like
    /// any written type, with explicit lifetimes allowed, since
    /// `record_annotation` keeps their regions for the borrow checker.
    fn resolve_annotation(&mut self, t: ast::TyId) -> Ty {
        let saved = self.body_scope.annotation;
        self.body_scope.annotation = true;
        let ty = self.resolve_written(t);
        self.body_scope.annotation = saved;
        ty
    }

    /// Records the regioned form of `let` annotation `t` for each binding
    /// pattern `pat` covers (W-BORROW): `'static` and the fn's named
    /// lifetimes keep their regions, elided ones are free. A pattern
    /// shape this cannot follow (by-ref bindings, `_`, nested patterns
    /// other than tuples) would drop the annotation's constraints, so it is
    /// a reject (L0203).
    fn record_annotation(&mut self, pat: ast::PatId, t: ast::TyId) {
        let p = self.p;
        let Some(r) = self.regioned_annotation(t, Region::Erased, true) else { return };
        if !self.annotate_pat(pat, r) {
            let s = p.ast.pat_span(pat);
            self.err(
                "L0203",
                s,
                "an explicit lifetime in the annotation of this pattern is not supported yet",
                "Bind a plain name (`let x: T = ..`), or a tuple of names.",
            );
        }
    }

    /// The regioned form of an annotation that names lifetimes (W-BORROW):
    /// `'static` and the fn's named lifetimes keep their regions, elided
    /// ones are free (`Region::Erased`). None after reporting `_` inside
    /// the annotation (no region form without inference, L0203).
    fn regioned_annotation(&mut self, t: ast::TyId, elided: Region, report: bool) -> Option<Ty> {
        let p = self.p;
        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
        let mut sc = self.body_scope.clone();
        sc.annotation = true;
        sc.infer_cell = None;
        sc.regions = generics::RegionMode::Keep { next: None, elided: Some(elided) };
        match generics::resolve_scoped(p.ast, p.interner, p.known, &cx, &mut self.tys, t, &sc) {
            Ok(r) => Some(r),
            Err(_) if !report => None,
            Err(_) => {
                let s = p.ast.ty_span(t);
                self.err("L0203", s, "an explicit lifetime in a type annotation with `_` is not supported yet", "Write the full type, or drop the lifetime.");
                None
            }
        }
    }

    fn annotate_pat(&mut self, pat: ast::PatId, r: Ty) -> bool {
        let pi = (pat.0 - self.out.pat_base) as usize;
        match (self.p.ast.pat(pat), self.out.pat_res.get(pi).copied()) {
            (Pat::Binding { .. }, Some(PatRes::Binding { local, mode: BindMode::Move })) => {
                self.out.annotations.push((local, r));
                true
            }
            (Pat::Tuple(elems), _) => match self.tys.kind(r) {
                TyKind::Tuple(ts) => {
                    let parts: Vec<Ty> = self.tys.tys_of(ts).to_vec();
                    let elems = elems.clone();
                    elems.len() == parts.len() && elems.iter().zip(parts).all(|(&e, t)| self.annotate_pat(e, t))
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn resolve_written(&mut self, t: ast::TyId) -> Ty {
        let p = self.p;
        let written_span = p.ast.ty_span(t);
        // A written type name in a body is a type-namespace binding read.
        // Primitive names and `Self` are scope layers, not bindings.
        if let ast::TyExpr::Path(segs) = p.ast.ty(t) {
            let seg = if segs.len() > 1 && segs[0].name == p.known.std {
                segs.last()
            } else if segs.len() == 1 {
                segs.first()
            } else {
                None
            };
            if let Some(seg) = seg {
                let name = seg.name;
                if p.known.int_ty(name).is_none()
                    && name != p.known.bool
                    && name != p.known.char
                    && name != p.known.str
                    && name != p.known.self_type
                {
                    self.binding(Namespace::Type, name);
                }
            }
        }
        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
        let span = p.ast.ty_span(t);
        match generics::resolve_scoped(p.ast, p.interner, p.known, &cx, &mut self.tys, t, &self.body_scope.clone()) {
            Ok(t) => {
                let t = self.instantiate_infers(t);
                if let Some(d) = object::dyn_type_diag(p, &self.tys, t, span) {
                    self.errs.push(d);
                }
                // A written type must be well-formed: the
                // bounds of every local Adt it applies, and the
                // trait ref of every projection in it as written,
                // become obligations here (rustc E0277 at the type).
                let n = self.normalize_here(t);
                if n != t {
                    self.wf_check_written(t, written_span);
                }
                self.wf_check_written(n, written_span);
                n
            }
            Err(d) => {
                self.errs.push(d);
                ERROR
            }
        }
    }

    /// Queues the well-formedness obligations of one body
    /// type: for every application of a local Adt inside it,
    /// the Adt's parameter bounds under the written arguments,
    /// and for every projection its trait ref. The parts
    /// `check::sized::parts` names must be `Sized` here (L0110).
    fn wf_check_written(&mut self, t: Ty, span: Span) {
        let generic = self.p.gx.has_generics;
        let mut stack: Vec<Ty> = vec![t];
        let mut seen: Vec<Ty> = Vec::new();
        let mut need: Vec<Ty> = Vec::new();
        while let Some(t) = stack.pop() {
            let t = self.deep(t);
            if seen.contains(&t) {
                continue;
            }
            seen.push(t);
            sized::parts(&self.tys, t, &mut |e| need.push(e));
            match self.tys.kind(t) {
                TyKind::Adt(d, a) => {
                    let argv: Vec<GenericArg> = self.tys.args(a).to_vec();
                    if generic && let Some(idx) = self.p.gx.adt_info.iter().position(|&(def, _)| def == d) {
                        let preds = self.p.gx.adt_generics[idx].predicates.clone();
                        if !preds.is_empty() {
                            self.push_predicates(&preds, &argv, span);
                        }
                    }
                    for g in argv {
                        if let Some(e) = g.as_ty() {
                            stack.push(e);
                        }
                    }
                }
                TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => stack.push(e),
                TyKind::Tuple(ts) => stack.extend(self.tys.tys_of(ts).iter().copied()),
                TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => {
                    if let TyKind::Projection(assoc, _) = self.tys.kind(t)
                        && generic
                        && let Some(def) = self.p.gx.index.trait_of_assoc(assoc.0)
                    {
                        self.obl.push_trait_at(TraitRef { def, args: a, bindings: EMPTY_BINDINGS }, span, 0);
                    }
                    let argv: Vec<GenericArg> = self.tys.args(a).to_vec();
                    for g in argv {
                        if let Some(e) = g.as_ty() {
                            stack.push(e);
                        }
                    }
                }
                TyKind::FnPtr(sig) => {
                    let b = self.tys.sig(sig);
                    stack.extend(self.tys.tys_of(b.value.inputs).iter().copied());
                    stack.push(b.value.output);
                }
                TyKind::Dyn(b, _) => {
                    if let Some(pr) = self.tys.dyn_bounds(b).principal {
                        stack.extend(self.tys.args(pr.value.args).iter().skip(1).filter_map(|g| g.as_ty()));
                    }
                }
                _ => {}
            }
        }
        for e in need {
            self.require_sized(e, span);
        }
    }

    /// True when a pattern binds some part by value (a binding
    /// without `ref`, anywhere inside it).
    fn pat_binds_value(&self, pat: PatId) -> bool {
        match self.p.ast.pat(pat) {
            Pat::Binding { by_ref, .. } => !by_ref,
            Pat::At { by_ref, inner, .. } => !by_ref || self.pat_binds_value(*inner),
            Pat::TupleStruct { elems, .. } | Pat::Tuple(elems) | Pat::Or(elems) => elems.iter().any(|&e| self.pat_binds_value(e)),
            Pat::Struct { fields, .. } => fields.iter().any(|&(_, s)| self.pat_binds_value(s)),
            Pat::Slice { prefix, middle, suffix } => {
                prefix.iter().chain(suffix.iter()).any(|&s| self.pat_binds_value(s)) || middle.is_some_and(|m| self.pat_binds_value(m))
            }
            Pat::Ref { inner, .. } | Pat::Paren(inner) => self.pat_binds_value(*inner),
            _ => false,
        }
    }

    /// Reports L0110 when `t` is not `Sized` here (a value
    /// position: a `let` binding, a closure param or return).
    fn require_sized(&mut self, t: Ty, span: Span) {
        if !self.sized_ok(t) {
            let d = sized::unsized_diag(self.p, &self.tys, t, span);
            self.errs.push(d);
        }
    }

    /// Instantiates one fn template at a call site: fresh
    /// variables for its parameters (explicit turbofish types
    /// where written), the substituted signature, bound
    /// obligations queued, and the site recorded for mono.
    /// Returns (params, ret, args).
    fn instantiate_template(
        &mut self,
        e: ExprId,
        template: LocalDefId,
        generics: &Generics,
        explicit: &[Option<GenericArg>],
        span: Span,
    ) -> (Vec<Ty>, Ty, Vec<GenericArg>) {
        let p = self.p;
        let info = p.fn_info(template);
        // More written generic arguments than the item has
        // parameters is an arity error (rustc E0107); `explicit`
        // is aligned to `generics.params` at every call site. The
        // params of `impl Trait` arguments (`impl#N`, appended last)
        // take no written argument.
        let declared = generics.params.iter().filter(|g| !self.name(g.name).starts_with("impl#")).count();
        if explicit.len() > declared {
            self.err("L0107", span, format!("too many generic arguments: this item takes {declared}"), "Remove the extra arguments.");
        }
        let mut args: Vec<GenericArg> = Vec::with_capacity(generics.params.len());
        for (i, param) in generics.params.iter().enumerate() {
            let given = explicit.get(i).copied().flatten();
            // A written argument of the wrong kind (a type where a
            // const parameter sits, or the reverse) is an error,
            // never a silent substitution.
            let given = match (given, &param.kind) {
                (Some(GenericArg::Ty(_)), ParamKind::Type)
                | (Some(GenericArg::Const(_)), ParamKind::Const(_))
                | (Some(GenericArg::Lifetime(_)), ParamKind::Lifetime)
                | (None, _) => given,
                (Some(_), _) => {
                    self.err(
                        "L0110",
                        span,
                        "generic argument has the wrong kind for its parameter",
                        "Match each argument to its parameter: a type for a type parameter, a const value for a const parameter.",
                    );
                    None
                }
            };
            args.push(match (given, &param.kind) {
                (Some(g), _) => g,
                (None, ParamKind::Type) => GenericArg::Ty(self.new_var(false)),
                (None, ParamKind::Lifetime) => GenericArg::Lifetime(Region::Erased),
                (None, ParamKind::Const(_)) => GenericArg::Const(self.fresh_const_var()),
            });
        }
        if self.check_const_args(generics, &args, span) {
            self.check_written_const_tys(e, generics, explicit, span);
        }
        let params: Vec<Ty> = info.params.iter().map(|&t| subst(&mut self.tys, t, &args)).collect();
        let ret = subst(&mut self.tys, info.ret, &args);
        let ret = self.callee_ret(ret);
        let preds = generics.predicates.clone();
        let fn_bounds = p.regions.fns.get(&template).map(|s| s.fn_bounds.clone()).unwrap_or_default();
        self.push_predicates_with(&preds, &args, span, &fn_bounds);
        self.generic_sites.push((self.ei(e), template, args.clone()));
        (params, ret, args)
    }

    /// The explicit generic arguments written on a call path
    /// (`f::<u8, _>(..)`), resolved in this body's scope and
    /// aligned to parameter positions. Unwritten positions are
    /// None.
    /// Checks written const generic arguments against their params'
    /// declared types (rustc E0308, and the out-of-range literal error):
    /// an integer in the type's range, a bool, a char, or a const param
    /// of this body with the same declared type. Reports once and
    /// returns false on a misfit.
    fn check_const_args(&mut self, generics: &Generics, args: &[GenericArg], span: Span) -> bool {
        for (param, arg) in generics.params.iter().zip(args) {
            let (ParamKind::Const(want), GenericArg::Const(c)) = (param.kind, *arg) else { continue };
            let want = self.deep(want);
            let fits = match (self.tys.const_kind(self.resolve_const(c)), self.kind(want)) {
                (ConstKind::Int(v), TyKind::Int(it)) => generics::const_int_fits(v, it),
                (ConstKind::Bool(_), TyKind::Bool) | (ConstKind::Char(_), TyKind::Char) => true,
                (ConstKind::Param(i), _) => {
                    let have = match self.p.gx.fn_templates.get(self.fid.0 as usize).and_then(|t| t.as_ref()) {
                        Some(t) => match t.generics.params.get(i as usize).map(|g| g.kind) {
                            Some(ParamKind::Const(t)) => Some(t),
                            _ => None,
                        },
                        None => None,
                    };
                    have.is_none_or(|h| self.deep(h) == want)
                }
                (ConstKind::Infer(_), _) => true,
                _ => false,
            };
            if !fits {
                let tn = self.tn(want);
                self.err(
                    "L0110",
                    span,
                    format!("mismatched types: this const argument is not a value of type `{tn}`"),
                    format!("Write a `{tn}` value in its range."),
                );
                return false;
            }
        }
        true
    }

    /// A braced or literal const generic argument on a call path
    /// (`f::<3>`, `f::<{ -3 }>`, `f::<true>`, `f::<{ N }>`): its value
    /// by the scalar evaluator. A form it cannot evaluate is an error,
    /// never an unwritten argument (that left the instance unmade).
    fn const_call_arg(&mut self, e: ExprId) -> GenericArg {
        let kind = self.const_call_kind(e);
        match kind {
            Some(k) => GenericArg::Const(self.tys.intern_const(k)),
            None => {
                let span = self.span(e);
                self.err(
                    "L0110",
                    span,
                    "this const generic argument form is not supported here",
                    "Write a literal, a const item, or a const param, such as `::<3>`.",
                );
                GenericArg::Const(self.fresh_const_var())
            }
        }
    }

    /// The value of a const generic argument expression (see
    /// `const_call_arg`), or None for a form the evaluator cannot read.
    fn const_call_kind(&mut self, e: ExprId) -> Option<ConstKind> {
        let p = self.p;
        let inner = match p.ast.expr(e) {
            Expr::Block(b) if p.ast.block(*b).stmts.is_empty() => p.ast.block(*b).tail.unwrap_or(e),
            _ => e,
        };
        match p.ast.expr(inner) {
            Expr::Bool(b) => Some(ConstKind::Bool(*b)),
            Expr::Char(c) => Some(ConstKind::Char(*c)),
            Expr::Path(segs)
                if segs.len() == 1
                    && let Some((i, _, val)) = self.const_param(segs[0].name) =>
            {
                Some(val.unwrap_or(ConstKind::Param(i)))
            }
            _ => crate::check::collect::eval_const_int(p.ast, p.interner, p.known, inner).map(|v| ConstKind::Int(v as u128)),
        }
    }

    /// The written forms of a call's turbofish const args against their
    /// params' declared types (`f::<{ 3u8 }>()` or `f::<L>()` with
    /// `const L: u8` for a `usize` param, rustc E0308);
    /// `check_const_args` checks the values. The written args are the
    /// last entries of `explicit` (a method's impl args come first). An
    /// entry that is not the written arg's value is left alone.
    fn check_written_const_tys(&mut self, e: ExprId, generics: &Generics, explicit: &[Option<GenericArg>], span: Span) {
        let p = self.p;
        fn angle(seg: Option<&ast::PathSeg>) -> &[ast::GenericArg] {
            match seg.map(|s| &s.args) {
                Some(ast::GenericArgs::Angle(a)) => a.as_slice(),
                _ => &[],
            }
        }
        let written: &[ast::GenericArg] = match p.ast.expr(e) {
            Expr::MethodCall { generic_args, .. } => generic_args,
            Expr::Call { callee, .. } => match p.ast.expr(*callee) {
                Expr::Path(segs) => angle(segs.last()),
                _ => &[],
            },
            Expr::Path(segs) => angle(segs.last()),
            _ => &[],
        };
        let Some(offset) = explicit.len().checked_sub(written.len()) else { return };
        for (j, w) in written.iter().enumerate() {
            let i = offset + j;
            let (Some(Some(GenericArg::Const(c))), Some(ParamKind::Const(t))) = (explicit.get(i), generics.params.get(i).map(|g| g.kind))
            else {
                continue;
            };
            let t = self.deep(t);
            let Some(want) = generics::ConstScalar::of(&self.tys, t) else { continue };
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            let fits = match w {
                ast::GenericArg::Const(x) => {
                    if self.const_call_kind(*x).map(|k| self.tys.intern_const(k)) != Some(*c) {
                        continue;
                    }
                    let scope = &self.body_scope;
                    generics::check_const_expr_ty(p.ast, p.interner, p.known, &cx, &mut self.tys, scope, *x, *c, want, span, "").is_ok()
                }
                // A bare name in a const position (`f::<L>`).
                ast::GenericArg::Type(t) => match p.ast.ty(*t) {
                    ast::TyExpr::Path(segs) if segs.len() == 1 => {
                        let scope = &self.body_scope;
                        generics::const_name_ty(p.ast, p.interner, p.known, &cx, &mut self.tys, scope, segs[0].name).is_none_or(|s| s == want)
                    }
                    _ => true,
                },
                _ => true,
            };
            if !fits {
                let tn = self.tn(t);
                self.err(
                    "L0110",
                    span,
                    format!("mismatched types: this const argument is not a value of type `{tn}`"),
                    format!("Write a `{tn}` value, or cast with `as {tn}`."),
                );
                return;
            }
        }
    }

    fn explicit_call_args(&mut self, callee: ExprId) -> Vec<Option<GenericArg>> {
        let p = self.p;
        let ast::Expr::Path(segs) = p.ast.expr(callee) else { return Vec::new() };
        let Some(seg) = segs.last() else { return Vec::new() };
        let ast::GenericArgs::Angle(written) = &seg.args else { return Vec::new() };
        let mut out = Vec::new();
        for a in written {
            out.push(match a {
                ast::GenericArg::Type(t) => {
                    // A bare path the parser read as a type may name
                    // a const (`h::<N>`): rustc reads it by the
                    // parameter's kind. When the name is no type
                    // here but is a const item, read the const;
                    // `instantiate_template` rejects a kind mismatch.
                    if let ast::TyExpr::Path(segs) = p.ast.ty(*t)
                        && segs.iter().all(|s| !s.has_args())
                    {
                        let is_param =
                            |cx: &Self, n: Sym| cx.body_scope.param_tys.iter().any(|(pn, _)| *pn == n) || n == p.known.self_type;
                        match segs.as_slice() {
                            // A const param of this body (`f::<N>()`).
                            [seg] if let Some((i, _, val)) = self.const_param(seg.name) => {
                                Some(GenericArg::Const(self.tys.intern_const(val.unwrap_or(ConstKind::Param(i)))))
                            }
                            [seg]
                                if !is_param(self, seg.name)
                                    && !p.type_names.contains_key(&seg.name)
                                    && !p.aliases.contains_key(&seg.name)
                                    && p.const_names.contains_key(&seg.name) =>
                            {
                                use crate::ty::consteval::ConstValue;
                                let idx = p.const_names[&seg.name];
                                match &p.consts[idx as usize].value {
                                    ConstValue::Int(v) => u128::try_from(*v)
                                        .ok()
                                        .map(|v| GenericArg::Const(self.tys.intern_const(ConstKind::Int(v)))),
                                    ConstValue::Bool(b) => Some(GenericArg::Const(self.tys.intern_const(ConstKind::Bool(*b)))),
                                    ConstValue::Char(c) => Some(GenericArg::Const(self.tys.intern_const(ConstKind::Char(*c)))),
                                    _ => Some(GenericArg::Ty(self.resolve_written(*t))),
                                }
                            }
                            // Multi-segment paths stay type paths:
                            // a const path as a generic argument
                            // needs braces in Rust (`h::<{ S::N }>`).
                            _ => Some(GenericArg::Ty(self.resolve_written(*t))),
                        }
                    } else {
                        Some(GenericArg::Ty(self.resolve_written(*t)))
                    }
                }
                ast::GenericArg::Lifetime(_) => None,
                ast::GenericArg::Const(e) => Some(self.const_call_arg(*e)),
                ast::GenericArg::Binding { span, .. } => {
                    self.errs.push(not_yet("L0621", *span, "associated bindings in call arguments"));
                    None
                }
            });
        }
        out
    }

    // ---------- Expressions ----------

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

    /// True when a condition is a let chain (some `&&` element is a `let`).
    fn is_let_chain(&self, cond: ExprId) -> bool {
        let mut elems = Vec::new();
        self.split_and(cond, &mut elems);
        elems.iter().any(|&e| matches!(self.p.ast.expr(e), Expr::Let { .. }))
    }

    /// Checks a let-chain condition: each `let` element binds into the
    /// current scope (visible to later elements and the then block, which
    /// the caller checks before truncating), each other element is bool.
    fn check_chain(&mut self, cond: ExprId) {
        let mut elems = Vec::new();
        self.split_and(cond, &mut elems);
        for el in elems {
            match self.p.ast.expr(el) {
                Expr::Let { pat, scrut } => {
                    let (pat, scrut) = (*pat, *scrut);
                    let st = self.expr(scrut, None);
                    self.set(el, BOOL);
                    self.pattern(pat, st, true);
                }
                _ => {
                    self.expect_expr(el, BOOL);
                }
            }
        }
    }

    fn expr(&mut self, e: ExprId, expected: Option<Ty>) -> Ty {
        let t = self.expr_inner(e, expected);
        self.set(e, t)
    }

    fn expr_inner(&mut self, e: ExprId, expected: Option<Ty>) -> Ty {
        let span = self.span(e);
        let p = self.p;
        match p.ast.expr(e) {
            Expr::Int(_, Some(s)) => int(IntTy::from_suffix(*s)),
            Expr::Int(_, None) => match expected.map(|t| (self.resolve(t), self.kind(t))) {
                Some((t, TyKind::Int(_))) => t,
                Some((t, k)) if k.is_int_infer() => t,
                _ => self.new_var(true),
            },
            Expr::Float(i) => {
                let text = p.ast.strings[*i as usize].as_str();
                match crate::check::collect::parse_float_literal(text) {
                    Some((_, suffix)) => match suffix {
                        Some(f) => self.tys.float_ty(f),
                        // An unsuffixed float literal stays a float
                        // variable until a use decides f32 or f64; it
                        // defaults to f64 at body end, like rustc.
                        None => match expected.map(|t| (self.resolve(t), self.kind(t))) {
                            Some((t, TyKind::Float(_))) => t,
                            Some((t, k)) if k.is_float_infer() => t,
                            _ => self.new_float_var(),
                        },
                    },
                    None => {
                        self.err("L0118", span, "invalid float literal", "Write the literal in a simpler form.");
                        ERROR
                    }
                }
            }
            Expr::Bool(_) => BOOL,
            Expr::Char(_) => CHAR,
            Expr::Str(_) => REF_STR,
            Expr::Unit => UNIT,
            Expr::SelfValue => match self.lookup(p.known.self_value, span.ctxt) {
                Some(l) => {
                    self.set_res(e, Res::Local(l));
                    self.out.locals[l as usize].ty
                }
                None => {
                    self.err("L0101", span, "`self` is not available here", "Only methods with a `self` parameter can use `self`.");
                    ERROR
                }
            },
            Expr::Path(segs) => {
                self.lifetime_turbofish(segs);
                self.path_expr(e, segs, span)
            }
            Expr::Block(b) => self.block(*b, expected),
            Expr::If { cond, then, els } if self.is_let_chain(*cond) => {
                let scope = self.scopes.len();
                self.check_chain(*cond);
                match els {
                    None => {
                        let t = self.block(*then, Some(UNIT));
                        let bspan = p.ast.block(*then).span;
                        if let Some(tail) = p.ast.block(*then).tail {
                            self.coerce_expr(tail, t, UNIT);
                        } else {
                            self.coerce_at(t, UNIT, bspan, None);
                        }
                        self.scopes.truncate(scope);
                        UNIT
                    }
                    Some(els) => {
                        let t1 = self.block(*then, expected);
                        self.scopes.truncate(scope);
                        let t2 = self.expr(*els, expected.or(Some(t1)));
                        if let Some(d) = self.dyn_ref_expectation(expected) {
                            self.coerce_block_tail(*then, t1, d);
                            self.coerce_expr(*els, t2, d);
                            return d;
                        }
                        if expected.is_none()
                            && let Some(tail) = p.ast.block(*then).tail
                            && self.lub_flip(&[tail], t1, t2)
                        {
                            return t2;
                        }
                        self.join(t1, t2, Some(*els), span)
                    }
                }
            }
            Expr::If { cond, then, els } => {
                self.expect_expr(*cond, BOOL);
                match els {
                    None => {
                        let t = self.block(*then, Some(UNIT));
                        let bspan = p.ast.block(*then).span;
                        if let Some(tail) = p.ast.block(*then).tail {
                            self.coerce_expr(tail, t, UNIT);
                        } else {
                            self.coerce_at(t, UNIT, bspan, None);
                        }
                        UNIT
                    }
                    Some(els) => {
                        let t1 = self.block(*then, expected);
                        let t2 = self.expr(*els, expected.or(Some(t1)));
                        if let Some(d) = self.dyn_ref_expectation(expected) {
                            self.coerce_block_tail(*then, t1, d);
                            self.coerce_expr(*els, t2, d);
                            return d;
                        }
                        if expected.is_none()
                            && let Some(tail) = p.ast.block(*then).tail
                            && self.lub_flip(&[tail], t1, t2)
                        {
                            return t2;
                        }
                        self.join(t1, t2, Some(*els), span)
                    }
                }
            }
            Expr::While { label, cond, body } if self.is_let_chain(*cond) => {
                let scope = self.scopes.len();
                self.check_chain(*cond);
                self.loops.push(LoopCtx { break_ty: None, is_loop: false, is_block: false, label: label_of(label) });
                let t = self.block(*body, Some(UNIT));
                self.unit_body(t, *body);
                self.loops.pop();
                self.scopes.truncate(scope);
                UNIT
            }
            Expr::While { label, cond, body } => {
                self.expect_expr(*cond, BOOL);
                self.loops.push(LoopCtx { break_ty: None, is_loop: false, is_block: false, label: label_of(label) });
                let t = self.block(*body, Some(UNIT));
                self.unit_body(t, *body);
                self.loops.pop();
                UNIT
            }
            Expr::Loop { label, body } => {
                self.loops.push(LoopCtx { break_ty: None, is_loop: true, is_block: false, label: label_of(label) });
                let t = self.block(*body, Some(UNIT));
                self.unit_body(t, *body);
                let l = self.loops.pop().unwrap();
                l.break_ty.unwrap_or(NEVER)
            }
            Expr::For { label, pat, iter, body } => {
                let item = self.for_iter(e, *iter);
                let scope = self.scopes.len();
                self.pattern(*pat, item, false);
                if !self.pat_always_matches(*pat) {
                    let s = self.p.ast.pat_span(*pat);
                    self.err(
                        "L0110",
                        s,
                        "refutable pattern in `for` loop binding",
                        "Use `while let` or `match` for a pattern that can fail.",
                    );
                }
                self.loops.push(LoopCtx { break_ty: None, is_loop: false, is_block: false, label: label_of(label) });
                let t = self.block(*body, Some(UNIT));
                self.unit_body(t, *body);
                self.loops.pop();
                self.scopes.truncate(scope);
                UNIT
            }
            Expr::Match { scrut, arms } => {
                let st = self.expr(*scrut, None);
                // ARCH 2.12 run point: a match must know the scrutinee enum.
                self.run_obligations(false);
                let mut result: Option<Ty> = None;
                let mut sites: Vec<ExprId> = Vec::new();
                for arm in arms {
                    let scope = self.scopes.len();
                    self.pattern(arm.pat, st, true);
                    if let Some(g) = arm.guard {
                        // A by-value slice-pattern middle binds
                        // before its guard runs (there is no
                        // subarray place to read it through by
                        // reference), so a failed guard would drop
                        // the moved parts early. Copy elements are
                        // exact already; anything else is a reject
                        // for now rather than wrong drop order.
                        if self.slice_middle_move_blocks_guard(arm.pat) {
                            self.errs.push(unsupported(self.span(g), "match guards over a by-value slice-pattern middle"));
                        }
                        self.expect_expr(g, BOOL);
                    }
                    let bt = self.expr(arm.body, expected.or(result));
                    if let Some(d) = self.dyn_ref_expectation(expected) {
                        self.coerce_expr(arm.body, bt, d);
                        result = Some(d);
                        self.scopes.truncate(scope);
                        continue;
                    }
                    result = Some(match result {
                        None => bt,
                        Some(r) if expected.is_none() && self.lub_flip(&sites, r, bt) => bt,
                        Some(r) => self.join(r, bt, Some(arm.body), self.span(arm.body)),
                    });
                    sites.push(arm.body);
                    self.scopes.truncate(scope);
                }
                self.exhaustive(st, arms, span);
                result.unwrap_or(NEVER)
            }
            Expr::Call { callee, args } => {
                if let Expr::Path(segs) = p.ast.expr(*callee) {
                    self.lifetime_turbofish(segs);
                }
                if let Some(t) = self.self_from_expected_call(e, *callee, args, expected, span) {
                    return t;
                }
                self.call(e, *callee, args, span, expected)
            }
            Expr::MethodCall { recv, name, name_span, generic_args, args } => {
                self.method_chain(e, *recv, *name, *name_span, args, generic_args, expected)
            }
            Expr::Field { base, name } => {
                let bt = self.expr(*base, None);
                // ARCH 2.12 run point: a field access must know the base type.
                self.run_obligations(false);
                let bt = self.deep(bt);
                let (mut derefs, mut inner) = self.autoderef_smart(bt);
                for step in 0..=4 {
                    if let Some(a) = self.tys.local_adt(inner) {
                        let adt = p.adt(a);
                        if !adt.is_enum
                            && let Some(i) = adt.variants[0].fields.iter().position(|f| f.name == *name)
                        {
                            self.check_field_vis(a, *name, span);
                            self.set_res(e, Res::Field { derefs, index: i as u32 });
                            // A generic Adt's fields are the template's,
                            // substituted with this value's args (the
                            // instance AdtDef already has them concrete).
                            let fty = adt.variants[0].fields[i].ty;
                            return match self.tys.adt_parts(inner) {
                                Some((_, args)) if args != EMPTY_ARGS && self.tys.flags(fty).contains_param() => {
                                    let gargs: Vec<GenericArg> = self.tys.args(args).to_vec();
                                    self.subst_norm(fty, &gargs, span)
                                }
                                _ => fty,
                            };
                        }
                    }
                    // rustc's autoderef goes on through a user `Deref`
                    // impl (`info.file_index` on a type that derefs to
                    // the struct holding it).
                    if step == 4 {
                        break;
                    }
                    let Some(target) = self.record_place_deref(e, inner, derefs, span) else { break };
                    let tref = self.tys.mk_ref(false, target);
                    (derefs, inner) = self.autoderef_smart(tref);
                }
                if !matches!(self.kind(inner), TyKind::Error) {
                    let tn = self.tn(bt);
                    self.err("L0103", span, format!("no field `{}` on type `{tn}`", self.name(*name)), "Check the field name.");
                }
                ERROR
            }
            Expr::Index { base, index } => {
                let bt = self.expr(*base, None);
                // ARCH 2.12 run point: an index must know the indexed type; the
                // index type then follows from the selected `Index` impl.
                self.run_obligations(false);
                let (mut derefs, mut inner) = self.autoderef_smart(bt);
                // A user type indexes through its `Deref` impls (a wrapper
                // over a Vec or slice), as rustc's index autoderef.
                for _ in 0..4 {
                    let indexable = matches!(self.kind(inner), TyKind::Array(..) | TyKind::Slice(_) | TyKind::Str | TyKind::Error)
                        || self.tys.vec_elem(inner).is_some()
                        || self.tys.is_string_ty(inner);
                    // rustc tries the type's own `Index` impl before any
                    // deref; `[]` through a user `Index` impl is not
                    // supported yet, so such a type stops here (L0113).
                    if indexable || self.has_user_index_impl(inner) {
                        break;
                    }
                    let Some(target) = self.record_place_deref(e, inner, derefs, span) else { break };
                    let tref = self.tys.mk_ref(false, target);
                    (derefs, inner) = self.autoderef_smart(tref);
                }
                if let Expr::Range { lo, hi, .. } = p.ast.expr(*index) {
                    // A range index makes a slice place. Bounds are usize.
                    // The range expression itself is not checked as a value;
                    // give it the error-free unit record so lowering (which
                    // reads the bounds directly) never sees a stale type.
                    for b in [lo, hi].into_iter().flatten() {
                        self.expect_expr(*b, USIZE);
                    }
                    self.set(*index, UNIT);
                    // A range index into a string makes a str place; the
                    // runtime range check also validates char boundaries.
                    if self.kind(inner) == TyKind::Str || self.tys.is_string_ty(inner) {
                        self.set_res(e, Res::SliceIndex { derefs });
                        return STR;
                    }
                    let elem = match self.kind(inner) {
                        TyKind::Array(elem, _) | TyKind::Slice(elem) => Some(elem),
                        _ => self.tys.vec_elem(inner),
                    };
                    match elem {
                        Some(elem) => {
                            self.set_res(e, Res::SliceIndex { derefs });
                            return self.tys.intern(TyKind::Slice(elem));
                        }
                        None => {
                            if !matches!(self.kind(inner), TyKind::Error) {
                                let tn = self.tn(bt);
                                self.err(
                                    "L0113",
                                    span,
                                    format!("cannot slice a value of type `{tn}`"),
                                    "Slice an array, a Vec, a slice, or a string.",
                                );
                            }
                            return ERROR;
                        }
                    }
                }
                self.expect_expr(*index, USIZE);
                match self.kind(inner) {
                    TyKind::Array(elem, _) | TyKind::Slice(elem) => {
                        self.set_res(e, Res::Index { derefs });
                        elem
                    }
                    _ if self.tys.vec_elem(inner).is_some() => {
                        self.set_res(e, Res::Index { derefs });
                        self.tys.vec_elem(inner).unwrap()
                    }
                    TyKind::Error => ERROR,
                    _ if self.kind(inner) == TyKind::Str || self.tys.is_string_ty(inner) => {
                        self.err(
                            "L0113",
                            span,
                            "strings cannot be indexed by an integer",
                            "Use `.chars()` later, or `.as_bytes()`. Not supported in the prototype yet.",
                        );
                        ERROR
                    }
                    _ => {
                        let tn = self.tn(bt);
                        self.err(
                            "L0113",
                            span,
                            format!("cannot index into a value of type `{tn}`"),
                            "Only Vec supports indexing in the prototype.",
                        );
                        ERROR
                    }
                }
            }
            Expr::Binary { op, lhs, rhs } => self.binary_chain(e, *op, *lhs, *rhs, span),
            Expr::Unary { op, expr } => {
                if *op == UnOp::Neg
                    && let Expr::Int(..) = p.ast.expr(*expr)
                {
                    self.negated_lits.push(*expr);
                }
                let t = self.expr(*expr, expected);
                // Rust has `-` and `!` for `&T` (shared references only, not `&mut T`).
                let (d, inner) = match self.kind(t) {
                    TyKind::Ref(_, Mut::Shared, inner) => (1, inner),
                    _ => (0, t),
                };
                self.set_res(e, Res::Bin { ld: d, rd: 0 });
                let k = self.kind(inner);
                match (op, k) {
                    (UnOp::Neg, TyKind::Float(_)) => inner,
                    (UnOp::Neg, k) if k.is_float_infer() => inner,
                    (UnOp::Neg, TyKind::Int(i)) if i.signed() => inner,
                    // The variable may still become unsigned (`let y: u64
                    // = x`): queue `Neg` for body end, as `x.neg()` does.
                    (UnOp::Neg, k) if k.is_int_infer() => {
                        let args_id = self.tys.intern_args(&[GenericArg::Ty(inner)]);
                        let tr = TraitRef { def: p.gx.lang.neg, args: args_id, bindings: EMPTY_BINDINGS };
                        self.obl.push_trait_at(tr, span, 0);
                        inner
                    }
                    (UnOp::Not, TyKind::Bool | TyKind::Int(_)) => inner,
                    (UnOp::Not, k) if k.is_int_infer() => inner,
                    (_, TyKind::Error) => ERROR,
                    // A user operator impl answers for the operand type as
                    // written (core's `Neg for &i32` and kin are scalar
                    // only): `-&v` needs `impl Neg for &V`.
                    _ => match self.trait_unop(e, *op, t, 0, span) {
                        Some(t) => t,
                        None => {
                            let tn = self.tn(t);
                            let sym = if *op == UnOp::Neg { "-" } else { "!" };
                            self.err(
                                "L0113",
                                span,
                                format!("cannot apply unary `{sym}` to type `{tn}`"),
                                "Use a signed integer type for `-`, or a bool or integer for `!`.",
                            );
                            ERROR
                        }
                    },
                }
            }
            Expr::Cast { expr, ty } => {
                let target = self.resolve_written(*ty);
                // An unsuffixed literal takes its type from the cast
                // target: `300 as u8` is a u8 literal out of range,
                // and `3000000000 as u64` needs no i32 fit first.
                let exp = if crate::ty::consteval::is_unsuffixed_lit(p.ast, *expr) { Some(target) } else { None };
                let t = self.expr(*expr, exp);
                // A cast to a dyn reference is a coercion cast: rustc
                // allows any coercion through `as` (ARCH 2.8).
                if matches!(self.kind(target), TyKind::Ref(_, _, inner) if matches!(self.kind(inner), TyKind::Dyn(..))) {
                    self.coerce_expr(*expr, t, target);
                    return target;
                }
                let enum_cast = match self.tys.local_adt(self.resolve(t)) {
                    Some(a) => p.adt(a).is_enum && p.adt(a).variants.iter().all(|v| v.shape == VariantShape::Unit),
                    None => false,
                };
                // A fn item casts to a fn pointer of the same signature,
                // and a fn pointer casts to itself. The item form goes
                // through the coercion path, which gives the inner
                // expression the pointer type for lowering.
                let fn_cast = match (self.kind(t), self.kind(target)) {
                    (TyKind::FnDef(..), TyKind::FnPtr(_)) if self.is_fn_item(t) => {
                        self.fn_item_ptr_unifies(t, target) && self.coerce_at(t, target, span, Some(*expr))
                    }
                    (TyKind::FnPtr(_), TyKind::FnPtr(_)) => match (self.callable_sig(t), self.callable_sig(target)) {
                        (Some((pa, ra)), Some((pb, rb))) => {
                            pa.len() == pb.len() && pa.iter().zip(&pb).all(|(&a, &b)| self.unify(a, b)) && self.unify(ra, rb)
                        }
                        _ => false,
                    },
                    _ => false,
                };
                // A reference-to-reference cast is a coercion cast in
                // rustc (`&[T; N] as &[T]`, `&mut T as &T`, `&Vec<T> as
                // &[T]`): it holds exactly when the coercion does. The
                // probe rolls back on failure so the cast error below
                // is the only diagnostic.
                let ref_cast = matches!((self.kind(t), self.kind(target)), (TyKind::Ref(..), TyKind::Ref(..))) && {
                    let snap = self.snapshot_vars();
                    let obl_len = self.obl_len();
                    let err_len = self.errs.len();
                    if self.coerce_at(t, target, span, Some(*expr)) {
                        true
                    } else {
                        self.rollback_vars(snap);
                        self.obl_truncate(obl_len);
                        self.errs.truncate(err_len);
                        false
                    }
                };
                // The `as` table rustc enforces (E0054, E0604, E0606): bool
                // and char never cast to a float, only `u8` casts to char,
                // nothing casts to bool, a fieldless enum casts only to an
                // integer. A same-kind cast (`bool as bool`) is fine.
                let ok = fn_cast
                    || ref_cast
                    || match (self.kind(t), self.kind(target)) {
                        // An integer of unknown type stays open: later uses decide it (default i32).
                        (k, TyKind::Int(_)) if k.is_int_infer() => true,
                        (k, TyKind::Float(_) | TyKind::Int(_)) if k.is_float_infer() => true,
                        (_, TyKind::Int(_)) if enum_cast => true,
                        (TyKind::Int(_) | TyKind::Bool | TyKind::Char, TyKind::Int(_)) => true,
                        (TyKind::Int(_) | TyKind::Float(_), TyKind::Float(_)) => true,
                        (TyKind::Float(_), TyKind::Int(_)) => true,
                        (TyKind::Int(IntTy::U8) | TyKind::Char, TyKind::Char) => true,
                        (TyKind::Bool, TyKind::Bool) => true,
                        (TyKind::Error, _) | (_, TyKind::Error) => true,
                        _ => false,
                    };
                if !ok {
                    let (a, b) = (self.tn(t), self.tn(target));
                    self.err(
                        "L0116",
                        span,
                        format!("cannot cast `{a}` as `{b}`"),
                        "Lust allows `as` between integers, from bool and char to integers, and from u8 to char.",
                    );
                }
                target
            }
            Expr::Ref { mutable, expr, .. } => {
                let inner_expected = expected.and_then(|t| match self.kind(t) {
                    TyKind::Ref(_, _, inner) => Some(inner),
                    _ => None,
                });
                let t = self.expr(*expr, inner_expected);
                self.check_packed_borrow(*expr, span);
                self.tys.mk_ref(*mutable, t)
            }
            Expr::Deref(inner) => {
                let t = self.expr(*inner, None);
                // ARCH 2.12 run point: a deref must know the pointee source type.
                self.run_obligations(false);
                let t = self.resolve(t);
                match self.kind(t) {
                    TyKind::Ref(_, _, x) => x,
                    TyKind::Error => ERROR,
                    _ if self.tys.smart_elem(t).is_some() => self.tys.smart_elem(t).unwrap_or(ERROR),
                    // `*w` through a user `Deref` impl.
                    _ if let Some(target) = self.record_place_deref(e, t, 0, span) => target,
                    _ => {
                        let tn = self.tn(t);
                        self.err(
                            "L0113",
                            span,
                            format!("type `{tn}` cannot be dereferenced"),
                            "Only references, `Box` values, and `Rc` values can be dereferenced with `*`.",
                        );
                        ERROR
                    }
                }
            }
            Expr::Assign { lhs, rhs } => {
                if self.assign_lhs_needs_expected(*lhs) {
                    // A target with a struct form or a `..` rest gets
                    // its element types from the right-hand side, as a
                    // pattern gets them from its scrutinee.
                    let rt = self.expr(*rhs, None);
                    self.assign_lhs_expected(*lhs, rt);
                    self.place_check(*lhs, true);
                    return UNIT;
                }
                let lt = self.assign_lhs_ty(*lhs);
                self.place_check(*lhs, true);
                self.expect_expr(*rhs, lt);
                UNIT
            }
            Expr::AssignOp { op, lhs, rhs } => {
                let lt = self.expr(*lhs, None);
                self.place_check(*lhs, false);
                let rt = self.expr(*rhs, Some(lt));
                let lk = self.kind(lt);
                if self.tys.is_string_ty(self.resolve(lt)) && *op == BinOp::Add {
                    self.coerce_expr(*rhs, rt, REF_STR);
                    self.set_res(e, Res::Bin { ld: 0, rd: 0 });
                    return UNIT;
                }
                let (rd, rinner) = self.peel_one_ref(rt);
                // `x += &y` is fine, but Rust has no compound assignment with a `&mut` operand.
                let rmut = matches!(self.kind(rt), TyKind::Ref(_, Mut::Mut, _));
                let int_like = |k: TyKind| matches!(k, TyKind::Int(_)) || k.is_int_infer();
                let ok = !rmut
                    && match (*op, lk) {
                        (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem, TyKind::Float(_)) => self.unify(lt, rinner),
                        (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem, k) if k.is_float_infer() => self.unify(lt, rinner),
                        (_, TyKind::Error) => true,
                        (BinOp::Shl | BinOp::Shr, k) if int_like(k) => int_like(self.kind(rinner)),
                        (_, k) if int_like(k) => self.unify(lt, rinner),
                        (BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor, TyKind::Bool) => self.unify(lt, rinner),
                        _ => false,
                    };
                if !ok {
                    // Through the assignment trait, like the binary
                    // operators: a bound proves it in a template, the
                    // unique impl answers in an instance.
                    // The right side as written (no peeled reference):
                    // `a += &b` needs `impl AddAssign<&B> for A`.
                    if !rmut && self.trait_assign_op(e, *op, lt, rt, 0, span) {
                        return UNIT;
                    }
                    let (a, b) = (self.tn(lt), self.tn(rt));
                    self.err(
                        "L0113",
                        span,
                        format!("cannot apply `{}=` to `{a}` and `{b}`", op.symbol()),
                        "Both sides must be the same integer type.",
                    );
                }
                self.set_res(e, Res::Bin { ld: 0, rd });
                UNIT
            }
            Expr::StructLit { path, fields, update } => self.struct_lit(e, path, fields, *update, span, expected),
            Expr::Range { lo: Some(lo), hi: Some(hi), inclusive } => self.range_value(e, *lo, *hi, *inclusive, span),
            Expr::Range { .. } => {
                self.errs.push(unsupported(span, "ranges outside `for` loops"));
                ERROR
            }
            Expr::Break { label, value: val } => {
                // Edition 2024 (rustc E0695): an unlabeled break may not
                // target or pass through a labeled block. If the innermost
                // breakable is a labeled block, the break needs the label.
                if label.is_none()
                    && let Some(lp) = self.loops.last()
                    && lp.is_block
                {
                    self.err(
                        "L0120",
                        span,
                        "unlabeled `break` inside of a labeled block",
                        "Give the break the block's label, such as `break 'a;`.",
                    );
                    if let Some(v) = val {
                        self.expr(*v, None);
                    }
                    return NEVER;
                }
                let target = match label {
                    None => self.loops.len().checked_sub(1),
                    Some(l) => self
                        .loops
                        .iter()
                        .rposition(|lp| lp.label.is_some_and(|(n, bs)| n == l.name && crate::diag::ctxt_can_see_local(l.span.ctxt, bs))),
                };
                let Some(ti) = target else {
                    match label {
                        Some(l) => {
                            let n = self.name(l.name).to_string();
                            self.err("L0120", span, format!("cannot find label `'{n}` in this scope"), "Check the label name.");
                        }
                        None => self.err("L0120", span, "`break` outside of a loop", "Remove the break, or put it inside a loop."),
                    }
                    if let Some(v) = val {
                        self.expr(*v, None);
                    }
                    return NEVER;
                };
                let is_loop = self.loops[ti].is_loop;
                let prev = self.loops[ti].break_ty;
                match val {
                    Some(v) if !is_loop => {
                        self.expr(*v, None);
                        self.err(
                            "L0120",
                            span,
                            "`break` with a value is only allowed in `loop` and labeled blocks",
                            "Remove the value, or use `loop`.",
                        );
                    }
                    Some(v) => {
                        let t = self.expr(*v, prev);
                        match prev {
                            Some(pt) => {
                                self.coerce_expr(*v, t, pt);
                            }
                            None => self.loops[ti].break_ty = Some(t),
                        }
                    }
                    None if is_loop => match prev {
                        Some(pt) => {
                            self.coerce_at(UNIT, pt, span, None);
                        }
                        None => self.loops[ti].break_ty = Some(UNIT),
                    },
                    None => {}
                }
                NEVER
            }
            Expr::Continue(label) => {
                // Edition 2024 (rustc E0695), as for `break` above: an
                // unlabeled continue may not pass through a labeled block.
                if label.is_none()
                    && let Some(lp) = self.loops.last()
                    && lp.is_block
                {
                    self.err(
                        "L0120",
                        span,
                        "unlabeled `continue` inside of a labeled block",
                        "Give the continue the loop's label, such as `continue 'a;`, or move it out of the labeled block.",
                    );
                    return NEVER;
                }
                let found = match label {
                    None => self.loops.iter().rposition(|lp| !lp.is_block),
                    Some(l) => self
                        .loops
                        .iter()
                        .rposition(|lp| lp.label.is_some_and(|(n, bs)| n == l.name && crate::diag::ctxt_can_see_local(l.span.ctxt, bs))),
                };
                match found {
                    None => match label {
                        Some(l) => {
                            let n = self.name(l.name).to_string();
                            self.err("L0120", span, format!("cannot find label `'{n}` in this scope"), "Check the label name.");
                        }
                        None => self.err("L0120", span, "`continue` outside of a loop", "Remove the continue, or put it inside a loop."),
                    },
                    Some(ti) if self.loops[ti].is_block => {
                        self.err("L0120", span, "`continue` cannot target a labeled block", "`continue` needs a loop label.");
                    }
                    Some(_) => {}
                }
                NEVER
            }
            Expr::Return(val) => {
                let ret = self.closure_rets.last().copied().unwrap_or(self.fn_ret);
                match val {
                    Some(v) => {
                        self.expect_expr(*v, ret);
                    }
                    None => {
                        self.coerce_at(UNIT, ret, span, None);
                    }
                }
                NEVER
            }
            Expr::LabeledBlock { label, body } => {
                self.loops.push(LoopCtx { break_ty: None, is_loop: true, is_block: true, label: Some((label.name, label.span)) });
                let t = self.block(*body, expected);
                let l = self.loops.pop().unwrap();
                match l.break_ty {
                    Some(bt) => self.join(bt, t, None, span),
                    None => t,
                }
            }
            Expr::Macro { kind, args, fmt, repeat } => self.macro_expr(e, *kind, args, fmt, *repeat, span, expected),
            Expr::Tuple(elems) => {
                let exp: Option<Vec<Ty>> = expected.and_then(|t| match self.kind(t) {
                    TyKind::Tuple(ts) if self.tys.tys_of(ts).len() == elems.len() => Some(self.tys.tys_of(ts).to_vec()),
                    _ => None,
                });
                let mut out = Vec::with_capacity(elems.len());
                for (i, &el) in elems.iter().enumerate() {
                    let want = exp.as_ref().map(|v| v[i]);
                    // A `&dyn` element is a coercion site, as in rustc's
                    // tuple check under a tuple expectation.
                    if let Some(w) = self.dyn_ref_expectation(want) {
                        self.expect_expr(el, w);
                        out.push(w);
                    } else {
                        out.push(self.expr(el, want));
                    }
                }
                let ts = self.tys.intern_tys(&out);
                self.tys.intern(TyKind::Tuple(ts))
            }
            Expr::Array(elems) => {
                let exp_elem = expected.and_then(|t| match self.kind(t) {
                    TyKind::Array(el, _) => Some(el),
                    _ => None,
                });
                let elem = match (exp_elem, elems.first()) {
                    (Some(el), _) => {
                        for &el_e in elems {
                            self.expect_expr(el_e, el);
                        }
                        el
                    }
                    (None, Some(&first)) => {
                        let el = self.expr(first, None);
                        // An array of plain fn items holds function
                        // pointers: retag the first element too when any
                        // element is a different fn item.
                        let elt = self.resolve(el);
                        // Closures that capture nothing join as a fn
                        // pointer when they differ (rustc's LUB coercion).
                        if elems.len() > 1 && matches!(self.kind(elt), TyKind::Closure(_, caps) if self.tys.args(caps).is_empty()) {
                            let mut joined = elt;
                            for &el_e in &elems[1..] {
                                let t = self.expr(el_e, None);
                                joined = match self.closure_lub(joined, t) {
                                    Some(fp) => fp,
                                    None => {
                                        if !self.unify(joined, t) {
                                            let sp = self.span(el_e);
                                            self.mismatch(sp, joined, t);
                                        }
                                        joined
                                    }
                                };
                            }
                            if matches!(self.kind(joined), TyKind::FnPtr(_)) {
                                for &el_e in elems.iter() {
                                    self.set(el_e, joined);
                                }
                            }
                            let c = self.tys.intern_const(ConstKind::Int(elems.len() as u128));
                            return self.tys.intern(TyKind::Array(joined, c));
                        }
                        // Fn items join as a fn pointer only when they
                        // differ (`[a, b]`); `[a, a]` keeps the item type,
                        // which is zero-sized (rustc's LUB coercion).
                        if elems.len() > 1 && self.is_fn_item(elt) {
                            let rest: Vec<Ty> = elems[1..].iter().map(|&el_e| self.expr(el_e, None)).collect();
                            if rest.iter().all(|&t| self.same_fn_item(elt, t)) {
                                let c = self.tys.intern_const(ConstKind::Int(elems.len() as u128));
                                return self.tys.intern(TyKind::Array(elt, c));
                            }
                            let Some((params, ret)) = self.callable_sig(elt) else {
                                let c = self.tys.intern_const(ConstKind::Int(elems.len() as u128));
                                return self.tys.intern(TyKind::Array(ERROR, c));
                            };
                            let fp = self.fn_ptr_ty(&params, ret);
                            self.set(first, fp);
                            for (&el_e, &t) in elems[1..].iter().zip(&rest) {
                                self.coerce_expr(el_e, t, fp);
                            }
                            let c = self.tys.intern_const(ConstKind::Int(elems.len() as u128));
                            return self.tys.intern(TyKind::Array(fp, c));
                        }
                        let mut el = el;
                        for (i, &el_e) in elems.iter().enumerate().skip(1) {
                            let t = self.expr(el_e, Some(el));
                            if self.lub_flip(&elems[..i], el, t) {
                                el = t;
                            } else {
                                self.coerce_expr(el_e, t, el);
                            }
                        }
                        el
                    }
                    (None, None) => self.new_var(false),
                };
                let c = self.tys.intern_const(ConstKind::Int(elems.len() as u128));
                self.tys.intern(TyKind::Array(elem, c))
            }
            Expr::ArrayRepeat { value, len } => {
                let exp_elem = expected.and_then(|t| match self.kind(t) {
                    TyKind::Array(el, _) => Some(el),
                    _ => None,
                });
                let elem = self.expr(*value, exp_elem);
                let errs_before = self.errs.len();
                self.expect_expr(*len, USIZE);
                // A const param length (`[x; N]`): symbolic in the template
                // check, the instance's value in an instance. The element
                // must be Copy or a const, as for any length above 1.
                if let Expr::Path(segs) = p.ast.expr(*len)
                    && segs.len() == 1
                    && self.lookup(segs[0].name, span.ctxt).is_none()
                    && let Some((i, _, val)) = self.const_param(segs[0].name)
                {
                    let c = self.tys.intern_const(val.unwrap_or(ConstKind::Param(i)));
                    let n = match val {
                        Some(ConstKind::Int(n)) => n,
                        _ => 2,
                    };
                    let const_val = self.out.const_exprs[self.ei(*value)].is_some();
                    if n > 1 && !const_val && !is_copy(p, &self.tys, self.resolve(elem)) {
                        self.err(
                            "L0110",
                            span,
                            "the trait `Copy` is not implemented for this type",
                            "Array repeat with a length above 1 needs a Copy element, or write the elements out.",
                        );
                    }
                    return self.tys.intern(TyKind::Array(elem, c));
                }
                // The scalar subset first; then the full bounded
                // evaluator, so size_of calls, const items, and const
                // fn calls all give lengths in expression position.
                let n = crate::check::collect::eval_array_len(p.ast, p.interner, p.known, *len).or_else(|| {
                    if self.errs.len() != errs_before {
                        return None;
                    }
                    let mut ccx = CheckCx { cx: self };
                    match crate::ty::consteval::eval(&mut ccx, *len, Some(USIZE)) {
                        Ok((crate::ty::consteval::ConstValue::Int(n), _)) if n >= 0 => Some(n as u128),
                        _ => None,
                    }
                });
                match n {
                    Some(n) => {
                        let const_val = self.out.const_exprs[self.ei(*value)].is_some();
                        if n > 1 && !const_val && !is_copy(p, &self.tys, self.resolve(elem)) {
                            self.err(
                                "L0110",
                                span,
                                "the trait `Copy` is not implemented for this type",
                                "Array repeat with a length above 1 needs a Copy element, or write the elements out.",
                            );
                        }
                        let c = self.tys.intern_const(ConstKind::Int(n));
                        self.tys.intern(TyKind::Array(elem, c))
                    }
                    None => {
                        self.err(
                            "L0110",
                            span,
                            "array repeat length must be a constant integer",
                            "Write a literal length such as `[0; 4]`.",
                        );
                        ERROR
                    }
                }
            }
            Expr::TupleField { base, index } => {
                let bt = self.expr(*base, None);
                self.run_obligations(false);
                let (derefs, inner) = self.autoderef_smart(bt);
                let field_ty = match self.kind(inner) {
                    TyKind::Tuple(ts) => self.tys.tys_of(ts).get(*index as usize).copied(),
                    _ => match self.tys.local_adt(inner) {
                        Some(a) if !p.adt(a).is_enum && p.adt(a).variants[0].shape == VariantShape::Tuple => {
                            // As for named fields: a generic Adt's field is
                            // the template's, substituted with these args.
                            p.adt(a).variants[0].fields.get(*index as usize).map(|f| match self.tys.adt_parts(inner) {
                                Some((_, args)) if args != EMPTY_ARGS && self.tys.flags(f.ty).contains_param() => {
                                    let gargs: Vec<GenericArg> = self.tys.args(args).to_vec();
                                    self.subst_norm(f.ty, &gargs, span)
                                }
                                _ => f.ty,
                            })
                        }
                        _ => None,
                    },
                };
                match field_ty {
                    Some(t) => {
                        if let Some(a) = self.tys.local_adt(inner) {
                            self.check_tuple_field_vis(a, *index, span);
                        }
                        self.set_res(e, Res::Field { derefs, index: *index });
                        t
                    }
                    None => {
                        if !matches!(self.kind(inner), TyKind::Error) {
                            let tn = self.tn(bt);
                            self.err("L0103", span, format!("no field `{index}` on type `{tn}`"), "Check the field index.");
                        }
                        ERROR
                    }
                }
            }
            Expr::ConstBlock(b) => {
                let b = *b;
                let mut ccx = CheckCx { cx: self };
                match crate::ty::consteval::eval(&mut ccx, e, expected) {
                    Ok((v, t)) => {
                        let i = ccx.cx.ei(e);
                        ccx.cx.out.const_exprs[i] = Some(v);
                        t
                    }
                    // A generic inline const (ARCH 2.13): a layout over the
                    // template's params has no value here, so the template
                    // check checks the block in generic form and each
                    // instance evaluates it with its own types (a failing
                    // assert is then a build error, as rustc's post-mono
                    // error is).
                    Err(d) if d.code == "L0652" && ccx.cx.is_template_check() => self.block(b, expected),
                    Err(d) => {
                        ccx.cx.errs.push(d);
                        ERROR
                    }
                }
            }
            Expr::Let { .. } => {
                self.errs.push(not_yet("L0820", span, "`let` outside an `if` or `while` condition chain"));
                ERROR
            }
            Expr::OffsetOf { ty, fields } => {
                let t = self.resolve_written(*ty);
                let mut cur = self.deep(t);
                // The offset is baked into this body as a constant; the
                // layout fingerprint hashes field types deeply, so one
                // read set over the root type covers the field walk.
                p.record_layout_reads(&mut self.out.reads, &self.tys, cur);
                let mut off: u64 = 0;
                let mut bad = false;
                for &ffield in fields {
                    let Some(a) = self.tys.local_adt(cur) else {
                        self.err("L0110", span, "`offset_of!` needs a struct type", "Use a struct with named fields.");
                        bad = true;
                        break;
                    };
                    if !matches!(
                        p.adt(a).repr.kind,
                        crate::ty::layout::ReprKind::C | crate::ty::layout::ReprKind::Packed | crate::ty::layout::ReprKind::Transparent
                    ) {
                        self.err(
                            "L0650",
                            span,
                            "`offset_of!` on a default-repr type is not supported",
                            "Add `#[repr(C)]` to the type, or measure with `size_of`.",
                        );
                        bad = true;
                        break;
                    }
                    let found = match ffield {
                        crate::ast::OffsetField::Name(fname) => p.adt(a).variants[0].fields.iter().position(|f| f.name == fname),
                        crate::ast::OffsetField::Index(idx) => {
                            if p.adt(a).variants[0].shape == VariantShape::Tuple && (idx as usize) < p.adt(a).variants[0].fields.len() {
                                Some(idx as usize)
                            } else {
                                None
                            }
                        }
                    };
                    let Some(i) = found else {
                        let shown = match ffield {
                            crate::ast::OffsetField::Name(fname) => self.name(fname).to_string(),
                            crate::ast::OffsetField::Index(idx) => idx.to_string(),
                        };
                        self.err("L0103", span, format!("no field `{shown}` for `offset_of!`"), "Check the field name.");
                        bad = true;
                        break;
                    };
                    match ffield {
                        crate::ast::OffsetField::Name(fname) => self.check_field_vis(a, fname, span),
                        crate::ast::OffsetField::Index(idx) => self.check_tuple_field_vis(a, idx, span),
                    }
                    match crate::ty::layout::layout_of_ty(&self.tys, &UserLayout(p), cur) {
                        Ok(l) => off += l.field_offsets.get(i).copied().unwrap_or(0),
                        Err(()) => {
                            self.err(
                                "L0652",
                                span,
                                "unsupported layout form in `offset_of!`",
                                "Use a type inside the supported layout grammar.",
                            );
                            bad = true;
                            break;
                        }
                    }
                    cur = p.adt(a).variants[0].fields[i].ty;
                }
                if bad {
                    ERROR
                } else {
                    self.set_res(e, Res::ConstUsize(off));
                    USIZE
                }
            }
            Expr::Closure { is_move, is_async: false, params, ret, body } => self.closure_expr(e, *is_move, params, *ret, *body, expected),
            Expr::Closure { .. } => {
                self.err("L0820", span, "async closures are not supported yet", "Use a plain closure.");
                ERROR
            }
            Expr::Try(inner) => self.try_expr(e, *inner, span),
            Expr::Underscore => {
                self.err(
                    "L0110",
                    span,
                    "in expressions, `_` can only be used on the left-hand side of an assignment",
                    "Remove the `_`, or use it as a discard target in an assignment.",
                );
                ERROR
            }
            Expr::QPath { self_ty, trait_path, segs } => self.qpath_value(e, *self_ty, trait_path, segs, span),
            // AST v2 expression forms the parser still rejects.
            Expr::Await(_) | Expr::AsyncBlock { .. } | Expr::UnsafeBlock(_) | Expr::MacroCall(_) => ERROR,
        }
    }

    /// The `?` operator. On `Option` the enclosing return type must
    /// be an `Option`; on `Result` it must be a `Result` whose error
    /// type matches, widens numerically, or converts through a
    /// `From` impl, selected here like `From::from` itself is in
    /// `assoc_call`. The conversion plan rides in `Res` for lowering.
    fn try_expr(&mut self, e: ExprId, inner: ExprId, span: Span) -> Ty {
        let p = self.p;
        let it0 = self.expr(inner, None);
        self.run_obligations(false);
        let it = self.resolve(it0);
        let ret = self.closure_rets.last().copied().unwrap_or(self.fn_ret);
        let ret = self.resolve(ret);
        let general_var = |cx: &Self, t: Ty| matches!(cx.tys.kind(t), TyKind::Infer(v) if !v.is_int() && !v.is_float());
        if let Some(elem) = self.tys.option_elem(it) {
            let ok = self.tys.option_elem(ret).is_some()
                || (general_var(self, ret) && {
                    let v = self.new_var(false);
                    let o = self.tys.mk_option(v);
                    self.unify(ret, o)
                });
            if !ok && self.kind(it) != TyKind::Error && self.kind(ret) != TyKind::Error {
                self.err(
                    "L0112",
                    span,
                    "the `?` operator on an `Option` can only be used in a function that returns `Option`",
                    "Change the return type to `Option<_>`, or handle the `None` case with `match`.",
                );
            }
            self.set_res(e, Res::TryPlain);
            return elem;
        }
        if let Some((ok_t, err_t)) = self.tys.result_args(it) {
            let ret_err = match self.tys.result_args(ret) {
                Some((_, e2)) => Some(e2),
                None if general_var(self, ret) => {
                    let o = self.new_var(false);
                    let r = self.tys.mk_result(o, err_t);
                    if self.unify(ret, r) { Some(err_t) } else { None }
                }
                None => None,
            };
            let Some(ret_err) = ret_err else {
                if self.kind(it) != TyKind::Error && self.kind(ret) != TyKind::Error {
                    self.err(
                        "L0112",
                        span,
                        "the `?` operator on a `Result` can only be used in a function that returns `Result`",
                        "Change the return type to `Result<_, _>`, or handle the `Err` case with `match`.",
                    );
                }
                self.set_res(e, Res::TryPlain);
                return ok_t;
            };
            // The common case: the error types already agree.
            let snap = self.snapshot_vars();
            if self.unify(err_t, ret_err) {
                self.set_res(e, Res::TryPlain);
                return ok_t;
            }
            self.rollback_vars(snap);
            let (e1, e2) = (self.resolve(err_t), self.resolve(ret_err));
            if Self::numeric_from_ok(self.kind(e1), self.kind(e2)) {
                self.set_res(e, Res::TryCast);
                return ok_t;
            }
            // The builtin `From<&str>` and `From<&String>` for
            // String: a copy, with no impl record behind it.
            if e2 == STRING && matches!(self.kind(e1), TyKind::Ref(_, _, i) if i == STR || i == STRING) {
                self.set_res(e, Res::TryStringFrom);
                return ok_t;
            }
            let args_id = self.tys.intern_args(&[GenericArg::Ty(e2), GenericArg::Ty(e1)]);
            let tr = TraitRef { def: p.gx.lang.from, args: args_id, bindings: EMPTY_BINDINGS };
            // The obligation is what makes a generic body without the
            // `From` bound fail at finish; selection here only picks
            // the call target for lowering.
            self.obl.push_trait_at(tr, span, 0);
            let sel = self.select_obligation_at(tr, span, 0);
            let from_fn = match &sel {
                Selection::Impl { id, args: impl_args, .. } => {
                    self.method_instance_for_impl(e, *id, tr, impl_args.clone(), "from", span).map(|(local, _, _)| local)
                }
                _ => None,
            };
            match (sel, from_fn) {
                (_, Some(local)) => self.set_res(e, Res::TryFrom(local)),
                // The MAX marker is a template-only plan: an instance
                // check re-selects and fills in the real target. In a
                // concrete body it would lower as a plain move of the
                // wrong type, so it must not escape a template check.
                (Selection::Impl { .. } | Selection::ParamEvidence(_), None) if self.is_template_check() => {
                    self.set_res(e, Res::TryFrom(LocalDefId(u32::MAX)))
                }
                _ => {
                    let (a, b) = (self.tn(e1), self.tn(e2));
                    self.err(
                        "L0112",
                        span,
                        format!("the `?` operator cannot convert the error type `{a}` to `{b}`"),
                        format!("Implement `From<{a}>` for `{b}`, or map the error before the `?`."),
                    );
                    self.set_res(e, Res::TryPlain);
                }
            }
            return ok_t;
        }
        if self.kind(it) != TyKind::Error {
            let tn = self.tn(it);
            self.err(
                "L0112",
                span,
                format!("the `?` operator can only be used on `Option` or `Result` values, not `{tn}`"),
                "Remove the `?`, or produce an `Option` or `Result` first.",
            );
        }
        self.set_res(e, Res::TryPlain);
        ERROR
    }

    fn unit_body(&mut self, t: Ty, b: ast::BlockId) {
        let block = self.p.ast.block(b);
        if let Some(tail) = block.tail {
            self.coerce_expr(tail, t, UNIT);
        }
    }

    /// The expected type when it is a pointer to a dyn type: a
    /// reference, or an owning `Box<dyn Tr>` or `Rc<dyn Tr>`. Branch
    /// results then coerce to it one by one, as rustc's expectation
    /// does, instead of joining the branch types first (ARCH 2.8).
    fn dyn_ref_expectation(&self, expected: Option<Ty>) -> Option<Ty> {
        let t = self.resolve(expected?);
        match self.kind(t) {
            TyKind::Ref(_, _, inner) if matches!(self.kind(inner), TyKind::Dyn(..)) => Some(t),
            TyKind::Adt(..) if self.tys.smart_elem(t).is_some_and(|e| matches!(self.kind(self.resolve(e)), TyKind::Dyn(..))) => Some(t),
            _ => None,
        }
    }

    /// Coerces a block's result to `to` at its tail expression.
    fn coerce_block_tail(&mut self, b: ast::BlockId, t: Ty, to: Ty) {
        let block = self.p.ast.block(b);
        match block.tail {
            Some(tail) => {
                self.coerce_expr(tail, t, to);
            }
            None => {
                self.coerce_at(t, to, block.span, None);
            }
        }
    }

    /// rustc's LUB fallback (CoerceMany): when the new site's type `new`
    /// cannot coerce to `prev`, the type of the earlier sites, but `prev`
    /// coerces to `new` (`[&&d, &d]`, or `match n { 0 => &[], _ => v }`
    /// with `v: &[u8]`), and no earlier site carries a coercion yet, the
    /// earlier sites coerce to `new`. True when it applied them; the
    /// caller then takes `new` as the joined type. The tests are pure,
    /// so a false answer leaves the usual coercion (and its error).
    fn lub_flip(&mut self, prev: &[ExprId], prev_ty: Ty, new: Ty) -> bool {
        if prev.is_empty() || self.kind(prev_ty) == TyKind::Never || self.kind(new) == TyKind::Never {
            return false;
        }
        if self.pure_coercible(new, prev_ty) || !self.pure_coercible(prev_ty, new) {
            return false;
        }
        if prev.iter().any(|&s| self.out.coerce[self.ei(s)] != Coerce::None) {
            return false;
        }
        for &s in prev {
            let t = self.out.expr_ty[self.ei(s)];
            if self.kind(t) != TyKind::Never {
                self.coerce_expr(s, t, new);
            }
        }
        true
    }

    /// True when `coerce_at` may take `f` to `e`: the types match up to
    /// inference variables, or a reference coercion applies (slice and
    /// `str` unsizing, `&mut` to `&`, deref of extra reference layers),
    /// or `e` is a dyn reference (an unsizing site). Pure.
    fn pure_coercible(&self, f: Ty, e: Ty) -> bool {
        if self.ty_matchish(f, e) || self.ref_coercible(f, e) {
            return true;
        }
        let (TyKind::Ref(..), TyKind::Ref(_, em, y)) = (self.kind(f), self.kind(e)) else { return false };
        if matches!(self.kind(y), TyKind::Dyn(..)) {
            return true;
        }
        let mut t = f;
        while let TyKind::Ref(_, _, inner) = self.kind(t)
            && matches!(self.kind(inner), TyKind::Ref(..))
        {
            t = inner;
            if !em.is_mut() && self.ty_matchish(t, e) {
                return true;
            }
        }
        false
    }

    /// Joins the types of two branches. A diverging branch takes the other branch's type.
    fn join(&mut self, a: Ty, b: Ty, be: Option<ExprId>, span: Span) -> Ty {
        if self.kind(a) == TyKind::Never {
            return b;
        }
        if self.kind(b) == TyKind::Never {
            return a;
        }
        // Two closures that capture nothing (or one and a fn pointer)
        // with one signature join as a function pointer, as rustc's LUB
        // coercion does; lowering makes each a trampoline value.
        if let Some(fp) = self.closure_lub(a, b) {
            return fp;
        }
        if self.same_fn_item(a, b) {
            return a;
        }
        // Two plain fn items (or an item and a pointer) with one
        // signature join as a function pointer.
        if self.is_fn_item(a) || self.is_fn_item(b) || matches!(self.kind(a), TyKind::FnPtr(_)) {
            if let (Some(sa), Some(sb)) = (self.callable_sig(a), self.callable_sig(b))
                && sa == sb
            {
                let fp = self.fn_ptr_ty(&sa.0, sa.1);
                if let Some(be) = be {
                    self.coerce_expr(be, b, fp);
                }
                return fp;
            }
        }
        if let Some(be) = be {
            if self.coerce_expr(be, b, a) {
                return a;
            }
            return ERROR;
        }
        if !self.unify(a, b) {
            self.mismatch(span, a, b);
            return ERROR;
        }
        a
    }

    /// Requires an assignable place expression on the left of `=`.
    /// A reference to a packed field could be unaligned (ARCH 4.4): any borrow
    /// of a field place whose base is a packed Adt, explicit or implicit
    /// (method autoref, format arguments), is an error at the borrow, unless
    /// the field type has alignment 1, when every address is aligned for it
    /// and Rust allows the reference.
    fn check_packed_borrow(&mut self, place_e: ExprId, span: Span) {
        let base = match self.p.ast.expr(place_e) {
            Expr::Field { base, .. } | Expr::TupleField { base, .. } => *base,
            _ => return,
        };
        let bt = self.out.expr_ty[self.ei(base)];
        let (_, inner) = self.autoderef(bt);
        if let Some(a) = self.tys.local_adt(inner)
            && self.p.adt(a).repr.kind == crate::ty::layout::ReprKind::Packed
        {
            let ft = self.deep(self.out.expr_ty[self.ei(place_e)]);
            if crate::ty::layout::layout_of_ty(&self.tys, self.p, ft).is_ok_and(|l| l.align <= 1) {
                return;
            }
            self.err("L0651", span, "reference to a packed field is not allowed", "Copy the field value into a local first.");
        }
    }

    /// Assignment into a static is never a plain place write here: an
    /// immutable static cannot be assigned, and a mutable one needs `unsafe`.
    fn static_root(&self, e: ExprId) -> Option<u32> {
        match self.p.ast.expr(e) {
            Expr::Path(_) => match self.out.expr_res[self.ei(e)] {
                Res::Static(idx) => Some(idx),
                _ => None,
            },
            Expr::Field { base, .. } | Expr::TupleField { base, .. } | Expr::Index { base, .. } => self.static_root(*base),
            _ => None,
        }
    }

    /// The type of an assignment target. Tuple and array targets are
    /// destructuring assignment: their elements are targets in turn,
    /// and `_` discards its element with a fresh type variable. Every
    /// other target checks as the place expression it is.
    fn assign_lhs_ty(&mut self, e: ExprId) -> Ty {
        match self.p.ast.expr(e) {
            Expr::Underscore => {
                let t = self.new_var(false);
                self.set(e, t)
            }
            Expr::Tuple(elems) => {
                let ts: Vec<Ty> = elems.iter().map(|&el| self.assign_lhs_ty(el)).collect();
                let id = self.tys.intern_tys(&ts);
                let t = self.tys.intern(TyKind::Tuple(id));
                self.set(e, t)
            }
            Expr::Array(elems) => {
                let mut elem_ty = None;
                for &el in elems {
                    let et = self.assign_lhs_ty(el);
                    match elem_ty {
                        None => elem_ty = Some(et),
                        Some(prev) => {
                            if !self.unify(prev, et) {
                                let s = self.span(el);
                                self.mismatch(s, prev, et);
                            }
                        }
                    }
                }
                let elem = elem_ty.unwrap_or_else(|| self.new_var(false));
                let c = self.tys.intern_const(ConstKind::Int(elems.len() as u128));
                let t = self.tys.intern(TyKind::Array(elem, c));
                self.set(e, t)
            }
            _ => self.expr(e, None),
        }
    }

    /// True for a bare `..` element of an assignment target. The
    /// parser reads it as an open range expression.
    fn is_rest_elem(&self, e: ExprId) -> bool {
        matches!(self.p.ast.expr(e), Expr::Range { lo: None, hi: None, inclusive: false })
    }

    /// True when an assignment target contains a struct form or a
    /// `..` rest, so its element types must come from the right-hand
    /// side type (see `assign_lhs_expected`). Plain tuple and array
    /// targets build their type from their places instead, which
    /// lets the right-hand side infer against them.
    fn assign_lhs_needs_expected(&self, e: ExprId) -> bool {
        match self.p.ast.expr(e) {
            Expr::StructLit { .. } | Expr::Call { .. } => true,
            Expr::Tuple(elems) | Expr::Array(elems) => {
                elems.iter().any(|&el| self.is_rest_elem(el) || self.assign_lhs_needs_expected(el))
            }
            _ => false,
        }
    }

    /// Maps target elements to source indices around a `..` rest,
    /// like `map_tuple_elems` for patterns. None when the counts do
    /// not fit a source of `n` elements.
    fn map_assign_elems(&self, elems: &[ExprId], n: usize) -> Option<Vec<(usize, ExprId)>> {
        match elems.iter().position(|&e| self.is_rest_elem(e)) {
            None => {
                if elems.len() != n {
                    return None;
                }
                Some(elems.iter().enumerate().map(|(i, &e)| (i, e)).collect())
            }
            Some(r) => {
                if elems[r + 1..].iter().any(|&e| self.is_rest_elem(e)) {
                    return None;
                }
                let suffix = elems.len() - r - 1;
                if r + suffix > n {
                    return None;
                }
                let mut out: Vec<(usize, ExprId)> = elems[..r].iter().enumerate().map(|(i, &e)| (i, e)).collect();
                for (j, &e) in elems[r + 1..].iter().enumerate() {
                    out.push((n - suffix + j, e));
                }
                Some(out)
            }
        }
    }

    /// Resolves the struct or variant an assignment target names and
    /// unifies it with the right-hand side type, as a pattern does
    /// with its scrutinee. Answers the Adt, the variant, and the
    /// scrutinee's generic arguments for field substitution. An enum
    /// variant of a multi-variant enum can fail to match, so it is
    /// an error here (rustc E0005) but still resolves.
    fn assign_variant(&mut self, segs: &[ast::PathSeg], want: Ty, span: Span) -> Option<(AdtId, u32, Vec<GenericArg>)> {
        let p = self.p;
        let target = if segs.len() == 1 {
            let n = segs[0].name;
            if n != p.known.self_type {
                self.binding(Namespace::Type, n);
            }
            let a = if n == p.known.self_type { self.self_adt() } else { p.type_names.get(&n).copied() };
            match a.filter(|&a| !p.adt(a).is_enum).map(|a| (a, 0)) {
                Some(v) => Some(v),
                None => match self.pat_ident(n) {
                    PatIdent::Variant(a, v) => Some((a, v)),
                    _ => None,
                },
            }
        } else {
            match self.resolve_assoc(segs, span) {
                Some(Res::Variant(a, v)) => Some((a, v)),
                Some(_) => {
                    self.err("L0110", span, "expected a variant or struct in this pattern", "Use `Type::Variant`.");
                    None
                }
                None => return None,
            }
        };
        let Some((a, v)) = target else {
            let last = segs.last().map(|s| s.name);
            if last == Some(p.known.Some) || last == Some(p.known.Ok) || last == Some(p.known.Err) {
                self.err("L0110", span, "refutable pattern in assignment", "Use `if let` or `match` for a pattern that can fail.");
            } else {
                self.err("L0102", span, "unknown struct or variant in pattern", "Check the name.");
            }
            return None;
        };
        // A path through `Self` names the impl's own type.
        if let Some(args) = self.self_path_args(a, segs, span)
            && !args.is_empty()
        {
            let st = self.tys.mk_adt(p.def_of_adt(a), &args);
            if !self.unify(st, want) {
                self.mismatch(span, want, st);
                return None;
            }
        }
        let dt = self.deep(want);
        let scrut_args: Vec<GenericArg> = match self.tys.adt_parts(dt) {
            Some((d, aa)) if d == p.def_of_adt(a) => self.tys.args(aa).to_vec(),
            _ => Vec::new(),
        };
        let (a, adt_ty) = match self.tys.local_adt(dt) {
            Some(inst) if inst != a && p.def_of_adt(inst) == p.def_of_adt(a) => (inst, dt),
            _ if !scrut_args.is_empty() => (a, dt),
            _ => (a, self.tys.adt_ty(a)),
        };
        if !self.unify(adt_ty, want) {
            self.mismatch(span, want, adt_ty);
            return None;
        }
        if p.adt(a).is_enum && p.adt(a).variants.len() != 1 {
            self.err("L0110", span, "refutable pattern in assignment", "Use `if let` or `match` for a pattern that can fail.");
        }
        Some((a, v, scrut_args))
    }

    /// Checks an assignment target against the right-hand side type,
    /// top down, as a pattern checks against its scrutinee type.
    /// Used for targets with a struct form or a `..` rest. Records
    /// the target type on every sub-target, which lowering reads for
    /// the element types of struct forms.
    fn assign_lhs_expected(&mut self, e: ExprId, want: Ty) {
        let p = self.p;
        let span = self.span(e);
        match p.ast.expr(e) {
            Expr::Underscore => {
                self.set(e, want);
            }
            Expr::Tuple(elems) => {
                self.set(e, want);
                match self.kind(want) {
                    TyKind::Tuple(ts) => {
                        let kt: Vec<Ty> = self.tys.tys_of(ts).to_vec();
                        match self.map_assign_elems(elems, kt.len()) {
                            Some(mapped) => {
                                for (i, sub) in mapped {
                                    self.assign_lhs_expected(sub, kt[i]);
                                }
                            }
                            None => {
                                self.err(
                                    "L0110",
                                    span,
                                    format!("this tuple has {} element(s)", kt.len()),
                                    "Match every element, use `_`, or skip the middle with `..`.",
                                );
                                for &sub in elems {
                                    if !self.is_rest_elem(sub) {
                                        self.assign_lhs_expected(sub, ERROR);
                                    }
                                }
                            }
                        }
                    }
                    TyKind::Error => {
                        for &sub in elems {
                            if !self.is_rest_elem(sub) {
                                self.assign_lhs_expected(sub, ERROR);
                            }
                        }
                    }
                    _ => {
                        let vars: Vec<Ty> = elems.iter().map(|_| self.new_var(false)).collect();
                        for (i, &sub) in elems.iter().enumerate() {
                            if !self.is_rest_elem(sub) {
                                self.assign_lhs_expected(sub, vars[i]);
                            }
                        }
                        let ts = self.tys.intern_tys(&vars);
                        let tt = self.tys.intern(TyKind::Tuple(ts));
                        if !self.unify(tt, want) {
                            self.mismatch(span, want, tt);
                        }
                    }
                }
            }
            Expr::Array(elems) => {
                self.set(e, want);
                let (elem, arr_len, is_slice) = match self.kind(want) {
                    TyKind::Array(el, c) => {
                        let n = match self.tys.const_kind(c) {
                            ConstKind::Int(n) => Some(n as usize),
                            _ => None,
                        };
                        (el, n, false)
                    }
                    TyKind::Slice(el) => (el, None, true),
                    TyKind::Error => {
                        for &sub in elems {
                            if !self.is_rest_elem(sub) {
                                self.assign_lhs_expected(sub, ERROR);
                            }
                        }
                        return;
                    }
                    _ => {
                        let tn = self.tn(want);
                        self.err(
                            "L0110",
                            span,
                            format!("slice pattern cannot match a value of type `{tn}`"),
                            "Match on an array or a slice, for example `&value[..]`.",
                        );
                        for &sub in elems {
                            if !self.is_rest_elem(sub) {
                                self.assign_lhs_expected(sub, ERROR);
                            }
                        }
                        return;
                    }
                };
                if is_slice {
                    // A slice can be too short, so this can fail.
                    self.err("L0110", span, "refutable pattern in assignment", "Use `if let` or `match` for a pattern that can fail.");
                    for &sub in elems {
                        if !self.is_rest_elem(sub) {
                            self.assign_lhs_expected(sub, elem);
                        }
                    }
                    return;
                }
                match arr_len {
                    Some(n) => match self.map_assign_elems(elems, n) {
                        Some(mapped) => {
                            for (_, sub) in mapped {
                                self.assign_lhs_expected(sub, elem);
                            }
                        }
                        None => {
                            let fixed = elems.iter().filter(|&&s| !self.is_rest_elem(s)).count();
                            self.err(
                                "L0110",
                                span,
                                format!("pattern requires {fixed} element(s) but the array has {n}"),
                                "Change the pattern length, or skip the middle with `..`.",
                            );
                            for &sub in elems {
                                if !self.is_rest_elem(sub) {
                                    self.assign_lhs_expected(sub, elem);
                                }
                            }
                        }
                    },
                    None => {
                        for &sub in elems {
                            if !self.is_rest_elem(sub) {
                                self.assign_lhs_expected(sub, elem);
                            }
                        }
                    }
                }
            }
            Expr::StructLit { path, fields, update } => {
                self.set(e, want);
                let rest = update.is_some_and(|u| self.is_rest_elem(u));
                if let Some(u) = update {
                    if rest {
                        self.set(*u, ERROR);
                    } else {
                        self.expr(*u, None);
                        self.err(
                            "L0121",
                            span,
                            "invalid left-hand side of assignment",
                            "Assign to a variable, a field, an index, or `*reference`.",
                        );
                    }
                }
                let Some((a, v, scrut_args)) = self.assign_variant(path, want, span) else {
                    for &(_, _, fe) in fields {
                        self.assign_lhs_expected(fe, ERROR);
                    }
                    return;
                };
                self.set_res(e, Res::Variant(a, v));
                let variant = &p.adt(a).variants[v as usize];
                if variant.shape != VariantShape::Named {
                    self.err("L0110", span, "this variant does not have named fields", "Use the tuple form.");
                    for &(_, _, fe) in fields {
                        self.assign_lhs_expected(fe, ERROR);
                    }
                    return;
                }
                let mut seen = vec![false; variant.fields.len()];
                for &(fname, fspan, fe) in fields {
                    match variant.fields.iter().position(|f| f.name == fname) {
                        Some(i) => {
                            if seen[i] {
                                self.err("L0106", fspan, format!("field `{}` is set twice", self.name(fname)), "Remove one of them.");
                            }
                            seen[i] = true;
                            self.check_field_vis(a, fname, fspan);
                            let ft = variant.fields[i].ty;
                            let ft = if scrut_args.is_empty() { ft } else { self.subst_norm(ft, &scrut_args, span) };
                            self.assign_lhs_expected(fe, ft);
                        }
                        None => {
                            self.assign_lhs_expected(fe, ERROR);
                            self.err("L0103", fspan, format!("no field `{}` in this variant", self.name(fname)), "Check the field name.");
                        }
                    }
                }
                if !rest && seen.iter().any(|s| !s) {
                    self.err("L0107", span, "pattern does not mention all fields", "Add the missing fields, or end the pattern with `..`.");
                }
            }
            Expr::Call { callee, args } => {
                self.set(e, want);
                let Expr::Path(segs) = p.ast.expr(*callee) else {
                    self.err(
                        "L0121",
                        span,
                        "invalid left-hand side of assignment",
                        "Assign to a variable, a field, an index, or `*reference`.",
                    );
                    for &arg in args {
                        if !self.is_rest_elem(arg) {
                            self.assign_lhs_expected(arg, ERROR);
                        }
                    }
                    return;
                };
                let segs = segs.clone();
                let Some((a, v, scrut_args)) = self.assign_variant(&segs, want, span) else {
                    for &arg in args {
                        if !self.is_rest_elem(arg) {
                            self.assign_lhs_expected(arg, ERROR);
                        }
                    }
                    return;
                };
                self.set_res(e, Res::Variant(a, v));
                self.set_res(*callee, Res::Variant(a, v));
                self.set(*callee, ERROR);
                let variant = &p.adt(a).variants[v as usize];
                if variant.shape != VariantShape::Tuple {
                    self.err(
                        "L0110",
                        span,
                        format!("this variant has {} field(s)", variant.fields.len()),
                        "Match every field, or use `_` for the ones you do not need.",
                    );
                    for &arg in args {
                        if !self.is_rest_elem(arg) {
                            self.assign_lhs_expected(arg, ERROR);
                        }
                    }
                    return;
                }
                if !p.adt(a).is_enum {
                    self.check_ctor_vis(a, span);
                }
                match self.map_assign_elems(args, variant.fields.len()) {
                    Some(mapped) => {
                        for (i, sub) in mapped {
                            let ft = variant.fields[i].ty;
                            let ft = if scrut_args.is_empty() { ft } else { self.subst_norm(ft, &scrut_args, span) };
                            self.assign_lhs_expected(sub, ft);
                        }
                    }
                    None => {
                        self.err(
                            "L0110",
                            span,
                            format!("this variant has {} field(s)", variant.fields.len()),
                            "Match every field, use `_`, or skip the middle with `..`.",
                        );
                        for &arg in args {
                            if !self.is_rest_elem(arg) {
                                self.assign_lhs_expected(arg, ERROR);
                            }
                        }
                    }
                }
            }
            _ => {
                let t = self.expr(e, None);
                if !self.unify(t, want) {
                    self.mismatch(span, want, t);
                }
            }
        }
    }

    fn place_check(&mut self, e: ExprId, destr: bool) {
        if let Some(idx) = self.static_root(e) {
            let s = self.span(e);
            if self.p.statics[idx as usize].mutable {
                self.err(
                    "L0404",
                    s,
                    "writing a mutable static requires `unsafe`, which is not supported",
                    "Make the static immutable, or use a local variable.",
                );
            } else {
                self.err("L0121", s, "cannot assign to an immutable static", "Statics are read-only; use a variable instead.");
            }
            return;
        }
        let ok = match self.p.ast.expr(e) {
            Expr::Path(segs) => {
                (segs.len() == 1 && matches!(self.out.expr_res[self.ei(e)], Res::Local(_)))
                    || (destr
                        && match self.out.expr_res[self.ei(e)] {
                            // A unit variant target (`U = make_u();`)
                            // writes nothing. A variant of a
                            // multi-variant enum can fail to match.
                            Res::Variant(a, v) => {
                                self.p.adt(a).variants[v as usize].shape == VariantShape::Unit
                                    && (!self.p.adt(a).is_enum || self.p.adt(a).variants.len() == 1)
                            }
                            _ => false,
                        })
            }
            Expr::Field { .. } | Expr::TupleField { .. } | Expr::Index { .. } | Expr::Deref(_) | Expr::SelfValue => true,
            Expr::Underscore => true,
            Expr::Unit => destr,
            Expr::Tuple(elems) | Expr::Array(elems) => {
                for &el in elems {
                    if !self.is_rest_elem(el) {
                        self.place_check(el, destr);
                    }
                }
                return;
            }
            Expr::StructLit { fields, .. } if destr => {
                for &(_, _, fe) in fields {
                    self.place_check(fe, destr);
                }
                return;
            }
            Expr::Call { args, .. } if destr && matches!(self.out.expr_res[self.ei(e)], Res::Variant(..)) => {
                for &arg in args {
                    if !self.is_rest_elem(arg) {
                        self.place_check(arg, destr);
                    }
                }
                return;
            }
            _ => false,
        };
        if !ok {
            let s = self.span(e);
            self.err("L0121", s, "invalid left-hand side of assignment", "Assign to a variable, a field, an index, or `*reference`.");
        }
    }

    /// Strips all references. Returns the count and the inner type.
    fn autoderef(&self, t: Ty) -> (u8, Ty) {
        let mut t = self.resolve(t);
        let mut n = 0;
        while let TyKind::Ref(_, _, inner) = self.tys.kind(t) {
            t = self.resolve(inner);
            n += 1;
        }
        (n, t)
    }

    /// Autoderef through references and `Box`: the chain field
    /// access, indexing, and method calls follow in Rust. The
    /// count is in the same units as `autoderef` (one `Deref`
    /// projection per step), so recorded resolutions lower
    /// uniformly.
    /// The (derefs, autoref) adjustment that takes a receiver
    /// of type `rt` to a typed receiver type `want` (`Box<Self>`,
    /// `&Rc<Self>`, kin), if one exists: peel references and
    /// smart pointers until the type is `want` itself (by
    /// value) or the pointee of the reference `want` asks for.
    fn typed_receiver_adjust(&self, rt: Ty, want: Ty) -> Option<(u8, Autoref)> {
        let want = self.resolve(want);
        let mut t = self.resolve(rt);
        for d in 0..8u8 {
            if t == want {
                return Some((d, Autoref::None));
            }
            if let TyKind::Ref(_, m, inner) = self.kind(want)
                && self.resolve(inner) == t
            {
                return Some((d, if m.is_mut() { Autoref::RefMut } else { Autoref::Ref }));
            }
            t = match self.kind(t) {
                TyKind::Ref(_, _, inner) => self.resolve(inner),
                _ => self.resolve(self.tys.smart_elem(t)?),
            };
        }
        None
    }

    fn autoderef_smart(&self, t: Ty) -> (u8, Ty) {
        let (mut n, mut base) = self.autoderef(t);
        while let Some(inner) = self.tys.smart_elem(base) {
            base = self.resolve(inner);
            n += 1;
            let (d, b) = self.autoderef(base);
            n += d;
            base = b;
        }
        (n, base)
    }
    fn peel_one_ref(&self, t: Ty) -> (u8, Ty) {
        match self.kind(t) {
            TyKind::Ref(_, _, inner) => (1, inner),
            _ => (0, t),
        }
    }
    /// True when `e` is a byte string literal, which the parser
    /// builds as a reference to a byte array literal.
    fn is_byte_str_lit(&self, e: ExprId) -> bool {
        match self.p.ast.expr(e) {
            Expr::Ref { mutable: false, raw: false, expr } => matches!(self.p.ast.expr(*expr), Expr::Array(_)),
            _ => false,
        }
    }

    /// True when a byte string pattern of type `&[u8; N]` may match
    /// a scrutinee of type `t`: rustc also allows `&[u8]` with the
    /// same mutability and element type. Other shapes (an array
    /// value, `&str`, a different length) stay type errors.
    fn byte_str_pat_ok(&mut self, lt: Ty, t: Ty) -> bool {
        let (TyKind::Ref(_, lm, li), TyKind::Ref(_, tm, ti)) = (self.kind(lt), self.kind(t)) else { return false };
        if lm != tm {
            return false;
        }
        match (self.kind(li), self.kind(ti)) {
            (TyKind::Array(e1, _), TyKind::Slice(e2)) => self.unify(e1, e2),
            _ => false,
        }
    }

    /// The value of a float pattern bound, widened to `f64` (exact
    /// for `f32`), if it is known: a float literal (possibly
    /// negated) or a const the checker evaluated.
    fn const_float(&self, e: ExprId, ft: crate::ty::FloatTy) -> Option<f64> {
        use crate::ty::FloatTy;
        if let Some(cv) = &self.out.const_exprs[self.ei(e)] {
            return match cv {
                crate::ty::consteval::ConstValue::Float(bits, FloatTy::F32) => Some(f32::from_bits(*bits as u32) as f64),
                crate::ty::consteval::ConstValue::Float(bits, FloatTy::F64) => Some(f64::from_bits(*bits)),
                _ => None,
            };
        }
        match self.p.ast.expr(e) {
            Expr::Float(i) => {
                let text = &self.p.ast.strings[*i as usize];
                crate::check::collect::parse_float_literal_as(text, ft).map(|bits| match ft {
                    FloatTy::F32 => f32::from_bits(bits as u32) as f64,
                    FloatTy::F64 => f64::from_bits(bits),
                })
            }
            Expr::Unary { op: UnOp::Neg, expr } => self.const_float(*expr, ft).map(|v| -v),
            _ => None,
        }
    }

    /// The value of a literal expression (an integer, possibly negated, or a char), if it is one.
    fn const_scalar(&self, e: ExprId) -> Option<i128> {
        // A const item or associated const the checker evaluated.
        if let Some(cv) = &self.out.const_exprs[self.ei(e)] {
            return match cv {
                crate::ty::consteval::ConstValue::Int(v) => Some(*v),
                crate::ty::consteval::ConstValue::Char(c) => Some(*c as i128),
                crate::ty::consteval::ConstValue::Bool(b) => Some(*b as i128),
                _ => None,
            };
        }
        match self.p.ast.expr(e) {
            Expr::Int(v, _) => Some(*v as u128 as i128),
            Expr::Char(c) => Some(*c as i128),
            Expr::Unary { op: UnOp::Neg, expr } => match self.p.ast.expr(*expr) {
                Expr::Int(v, _) => {
                    if *v == (1u128 << 127) {
                        Some(i128::MIN)
                    } else {
                        Some(-(*v as i128))
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }
    /// The mutability of each reference layer of `t`, outermost first.
    fn ref_layers(&self, t: Ty) -> Vec<bool> {
        let mut out = Vec::new();
        let mut t = t;
        while let TyKind::Ref(_, m, inner) = self.kind(t) {
            out.push(m.is_mut());
            t = inner;
        }
        out
    }

    /// Rejects an explicit lifetime in a value path's turbofish
    /// (`f::<'static>`, ARCH 5.5): rustc rejects it whenever the fn has a
    /// late-bound lifetime (E0794); lust rejects it always (W-BORROW).
    fn lifetime_turbofish(&mut self, segs: &[ast::PathSeg]) {
        let p = self.p;
        for seg in segs {
            if let ast::GenericArgs::Angle(args) = &seg.args {
                for g in args {
                    if let ast::GenericArg::Lifetime(lt) = g
                        && p.interner.get(lt.name) != "_"
                    {
                        self.err("L0731", lt.span, "explicit lifetime arguments on a fn are not supported", "Remove the lifetime argument; Rust infers it.");
                    }
                }
            }
        }
    }

    /// The written type args on a builtin `Option`/`Result` constructor
    /// path (`None::<u8>`, `Option::<u8>::Some`, `Ok::<u8, E>`,
    /// `Result::<u8, E>::Err`), `n` of them in the type's param order;
    /// `_` is a fresh variable. None when the path writes no type args;
    /// a wrong count is rustc's E0107.
    fn builtin_ctor_args(&mut self, segs: &[ast::PathSeg], n: usize, span: Span) -> Option<Vec<Ty>> {
        let p = self.p;
        let written: Vec<ast::TyId> = segs.iter().flat_map(|s| s.type_args()).collect();
        if written.is_empty() {
            return None;
        }
        if written.len() != n {
            self.err(
                "L0107",
                span,
                format!("this type takes {n} generic argument(s) but {} were given", written.len()),
                "Write one type per parameter.",
            );
            return Some((0..n).map(|_| ERROR).collect());
        }
        Some(
            written
                .into_iter()
                .map(|g| if matches!(p.ast.ty(g), ast::TyExpr::Infer) { self.new_var(false) } else { self.resolve_written(g) })
                .collect(),
        )
    }

    /// The const generic param a body path names (`N`): its index in
    /// the template's generics, its declared type, and in an instance
    /// its value from the instance's args (None in the template). None
    /// when `name` names no const param here.
    fn const_param(&mut self, name: Sym) -> Option<(u32, Ty, Option<ConstKind>)> {
        let p = self.p;
        let decl = |tl: LocalDefId, i: u32| -> Option<Ty> {
            match p.gx.fn_templates.get(tl.0 as usize)?.as_ref()?.generics.params.get(i as usize)?.kind {
                ParamKind::Const(t) => Some(t),
                _ => None,
            }
        };
        if let Some(&(_, i, _)) = self.body_scope.const_params.iter().find(|(n, ..)| *n == name) {
            return Some((i, decl(self.fid, i)?, None));
        }
        let info = p.gx.instances.get(&self.fid)?;
        let tl = info.template_local?;
        let &(_, i, _) = p.gx.fn_scopes.get(tl.0 as usize)?.scope.const_params.iter().find(|(n, ..)| *n == name)?;
        let GenericArg::Const(c) = *p.tys.args(info.args).get(i as usize)? else { return None };
        Some((i, decl(tl, i)?, Some(p.tys.const_kind(c))))
    }

    fn path_expr(&mut self, e: ExprId, segs: &[ast::PathSeg], span: Span) -> Ty {
        let p = self.p;
        if segs.len() == 1 {
            let name = segs[0].name;
            if let Some(l) = self.lookup(name, span.ctxt) {
                self.set_res(e, Res::Local(l));
                return self.out.locals[l as usize].ty;
            }
            match self.body_item_of(name, span.ctxt) {
                Some(crate::check::collect::BodyItem::Fn(f)) => {
                    // A nested fn used as a value is a fn item like a
                    // top-level one (its type was the error type with no
                    // diagnostic, so `k as fn(..)` built a null pointer).
                    self.set_res(e, Res::Fn(f));
                    return self.fn_value_ty(e, f, span);
                }
                Some(crate::check::collect::BodyItem::Const(ci)) => {
                    let c = &p.body_consts[ci as usize];
                    let (v, t) = (c.value.clone(), c.ty);
                    let i = self.ei(e);
                    self.out.const_exprs[i] = Some(v);
                    return self.deep(t);
                }
                Some(crate::check::collect::BodyItem::Static(idx)) => {
                    let st = &p.statics[idx as usize];
                    if st.mutable {
                        self.err(
                            "L0404",
                            span,
                            "reading a mutable static requires `unsafe`, which is not supported",
                            "Make the static immutable, or read it through a const.",
                        );
                        return ERROR;
                    }
                    let t = st.ty;
                    self.set_res(e, Res::Static(idx));
                    return self.deep(t);
                }
                None => {}
            }
            // A const generic param (`N`): abstract in the template check
            // (a placeholder value for its own lowering), the instance's
            // arg in an instance.
            if let Some((_, t, val)) = self.const_param(name) {
                let i = self.ei(e);
                match val {
                    Some(ConstKind::Int(v)) => self.out.const_exprs[i] = Some(crate::ty::consteval::ConstValue::Int(v as i128)),
                    Some(ConstKind::Bool(b)) => self.out.const_exprs[i] = Some(crate::ty::consteval::ConstValue::Bool(b)),
                    Some(ConstKind::Char(c)) => self.out.const_exprs[i] = Some(crate::ty::consteval::ConstValue::Char(c)),
                    _ => self.abstract_consts.push(e),
                }
                return self.deep(t);
            }
            // One value-namespace binding read covers the fn and constructor
            // cases below. The prelude `None` keeps its place between them,
            // as before: it is a prelude name, not a module binding.
            // `Self` as a value in an impl of a unit or tuple struct: the
            // unit value or the constructor, at the impl's own args.
            if name == p.known.self_type
                && let Some(a) = self.self_adt()
                && !p.adt(a).is_enum
            {
                match p.adt(a).variants[0].shape {
                    VariantShape::Unit => {
                        self.set_res(e, Res::Variant(a, 0));
                        return match self.self_path_args(a, segs, span) {
                            Some(args) if !args.is_empty() => self.tys.mk_adt(p.def_of_adt(a), &args),
                            _ => self.tys.adt_ty(a),
                        };
                    }
                    VariantShape::Tuple => {
                        // In an instance `Self` names a materialized Adt;
                        // the constructor item is the template's, at the
                        // instance's args.
                        let a = match p.gx.adt_instance_of.get(a.0 as usize).copied().flatten() {
                            Some((def, _)) => p.adt_by_def(def).unwrap_or(a),
                            None => a,
                        };
                        self.set_res(e, Res::Variant(a, 0));
                        return self.ctor_value_ty(e, a, 0, span);
                    }
                    VariantShape::Named => {}
                }
            }
            let bound = self.binding(Namespace::Value, name);
            if let BindingRes::Def(def) = bound
                && p.binding_kind(def) == Some(DefsKind::Fn)
                && let Some(f) = p.local_def(def.hash)
            {
                self.set_res(e, Res::Fn(f));
                return self.fn_value_ty(e, f, span);
            }
            if let BindingRes::Def(def) = bound {
                match p.binding_kind(def) {
                    Some(DefsKind::Const) => {
                        if let Some(idx) = p.const_by_def(def) {
                            let c = &p.consts[idx as usize];
                            let (v, t) = (c.value.clone(), c.ty);
                            let i = self.ei(e);
                            self.out.const_exprs[i] = Some(v);
                            // The value lives in the global store; rebuild the
                            // type in this body's overlay so unification sees it.
                            return self.deep(t);
                        }
                    }
                    Some(DefsKind::Static) => {
                        if let Some(idx) = p.static_by_def(def) {
                            let st = &p.statics[idx as usize];
                            if st.mutable {
                                self.err(
                                    "L0404",
                                    span,
                                    "reading a mutable static requires `unsafe`, which is not supported",
                                    "Make the static immutable, or read it through a const.",
                                );
                                return ERROR;
                            }
                            let t = st.ty;
                            self.set_res(e, Res::Static(idx));
                            return self.deep(t);
                        }
                    }
                    _ => {}
                }
            }
            if name == p.known.None {
                self.set_res(e, Res::OptNone);
                let v = match self.builtin_ctor_args(segs, 1, span) {
                    Some(a) => a[0],
                    None => self.new_var(false),
                };
                return self.tys.mk_option(v);
            }
            if let BindingRes::Def(def) = bound
                && let Some(a) = p.adt_by_def(def)
            {
                let shape = match p.sig_of(&mut self.out.reads, def) {
                    SigOf::Adt(adt) if !adt.is_enum => Some(adt.variants[0].shape),
                    _ => None,
                };
                match shape {
                    Some(VariantShape::Unit) => {
                        self.set_res(e, Res::Variant(a, 0));
                        return self.unit_value_ty(e, a, span);
                    }
                    Some(VariantShape::Tuple) => {
                        self.set_res(e, Res::Variant(a, 0));
                        return self.ctor_value_ty(e, a, 0, span);
                    }
                    _ => {}
                }
            }
            // The prelude's `Some`, `Ok`, and `Err` as values
            // (`.map(Some)`), when no binding takes the name.
            if matches!(bound, BindingRes::Absent) {
                let k = p.known;
                let r = [(k.Some, Res::OptSome), (k.Ok, Res::ResOk), (k.Err, Res::ResErr)].into_iter().find(|&(n, _)| n == name);
                if let Some((_, r)) = r {
                    return self.builtin_item_value(e, r, segs, span);
                }
            }
            self.err(
                "L0101",
                span,
                format!("cannot find value `{}` in this scope", self.name(name)),
                "Check the spelling, or declare it with `let` first.",
            );
            return ERROR;
        }
        // Float associated consts: `f64::NAN`, `f32::EPSILON`,
        // `std::f64::consts::PI`, and kin.
        {
            let names: Vec<&str> = segs.iter().map(|s| self.name(s.name)).collect();
            let assoc = match names.as_slice() {
                [t, item] => Some((*t, *item, false)),
                [pre, t, c, item] if matches!(*pre, "std" | "core") && *c == "consts" => Some((*t, *item, true)),
                _ => None,
            };
            if let Some((ty_name, item, module)) = assoc {
                let f = match ty_name {
                    "f32" => Some(FloatTy::F32),
                    "f64" => Some(FloatTy::F64),
                    _ => None,
                };
                if let Some(f) = f {
                    use crate::ty::consteval::ConstValue;
                    if module {
                        if let Some(bits) = crate::ty::consteval::float_consts_value(f, item) {
                            let i = self.ei(e);
                            self.out.const_exprs[i] = Some(ConstValue::Float(bits, f));
                            return self.tys.float_ty(f);
                        }
                    } else if let Some((v, int_ty)) = crate::ty::consteval::primitive_float_assoc(f, item) {
                        let i = self.ei(e);
                        return match int_ty {
                            Some(it) => {
                                self.out.const_exprs[i] = Some(ConstValue::Int(v as i64 as i128));
                                int(it)
                            }
                            None => {
                                self.out.const_exprs[i] = Some(ConstValue::Float(v, f));
                                self.tys.float_ty(f)
                            }
                        };
                    }
                }
            }
        }
        // `ExitCode::SUCCESS` and `ExitCode::FAILURE` (check/process.rs).
        if let Some(t) = self.exit_code_const(e, segs) {
            return t;
        }
        // Char associated consts.
        if segs.len() == 2 && segs[0].name == p.known.char {
            let c = match self.name(segs[1].name) {
                "MAX" => Some(char::MAX),
                "MIN" => Some(char::MIN),
                "REPLACEMENT_CHARACTER" => Some(char::REPLACEMENT_CHARACTER),
                _ => None,
            };
            if let Some(c) = c {
                let i = self.ei(e);
                self.out.const_exprs[i] = Some(crate::ty::consteval::ConstValue::Char(c));
                return CHAR;
            }
            if self.name(segs[1].name) == "UNICODE_VERSION" {
                use crate::ty::consteval::ConstValue;
                let (maj, min, pat) = char::UNICODE_VERSION;
                let u8t = int(IntTy::U8);
                let ts = self.tys.intern_tys(&[u8t, u8t, u8t]);
                let ty = self.tys.intern(TyKind::Tuple(ts));
                let parts = vec![ConstValue::Int(maj as i128), ConstValue::Int(min as i128), ConstValue::Int(pat as i128)];
                let val = ConstValue::Aggregate(parts);
                let i = self.ei(e);
                self.out.const_exprs[i] = Some(val);
                return ty;
            }
        }
        // Primitive associated consts: `i64::MAX`, `u32::BITS`, and kin.
        if segs.len() == 2
            && let Some(it) = p.known.int_ty(segs[0].name)
        {
            let item = self.name(segs[1].name);
            let bits = it.bits();
            let v = match item {
                "MAX" => Some(crate::ty::consteval::truncate_to_int(it.max128() as i128, it)),
                "MIN" => Some(if it.signed() { if bits >= 128 { i128::MIN } else { -(1i128 << (bits - 1)) } } else { 0 }),
                "BITS" => Some(bits as i128),
                _ => None,
            };
            if let Some(v) = v {
                let (ty, val) = if item == "BITS" {
                    (int(IntTy::U32), crate::ty::consteval::ConstValue::Int(v))
                } else {
                    // u128::MAX does not fit an i128; store its bits as -1 and
                    // let materialization reinterpret them at the u128 type.
                    let val = if it == IntTy::U128 && item == "MAX" { -1 } else { v };
                    (int(it), crate::ty::consteval::ConstValue::Int(val))
                };
                let i = self.ei(e);
                self.out.const_exprs[i] = Some(val);
                return ty;
            }
        }
        // Associated consts of inherent impls (Self::A, Type::A) read
        // as their evaluated value, like free consts. Inherent items
        // shadow trait items, as in rustc. Same-name consts of
        // disjoint impls pick by the written Self type instance.
        // The value is baked into this body, so the const's
        // `Sig` read (its fingerprint folds the value) is
        // recorded, as `const_item_pat` does.
        let assoc_base = if segs.len() == 2 { self.assoc_const_base(segs, Some(span)) } else { None };
        if let Some((adt, item)) = self.assoc_const_key(segs)
            && let Some(picked) = assoc_base.and_then(|base| self.inherent_assoc_pick(adt, item, base, Some(span)))
        {
            return match picked {
                Some(idx) => {
                    if let Some(&def) = p.const_defs.get(idx as usize) {
                        let _ = p.sig_of(&mut self.out.reads, def);
                    }
                    self.check_assoc_vis(adt, item, "associated constant", span);
                    let c = &p.consts[idx as usize];
                    let (v, t) = (c.value.clone(), c.ty);
                    let i = self.ei(e);
                    self.out.const_exprs[i] = Some(v);
                    self.deep(t)
                }
                None => ERROR,
            };
        }
        // Associated consts of traits (`Type::C`, `T::C`,
        // `Self::C`): the value when an impl is confirmed, the
        // declared type alone under param evidence.
        if segs.len() == 2
            && (self.replay_pick(e).is_some()
                || !self.assoc_const_key(segs).is_some_and(|(adt, item)| self.inherent_value_blocks(adt, item)))
            && let Some(base) = assoc_base
            && let Some((idx, t)) = self.trait_assoc_const(Some(e), base, None, segs[1].name, span)
        {
            if let Some(idx) = idx {
                let v = p.consts[idx as usize].value.clone();
                let i = self.ei(e);
                self.out.const_exprs[i] = Some(v);
            }
            return t;
        }
        if let Some(r) = self.resolve_assoc(segs, span) {
            self.set_res(e, r);
            if r == Res::OptNone {
                let v = match self.builtin_ctor_args(segs, 1, span) {
                    Some(a) => a[0],
                    None => self.new_var(false),
                };
                return self.tys.mk_option(v);
            }
            if let Res::Variant(a, v) = r {
                let variant = &p.adt(a).variants[v as usize];
                if variant.shape == VariantShape::Unit {
                    if p.gx.adt_generics[a.0 as usize].params.is_empty() {
                        return self.tys.adt_ty(a);
                    }
                    // A unit variant of a generic enum: its params come
                    // from any turbofish, else from later uses.
                    let gen_args = self.value_path_args(a, segs, span);
                    let preds = p.gx.adt_generics[a.0 as usize].predicates.clone();
                    if !preds.is_empty() {
                        self.push_predicates(&preds, &gen_args, span);
                    }
                    return self.tys.mk_adt(p.def_of_adt(a), &gen_args);
                }
                if variant.shape == VariantShape::Tuple {
                    return self.ctor_value_ty(e, a, v, span);
                }
                self.err("L0101", span, "expected value, found struct variant", "Write a struct literal: `Enum::Variant { .. }`.");
                return ERROR;
            }
            if let Res::Fn(f) = r {
                return self.fn_value_ty(e, f, span);
            }
            if matches!(r, Res::OptSome | Res::ResOk | Res::ResErr | Res::Builtin(Builtin::BoxNew | Builtin::RcNew | Builtin::StringFrom)) {
                return self.builtin_item_value(e, r, segs, span);
            }
            // Other std fns (`String::new`, `Vec::from`) have no value
            // form yet. An error type without a diagnostic would reach
            // codegen, so report every one.
            self.errs.push(unsupported(span, "this std function used as a value"));
            return ERROR;
        }
        ERROR
    }

    /// Resolves a `core::intrinsics::<name>` path. Order is fixed: the
    /// name must exist in the registry, the call site's crate must be on
    /// the row's privilege list, and codegen must implement the row.
    /// A user call site never has a shipped crate, so it stops at the
    /// privilege test with L0642 (docs/ARCH.md sections 3.1 and 3.2).
    fn resolve_intrinsic(&mut self, name: Sym, span: Span) -> Option<Res> {
        let text = self.name(name).to_string();
        let Some(id) = lang::intrinsic_by_name(&text) else {
            self.err(
                "L0104",
                span,
                format!("no intrinsic `core::intrinsics::{text}`"),
                "Intrinsics are a closed registry (src/ty/lang.rs). Call a public std item instead.",
            );
            return None;
        };
        let def = lang::intrinsic(id);
        if !def.allows(self.p.shipped_crate_at(span)) {
            self.err(
                "L0642",
                span,
                format!("intrinsic `core::intrinsics::{text}` can only be called from lust's shipped library crates"),
                "Call the public std item that wraps it instead.",
            );
            return None;
        }
        if !def.implemented {
            self.err(
                "L0640",
                span,
                format!("intrinsic `core::intrinsics::{text}` is declared but not yet implemented"),
                "Implement the registry row and its runtime hook first (docs/ARCH.md section 3.2).",
            );
            return None;
        }
        Some(Res::Intrinsic(id))
    }

    /// Resolves `Type::item` and `std::env::args`. Reports an error and returns None on failure.
    fn resolve_assoc(&mut self, segs: &[ast::PathSeg], span: Span) -> Option<Res> {
        let p = self.p;
        let k = p.known;
        let names: Vec<Sym> = segs.iter().map(|s| s.name).collect();
        if names.len() == 3 && names[0] == k.core && names[1] == k.intrinsics {
            return self.resolve_intrinsic(names[2], span);
        }
        // Shipped source std fns (the `STD_FNS` registry). A declared row
        // with no body yet rejects with L0640; an implemented row routes
        // to the spliced body the loader put in this program. If std was
        // not loaded (the driver trigger missed this spelling), the path
        // falls through to the module-path reject below, never an accept.
        if names[0] == k.std {
            for def in lang::STD_FNS {
                if def.path.len() == names.len() && def.path.iter().zip(&names).all(|(s, n)| *s == self.name(*n)) {
                    if !def.implemented {
                        self.err(
                            "L0640",
                            span,
                            format!("`{}` is declared but not yet implemented in lust std", def.path.join("::")),
                            "Use a std item lust implements today, or write the behavior in your own code.",
                        );
                        return None;
                    }
                    if let Some(f) = p.std_fn_for_path(&names) {
                        return Some(Res::Fn(f));
                    }
                    break;
                }
            }
        }
        if names == [k.std, k.env, k.args] {
            return Some(Res::Builtin(Builtin::EnvArgs));
        }
        if names.len() == 3
            && (names[0] == k.std || names[0] == k.core)
            && self.name(names[1]) == "mem"
            && matches!(self.name(names[2]), "size_of" | "align_of")
        {
            let align = self.name(names[2]) == "align_of";
            return Some(self.layout_query(&segs[2], align, span));
        }
        if names.len() == 2 && names[1] == k.from_bits {
            if names[0] == k.f64 {
                return Some(Res::Builtin(Builtin::F64FromBits));
            }
            if names[0] == k.f32 {
                return Some(Res::Builtin(Builtin::F32FromBits));
            }
        }
        // `char::from_u32`, `char::from_digit`, and the Unicode predicate
        // associated calls (`char::is_alphabetic(&c)`).
        if names.len() == 2 && names[0] == k.char {
            let b = match names[1] {
                n if n == k.from_u32 => Some(Builtin::CharFromU32),
                n if n == k.from_digit => Some(Builtin::CharFromDigit),
                n if n == k.is_alphabetic => Some(Builtin::CharIsAlphabeticUnicode),
                n if n == k.is_numeric => Some(Builtin::CharIsNumericUnicode),
                n if n == k.is_alphanumeric => Some(Builtin::CharIsAlphanumericUnicode),
                n if n == k.is_lowercase => Some(Builtin::CharIsLowercaseUnicode),
                n if n == k.is_uppercase => Some(Builtin::CharIsUppercaseUnicode),
                n if n == k.is_whitespace => Some(Builtin::CharIsWhitespaceUnicode),
                n if n == k.is_control => Some(Builtin::CharIsControlUnicode),
                _ => None,
            };
            if let Some(b) = b {
                return Some(Res::Builtin(b));
            }
        }
        // `fmt::Error`, the unit struct value (W-STD-B).
        if names.len() == 3
            && (names[0] == k.std || names[0] == k.core)
            && self.name(names[1]) == "fmt"
            && self.name(names[2]) == "Error"
            && let Some(a) = p.tys.local_adt_of(generics::fmt_error_def())
        {
            return Some(Res::Variant(a, 0));
        }
        // `mpsc::RecvError`, the unit struct value (W-THREADS).
        if names.len() == 4
            && names[0] == k.std
            && self.name(names[1]) == "sync"
            && self.name(names[2]) == "mpsc"
            && self.name(names[3]) == "RecvError"
            && let Some(a) = p.tys.local_adt_of(generics::recv_error_def())
        {
            return Some(Res::Variant(a, 0));
        }
        // `std::cmp::Ordering::Less`, `std::sync::atomic::Ordering::SeqCst`,
        // and kin: a variant of a synthetic std enum by its full path.
        if names.len() >= 4 && (names[0] == k.std || names[0] == k.core) {
            let path: Vec<&str> = names.iter().map(|n| self.name(*n)).collect();
            if let Some((a, v)) = generics::std_variant_of(p, &path) {
                return Some(Res::Variant(a, v));
            }
            if let Some(a) = generics::std_adt_of_path(&path[..path.len() - 1]).and_then(|d| p.tys.local_adt_of(d))
                && p.adt(a).is_enum
                && crate::ty::lang::std_path_kind(&path[..path.len() - 1]) == Some(crate::ty::lang::StdPathKind::Type)
            {
                let all: Vec<String> = p.adt(a).variants.iter().map(|v| format!("`{}`", self.name(v.name))).collect();
                self.err(
                    "L0104",
                    span,
                    format!("no variant `{}` on `Ordering`", path[path.len() - 1]),
                    format!("Check the name: {}.", all.join(", ")),
                );
                return None;
            }
        }
        // `std::sync::atomic::fence` and the other sync free fns.
        if names.len() >= 3 && (names[0] == k.std || names[0] == k.core) {
            let path: Vec<&str> = names.iter().map(|n| self.name(*n)).collect();
            if let Some(op) = sync::sync_free_fn(&path) {
                return Some(Res::Builtin(Builtin::Sync(op)));
            }
        }
        // The `core::mem` and `core::cmp` free fns by module path.
        if names.len() == 3 && (names[0] == k.std || names[0] == k.core) {
            let b = match (self.name(names[1]), self.name(names[2])) {
                ("mem", "drop") => Some(Builtin::MemDrop),
                ("mem", "swap") => Some(Builtin::MemSwap),
                ("mem", "replace") => Some(Builtin::MemReplace),
                ("mem", "take") => Some(Builtin::MemTake),
                ("cmp", "max") => Some(Builtin::CmpMax),
                ("cmp", "min") => Some(Builtin::CmpMin),
                ("str", "from_utf8") => Some(Builtin::StrFromUtf8),
                _ => None,
            };
            if let Some(b) = b {
                return Some(Res::Builtin(b));
            }
        }
        // A canonical std type path plus an associated item
        // (`std::vec::Vec::new`, `core::option::Option::Some`):
        // the last two segments name the type and the item, as in
        // the two-segment spelling. Only exact table rows qualify.
        let std_ty = segs.len() > 2;
        let (ty_name, item) = if segs.len() == 2 {
            (names[0], names[1])
        } else {
            let path: Vec<&str> = names[..names.len() - 1].iter().map(|n| self.name(*n)).collect();
            if crate::ty::lang::std_path_kind(&path) != Some(crate::ty::lang::StdPathKind::Type) {
                self.errs.push(not_yet("L0505", span, "module paths"));
                return None;
            }
            (names[names.len() - 2], names[names.len() - 1])
        };
        // The first segment is a type-namespace binding read (`Self` is a
        // scope name, not a binding, and records nothing).
        let ty_bound = if ty_name == k.self_type { BindingRes::Absent } else { self.binding(Namespace::Type, ty_name) };
        if ty_name == k.String || ty_name == k.str {
            if let Some(r) = self.utf8_assoc(ty_name == k.String, item, span) {
                return r;
            }
        }
        if ty_name == k.String {
            let b = if item == k.new {
                Builtin::StringNew
            } else if item == k.from {
                Builtin::StringFrom
            } else if item == k.with_capacity {
                Builtin::StringWithCapacity
            } else if item == k.clone {
                Builtin::Clone
            } else {
                self.err(
                    "L0104",
                    span,
                    format!("no function `String::{}`", self.name(item)),
                    "Lust supports String::new, String::from, and String::with_capacity.",
                );
                return None;
            };
            return Some(Res::Builtin(b));
        }
        if ty_name == k.Vec {
            let b = if item == k.new {
                Builtin::VecNew
            } else if item == k.with_capacity {
                Builtin::VecWithCapacity
            } else if item == k.from {
                Builtin::VecFrom
            } else if item == k.clone {
                Builtin::Clone
            } else {
                self.err(
                    "L0104",
                    span,
                    format!("no function `Vec::{}`", self.name(item)),
                    "Lust supports Vec::new, Vec::with_capacity, and Vec::from.",
                );
                return None;
            };
            return Some(Res::Builtin(b));
        }
        if ty_name == k.Box {
            if item == k.new {
                return Some(Res::Builtin(Builtin::BoxNew));
            }
            if item == k.clone {
                return Some(Res::Builtin(Builtin::Clone));
            }
            if item == k.leak {
                return Some(Res::Builtin(Builtin::BoxLeak));
            }
            self.err(
                "L0104",
                span,
                format!("no function `Box::{}`", self.name(item)),
                "Lust supports Box::new and Box::leak.",
            );
            return None;
        }
        // `AtomicUsize::new`, `Arc::new`, `sync::Weak::new`, and the other
        // sync types by their full path (check/sync.rs), ahead of the
        // `rc::Weak` names below.
        if let Some(r) = self.sync_assoc(&names, std_ty, span) {
            return r;
        }
        // `Rc::downgrade`, `Weak::new`, `RefCell::new`, and kin (check/cells.rs).
        if let Some(r) = self.cell_assoc(ty_name, item, std_ty, span) {
            return r;
        }
        if let Some(r) = self.exit_code_assoc(ty_name, item, std_ty, span) {
            return r;
        }
        // A user type named `Rc` shadows std's (which needs a `use`),
        // but never on a std path.
        if ty_name == k.Rc && (std_ty || !self.p.type_names.contains_key(&ty_name)) {
            let b = if item == k.new {
                Builtin::RcNew
            } else if item == k.clone {
                Builtin::Clone
            } else if item == k.strong_count {
                Builtin::RcStrongCount
            } else if item == k.weak_count {
                Builtin::RcWeakCount
            } else if item == k.make_mut {
                Builtin::RcMakeMut
            } else if item == k.get_mut {
                Builtin::RcGetMut
            } else if item == k.try_unwrap {
                Builtin::RcTryUnwrap
            } else if self.name(item) == "into_inner" {
                Builtin::RcIntoInner
            } else if self.name(item) == "unwrap_or_clone" {
                Builtin::RcUnwrapOrClone
            } else {
                self.err(
                    "L0104",
                    span,
                    format!("no function `Rc::{}`", self.name(item)),
                    "Lust supports Rc::new, Rc::strong_count, Rc::weak_count, Rc::make_mut, Rc::get_mut, Rc::try_unwrap, Rc::into_inner, and Rc::unwrap_or_clone.",
                );
                return None;
            };
            return Some(Res::Builtin(b));
        }
        // Qualified builtin variant constructors: `Option::Some(..)`,
        // `Result::Ok(..)`, `Result::Err(..)`.
        if ty_name == k.Option && item == k.Some {
            return Some(Res::OptSome);
        }
        if ty_name == k.Option && item == k.None {
            return Some(Res::OptNone);
        }
        if ty_name == k.Result && item == k.Ok {
            return Some(Res::ResOk);
        }
        if ty_name == k.Result && item == k.Err {
            return Some(Res::ResErr);
        }
        let adt = if ty_name == p.known.self_type {
            self.self_adt()
        } else {
            match ty_bound {
                BindingRes::Def(def) => p.adt_by_def(def),
                _ => None,
            }
        };
        // A type alias of a user Adt (`EA::A(3)`, `SA::new()`, generic
        // `A::make(5)`); `value_path_args` gives its args.
        let adt = adt.or_else(|| self.alias_adt_seg(&segs[segs.len() - 2], span).map(|(a, ..)| a));
        let Some(a) = adt else {
            self.err(
                "L0101",
                span,
                format!("cannot find type `{}`", crate::intern::source_name(self.name(ty_name))),
                "Check the spelling.",
            );
            return None;
        };
        // A std path names std's type, never a user type of the same
        // name (std's `Ordering` is the one std Adt here).
        if std_ty && !generics::is_std_adt(&p.tys, a) {
            self.errs.push(collect::std_path_shadowed(p.interner, ty_name, span));
            return None;
        }
        // The variant and associated-item tables of the Adt are part of its
        // signature read. Associated fns get their own index query when the
        // trait index lands (W-TRAITS-CORE); the method map stays behind
        // this `Sig` read until then.
        let adef = p.def_of_adt(a);
        let is_variant = match p.sig_of(&mut self.out.reads, adef) {
            SigOf::Adt(def) if def.is_enum => def.variants.iter().position(|v| v.name == item),
            _ => None,
        };
        if let Some(v) = is_variant {
            if self.hidden_variant(a, v as u32, span) {
                return None;
            }
            return Some(Res::Variant(a, v as u32));
        }
        p.inherent_reads(&mut self.out.reads, adef, item);
        if let Some(fs) = p.methods.get(&(a, item)).filter(|fs| !fs.is_empty()) {
            // Materialized instances join the same entry; the written
            // fns (one per impl) are the candidates.
            let written: Vec<LocalDefId> = fs.iter().copied().filter(|f| !p.gx.instances.contains_key(f)).collect();
            let f = match written.as_slice() {
                [] => fs[0],
                &[f] => f,
                _ => self.inherent_fn_by_self(a, &written, segs, span)?,
            };
            let what = if p.fn_info(f).self_kind.is_some() { "method" } else { "associated function" };
            self.check_assoc_vis(a, item, what, span);
            return Some(Res::Fn(f));
        }
        // A trait's function of a non-generic type as a value
        // (`S::mk`, `.map(S::from)`): the written impl's own fn.
        if p.gx.adt_generics.get(a.0 as usize).is_none_or(|g| g.params.is_empty()) {
            let base = self.tys.adt_ty(a);
            if let Some(f) = self.trait_fn_value(base, None, item, false, span) {
                return f.map(|(f, _)| Res::Fn(f));
            }
        }
        let tn = self.name(ty_name).to_string();
        self.err("L0104", span, format!("no variant or associated function `{}` on `{tn}`", self.name(item)), "Check the name.");
        None
    }

    /// A trait's function as a value on a concrete type (`S::mk`,
    /// `<S as Tr>::mk`): the trait (written in `hint`, else every
    /// trait in scope with a method of that name) selects a written
    /// impl, and its fn is the value: the impl's own fn, or the
    /// trait's default body when the impl does not write it. Returns
    /// the fn and its instantiation prefix (the impl's args for an
    /// impl fn, the trait ref's args for a default body). With
    /// `generic` false only a plain (non-template) fn answers. None
    /// when nothing applies; Some(None) after reporting an ambiguity.
    /// Core's synthetic impls have no fn to name here (a reject).
    fn trait_fn_value(
        &mut self,
        base: Ty,
        hint: Option<TraitRef>,
        name: Sym,
        generic: bool,
        span: Span,
    ) -> Option<Option<(LocalDefId, Vec<GenericArg>)>> {
        let p = self.p;
        let traits: Vec<DefId> = match hint {
            Some(tr) => vec![tr.def],
            None => p.gx.traits_by_method.get(&name).cloned().unwrap_or_default().into_iter().filter(|&d| method::trait_in_scope_pub(self, d)).collect(),
        };
        // First pass, rolled back: which traits answer.
        let mut hits: Vec<TraitRef> = Vec::new();
        for trait_def in traits {
            let Some(rec) = p.gx.index.trait_record(trait_def).cloned() else { continue };
            if rec.method_by_name(name).is_none() {
                continue;
            }
            let tr = match hint {
                Some(t) => t,
                None => {
                    let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(base)];
                    for _ in 1..rec.generics.params.len() {
                        tr_args.push(GenericArg::Ty(self.new_var(false)));
                    }
                    let args_id = self.tys.intern_args(&tr_args);
                    TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS }
                }
            };
            let snap = self.snapshot_vars();
            let obl_len = self.obl_len();
            let found = self.trait_fn_of(tr, name, generic, span).is_some();
            self.rollback_vars(snap);
            self.obl_truncate(obl_len);
            if found {
                hits.push(tr);
            }
        }
        match hits.len() {
            0 => None,
            // The winner selects again, keeping its bindings.
            1 => self.trait_fn_of(hits[0], name, generic, span).map(Some),
            _ => {
                self.err(
                    "L0720",
                    span,
                    format!("multiple trait functions named `{}` apply here", self.name(name)),
                    "Name the trait with a qualified path, such as `<Type as Trait>::name`.",
                );
                Some(None)
            }
        }
    }

    /// One trait's fn `name` for trait ref `tr` (see `trait_fn_value`):
    /// selection must confirm a written impl with every impl param known.
    fn trait_fn_of(&mut self, tr: TraitRef, name: Sym, generic: bool, span: Span) -> Option<(LocalDefId, Vec<GenericArg>)> {
        use crate::traits::index::Synthetic;
        let p = self.p;
        let Selection::Impl { id, args: impl_args, unbound, .. } = self.select_obligation_at(tr, span, 0) else { return None };
        let rec_impl = p.gx.index.get(id);
        if !unbound.is_empty() || rec_impl.synthetic != Synthetic::None {
            return None;
        }
        let (f, prefix) = match rec_impl.items.iter().find_map(|&d| p.local_def(d.hash).filter(|&l| p.fn_info(l).name == name)) {
            Some(l) => (l, impl_args),
            None => {
                let m = p.gx.index.trait_record(tr.def)?.method_by_name(name)?;
                let l = p.local_def(m.hash)?;
                let raw: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
                (l, raw.into_iter().map(|g| if let GenericArg::Ty(t) = g { GenericArg::Ty(self.deep(t)) } else { g }).collect())
            }
        };
        let is_template = p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some());
        if is_template && !generic {
            return None;
        }
        Some((f, prefix))
    }

    /// The one turbofish type argument on a path callee's last
    /// segment, resolved; a fresh inference variable when absent.
    fn callee_turbo_ty(&mut self, callee: ExprId, span: Span) -> Ty {
        let args = match self.p.ast.expr(callee) {
            Expr::Path(segs) => segs.last().map(|s| s.type_args()).unwrap_or_default(),
            _ => Vec::new(),
        };
        match args.len() {
            0 => self.new_var(false),
            1 => self.resolve_written(args[0]),
            _ => {
                self.err("L0105", span, "this function takes one type argument", "Write one type in the `::<...>`.");
                ERROR
            }
        }
    }

    /// A `size_of` or `align_of` query on the given turbofish type argument:
    /// the layout engine answers, or the layout reject fires (ARCH 4.4).
    fn layout_query(&mut self, seg: &ast::PathSeg, align: bool, span: Span) -> Res {
        let args = seg.type_args();
        if args.len() != 1 {
            self.err("L0105", span, "this function takes one type argument", "Write `size_of::<Type>()`.");
            return Res::ConstUsize(0);
        }
        let t = self.resolve_written(args[0]);
        let p: &Program<'_> = self.p;
        let t = self.deep(t);
        // The answer is baked into this body as a constant. Record a
        // layout read for every Adt in the type: the written-type
        // binding read only names an outermost path, so a compound
        // type (`[S; 2]`, `(S, u8)`) would record nothing for `S`.
        p.record_layout_reads(&mut self.out.reads, &self.tys, t);
        // A template check has no layout for a type over its params;
        // each instance answers with its own (the template body is
        // never generated). A const context still needs the number,
        // and its evaluator rejects the param (`ConstCx::layout`).
        // The placeholder still needs rustc's `T: Sized` requirement:
        // `size_of::<T>()` with only `T: ?Sized` in the env rejects.
        if self.is_template_check() && self.tys.flags(t).contains_param() {
            if !self.sized_ok(t) {
                let tn = self.tn(t);
                self.err(
                    "L0110",
                    span,
                    format!("the size for values of type `{tn}` cannot be known"),
                    "Add a `Sized` bound, or use `size_of_val` on a reference.",
                );
            }
            return Res::ConstUsize(0);
        }
        match crate::ty::layout::layout_of_ty(&self.tys, &UserLayout(p), t) {
            Ok(l) => Res::ConstUsize(if align { l.align } else { l.size }),
            Err(()) => {
                self.err(
                    "L0652",
                    span,
                    format!("unsupported layout form: `{}`", self.tn(t)),
                    "Use a type inside the supported layout grammar.",
                );
                Res::ConstUsize(0)
            }
        }
    }

    /// `From` between a literal variable and a scalar (`u32: From<{integer}>`,
    /// `{float}: From<f32>`), decided as rustc decides it from core's
    /// numeric impls: none is NoImpl, exactly one binds the literal to
    /// it (`let c: char = From::from(65)` makes 65 a u8), more defer to
    /// the literal fallback. None when neither side is such a pair.
    fn lit_from_select(&mut self, input: Ty, ik: TyKind, self_ty: Ty, sk: TyKind) -> Option<Selection> {
        let scalar = |k: TyKind| matches!(k, TyKind::Int(_) | TyKind::Float(_) | TyKind::Char | TyKind::Bool);
        let floats = [self.tys.float_ty(FloatTy::F32), self.tys.float_ty(FloatTy::F64)];
        let lit_types = |k: TyKind| -> Option<Vec<Ty>> {
            if k.is_int_infer() {
                Some(IntTy::ALL_SUPPORTED.iter().map(|&i| int(i)).collect())
            } else if k.is_float_infer() {
                Some(floats.to_vec())
            } else {
                None
            }
        };
        let (var, choices): (Ty, Vec<Ty>) = match (lit_types(ik), lit_types(sk)) {
            (Some(_), Some(_)) => return Some(Selection::Ambiguous),
            (Some(ts), None) if scalar(sk) => (input, ts.into_iter().filter(|&t| Self::numeric_from_ok(self.kind(t), sk)).collect()),
            (None, Some(ts)) if scalar(ik) => (self_ty, ts.into_iter().filter(|&t| Self::numeric_from_ok(ik, self.kind(t))).collect()),
            _ => return None,
        };
        Some(match choices[..] {
            [] => Selection::NoImpl,
            [t] if self.unify(var, t) => Selection::ParamEvidence(usize::MAX),
            [_] => Selection::NoImpl,
            _ => Selection::Ambiguous,
        })
    }

    /// True for the scalar conversions `From` provides in core
    /// (identity is the blanket's job and also answers true).
    fn numeric_from_ok(src: TyKind, dst: TyKind) -> bool {
        // Core's exact `From` set between the scalar types (rustc
        // 1.99 on a 64-bit target; probed exhaustively). Identity
        // is the blanket's job and also answers true. Notable
        // non-obvious cells: `usize`/`isize` have no outgoing
        // impls at all, `usize` is a target only of u8/u16/bool,
        // `isize` only of u8/i8/i16/bool, int-to-float exists only
        // where every value is exact (f32: 16-bit ints, f64:
        // 32-bit ints), and bool converts to every int and float.
        use IntTy::*;
        if src == dst {
            return true;
        }
        match (src, dst) {
            (TyKind::Bool, TyKind::Int(_) | TyKind::Float(_)) => true,
            (TyKind::Char, TyKind::Int(U32 | U64 | U128)) => true,
            (TyKind::Int(U8), TyKind::Char) => true,
            (TyKind::Float(FloatTy::F32), TyKind::Float(FloatTy::F64)) => true,
            (TyKind::Int(s), TyKind::Int(d)) => match (s, d) {
                (Usize | Isize, _) => false,
                (U8 | U16, Usize) => true,
                (U8 | I8 | I16, Isize) => true,
                (_, Usize | Isize) => false,
                _ => d.bits() > s.bits() && (!s.signed() || d.signed()),
            },
            (TyKind::Int(s), TyKind::Float(f)) => match f {
                FloatTy::F32 => matches!(s, U8 | U16 | I8 | I16),
                FloatTy::F64 => matches!(s, U8 | U16 | U32 | I8 | I16 | I32),
            },
            _ => false,
        }
    }

    /// The Adt `Self` names in this body: the method's owner, or the
    /// scope's Self type (a trait default assoc fn has no receiver to
    /// name an owner).
    fn self_adt(&self) -> Option<AdtId> {
        if let Some(a) = self.const_fn_self {
            return a;
        }
        self.f.owner.or_else(|| self.body_scope.self_ty.and_then(|t| self.tys.local_adt(t)))
    }

    /// The Self type of `Type::name(..)` when the call goes through a
    /// trait: `Type` is an Adt (or an alias of one) with no variant and
    /// no inherent fn called `name`, or `picked` (the template check
    /// already resolved the call through a trait). Type arguments are
    /// the written ones (`M::<u8>::mk`, `Self` in `impl M<u8>`, an
    /// alias's), else fresh variables: rustc selects the impl for
    /// that type (E0599 when only `M<u16>` has one).
    fn trait_assoc_base(&mut self, segs: &[ast::PathSeg], picked: bool, span: Span) -> Option<Ty> {
        let p = self.p;
        let (ty_name, item) = (segs[0].name, segs[1].name);
        // A primitive type names itself as the base (`u32::from(x)`):
        // there is no Adt, and the assoc call probes traits for it.
        if let Some(it) = p.known.int_ty(ty_name) {
            return Some(int(it));
        }
        if ty_name == p.known.bool {
            return Some(BOOL);
        }
        if ty_name == p.known.char {
            return Some(CHAR);
        }
        if ty_name == p.known.f32 {
            return Some(self.tys.float_ty(FloatTy::F32));
        }
        if ty_name == p.known.f64 {
            return Some(self.tys.float_ty(FloatTy::F64));
        }
        let a = if ty_name == p.known.self_type {
            self.self_adt()?
        } else {
            match self.binding(Namespace::Type, ty_name) {
                BindingRes::Def(def) => p.adt_by_def(def).or_else(|| self.alias_adt_seg(&segs[0], span).map(|(a, ..)| a))?,
                _ => return None,
            }
        };
        if !picked {
            p.inherent_reads(&mut self.out.reads, p.def_of_adt(a), item);
        }
        if !picked && (p.methods.contains_key(&(a, item)) || (p.adt(a).is_enum && p.adt(a).variants.iter().any(|v| v.name == item))) {
            return None;
        }
        let generics = p.gx.adt_generics.get(a.0 as usize).cloned().unwrap_or_default();
        if generics.params.is_empty() {
            return Some(self.tys.adt_ty(a));
        }
        let args = self.value_path_args(a, &segs[..1], span);
        Some(self.tys.mk_adt(p.def_of_adt(a), &args))
    }

    /// `W::<u8>::new()`: type arguments written on the type segment
    /// of a path call fix the Self type of the inherent impl, and so
    /// the impl's parameters in the method's template args.
    /// In an instance of a generic body, the template's one bound on
    /// `self_ty` whose trait declares `method`, substituted at the
    /// instance's args: what a `T::method(..)` call meant in the
    /// template, where a type param resolves only through its bounds
    /// (see `instance_bound_arg` for the conversion methods). None
    /// outside instances, or when no bound or several bounds match.
    fn instance_bound_ref(&mut self, method: Sym, self_ty: Ty) -> Option<TraitRef> {
        let p = self.p;
        let info = p.gx.instances.get(&self.fid)?;
        let tl = info.template_local?;
        let env = p.gx.fn_scopes.get(tl.0 as usize)?.env.clone();
        let args: Vec<GenericArg> = p.tys.args(info.args).to_vec();
        let self_ty = self.resolve(self_ty);
        let mut found: Option<TraitRef> = None;
        for pred in env {
            let Predicate::Trait(b) = pred else { continue };
            if b.count != 0 || p.gx.index.trait_record(b.value.def).and_then(|r| r.method_by_name(method)).is_none() {
                continue;
            }
            let tr = crate::traits::index::subst_trait_ref_pub(&mut self.tys, b.value, &args);
            if self.tys.args(tr.args).first().and_then(|g| g.as_ty()) != Some(self_ty) {
                continue;
            }
            if found.is_some_and(|f| f != tr) {
                return None;
            }
            found = Some(tr);
        }
        found
    }

    /// True when `t` is an Adt with a written `Index` or `IndexMut`
    /// impl (any args).
    fn has_user_index_impl(&self, t: Ty) -> bool {
        use crate::traits::index::{SelfHead, Synthetic};
        let p = self.p;
        let Some((def, _)) = self.tys.adt_parts(t) else { return false };
        [p.gx.lang.index, p.gx.lang.index_mut].iter().any(|&tr| {
            p.gx.index.impls_of_trait(tr).iter().any(|&id| {
                let rec = p.gx.index.get(id);
                rec.synthetic == Synthetic::None && rec.head == SelfHead::Adt(def)
            })
        })
    }

    /// One of several inherent fns of one name, each in its own impl
    /// (`impl W<u8>` and `impl W<u16>` both define `tag`), by the
    /// path's Self type (`W::<u16>::tag`, an alias, or `Self`): the one
    /// fn whose impl's Self type unifies with it. None after reporting
    /// no match (rustc E0599) or more than one (E0034, `W::tag()`).
    fn inherent_fn_by_self(&mut self, a: AdtId, fs: &[LocalDefId], segs: &[ast::PathSeg], span: Span) -> Option<LocalDefId> {
        let p = self.p;
        let gargs = self.value_path_args(a, &segs[..segs.len().saturating_sub(1).max(1)], span);
        let written = self.tys.mk_adt(p.def_of_adt(a), &gargs);
        let mut found = Vec::new();
        for &f in fs {
            let Some(self_tmpl) = p.gx.fn_scopes.get(f.0 as usize).and_then(|s| s.scope.self_ty) else { continue };
            let self_ty = match p.gx.fn_templates.get(f.0 as usize) {
                Some(Some(tmpl)) => {
                    let args = self.fresh_args(&tmpl.generics.clone());
                    subst(&mut self.tys, self_tmpl, &args)
                }
                _ => self_tmpl,
            };
            let snap = self.snapshot_vars();
            if self.unify(self_ty, written) {
                found.push(f);
            }
            self.rollback_vars(snap);
        }
        let item = self.name(segs[segs.len() - 1].name).to_string();
        match found.as_slice() {
            &[f] => Some(f),
            [] => {
                let tn = self.tn(written);
                self.err("L0104", span, format!("no associated function `{item}` for `{tn}`"), "Check the type's arguments.");
                None
            }
            _ => {
                self.err(
                    "L0720",
                    span,
                    format!("multiple applicable items named `{item}` are in scope"),
                    "Write the type's arguments, such as `W::<u8>::name`.",
                );
                None
            }
        }
    }

    /// The Self type a path call or fn value writes before the fn's
    /// name fixes the impl's params: `S::<u8>::make`, or an alias of
    /// the Adt at fixed args (`type A = S<u8>; A::make(5)`), where
    /// `value_path_args` gives the alias's args. `inst_args` is empty
    /// for a plain fn: a concrete impl's Self (`impl S<u8>`) must then
    /// be the written type (rustc E0599 for `S::<u16>::make`).
    fn unify_written_self(&mut self, callee: ExprId, f: LocalDefId, inst_args: &[GenericArg], span: Span) {
        let p = self.p;
        let Expr::Path(segs) = p.ast.expr(callee) else { return };
        if segs.len() != 2 || !(segs[0].has_args() || self.alias_adt_seg(&segs[0], span).is_some_and(|(_, args, _)| !args.is_empty())) {
            return;
        }
        let Some(owner) = p.fn_info(f).owner else { return };
        let Some(self_tmpl) = p.gx.fn_scopes.get(f.0 as usize).and_then(|s| s.scope.self_ty) else { return };
        let gargs = self.value_path_args(owner, &segs[..1], span);
        let written_ty = self.tys.mk_adt(p.def_of_adt(owner), &gargs);
        let self_ty = subst(&mut self.tys, self_tmpl, inst_args);
        if !self.unify(self_ty, written_ty) {
            self.mismatch(span, written_ty, self_ty);
        }
    }

    /// An associated function call through a trait:
    /// `<T as Tr>::name(..)` or `T::name(..)`. Selects the impl
    /// for the Self type and calls the method as a free fn (an
    /// explicit receiver is simply its first parameter).
    fn assoc_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        base: Ty,
        hint: Option<TraitRef>,
        name: Sym,
        args: &[ExprId],
        span: Span,
    ) -> Option<Ty> {
        let p = self.p;
        // An instance replays the template's param-env evidence for a
        // `from` call (`U: From<u8>` fixes the input: check/picks.rs).
        let hint = match self.replayed_trait_ref(e, p.gx.lang.from) {
            Some(r) if self.name(name) == "from" && hint.is_none_or(|h| h.def == p.gx.lang.from) => Some(r),
            _ => hint,
        };
        // Numeric `From::from` is a widening cast, with no user
        // fn behind it (the lang blanket covers only identity).
        if self.name(name) == "from" && args.len() == 1 && hint.is_none_or(|h| h.def == p.gx.lang.from) {
            let src = self.expr(args[0], None);
            // A written trait (`<M as From<i32>>::from`) fixes the
            // input type: a literal takes it, and a suffixed
            // argument of another type is the mismatch rustc
            // reports through the impl's signature below.
            let hint_input = hint.and_then(|h| self.tys.args(h.args).get(1).and_then(|g| g.as_ty())).map(|t| self.deep(t));
            let hint_ok = match hint_input {
                Some(hi) => self.unify(src, hi),
                None => true,
            };
            let src = self.deep(src);
            if hint_ok && Self::numeric_from_ok(self.kind(src), self.kind(base)) {
                self.set_res(callee, Res::FromCast);
                self.set_res(e, Res::FromCast);
                return Some(base);
            }
            let src_kind = self.kind(src);
            if matches!(src_kind, TyKind::Int(_) | TyKind::Float(_) | TyKind::Char | TyKind::Bool)
                || src_kind.is_int_infer()
                || src_kind.is_float_infer()
            {
                // With the input type known from the argument,
                // selection can pick between input-specific impls
                // (or, in a template check, the bounds for each From).
                // An unsuffixed literal with several fitting impls
                // falls back to i32/f64, as in rustc: try the
                // written or literal type first, then the fallback.
                let mut candidates: Vec<TraitRef> = Vec::new();
                match hint {
                    Some(h) => candidates.push(h),
                    None => {
                        let args_id = self.tys.intern_args(&[GenericArg::Ty(base), GenericArg::Ty(src)]);
                        candidates.push(TraitRef { def: p.gx.lang.from, args: args_id, bindings: EMPTY_BINDINGS });
                    }
                }
                let fallback = if src_kind.is_int_infer() {
                    Some(int(IntTy::I32))
                } else if src_kind.is_float_infer() {
                    Some(self.tys.float_ty(FloatTy::F64))
                } else {
                    None
                };
                let n_tries = if fallback.is_some() { 2 } else { 1 };
                for try_no in 0..n_tries {
                    let snap = self.snapshot_vars();
                    let obl_len = self.obl_len();
                    let sites_len = self.generic_sites.len();
                    let tr = if try_no == 0 {
                        candidates[0]
                    } else {
                        let fb = fallback.expect("second try has a fallback");
                        if !self.unify(src, fb) {
                            break;
                        }
                        // The fallback type widens like a suffixed literal.
                        if Self::numeric_from_ok(self.kind(fb), self.kind(base)) {
                            self.set_res(callee, Res::FromCast);
                            self.set_res(e, Res::FromCast);
                            return Some(base);
                        }
                        let args_id = self.tys.intern_args(&[GenericArg::Ty(base), GenericArg::Ty(fb)]);
                        TraitRef { def: p.gx.lang.from, args: args_id, bindings: EMPTY_BINDINGS }
                    };
                    let mut env_pick: Option<usize> = None;
                    let found = match self.select_obligation_at(tr, span, 0) {
                        Selection::Impl { id, args: impl_args, .. } => self.method_instance_for_impl(e, id, tr, impl_args, "from", span),
                        // The one numeric impl a literal fits (it is bound now).
                        Selection::ParamEvidence(usize::MAX) => {
                            self.set_res(callee, Res::FromCast);
                            self.set_res(e, Res::FromCast);
                            return Some(base);
                        }
                        Selection::ParamEvidence(i) => {
                            env_pick = Some(i);
                            self.stub_instance(e, tr, name, span)
                        }
                        _ => None,
                    };
                    if let Some((local, params, ret)) = found {
                        if env_pick.is_some() {
                            self.record_pick_env(e, p.gx.lang.from, 0, ReceiverForm::Value, env_pick);
                        }
                        self.set_res(e, Res::Fn(local));
                        self.check_args(&params, args, span);
                        return Some(self.normalize_use(ret, span));
                    }
                    self.rollback_vars(snap);
                    self.obl_truncate(obl_len);
                    self.generic_sites.truncate(sites_len);
                }
                // A literal argument with no scalar impl even after its fallback
                // has no other reading (`let d: u32 = From::from(c)` with
                // `c = 3` needs `u32: From<i32>`): report it here, not
                // through a later path that does not check the impl.
                if let Some(fb) = fallback
                    && matches!(self.kind(base), TyKind::Int(_) | TyKind::Float(_) | TyKind::Char | TyKind::Bool)
                {
                    let (fbn, tn) = (self.tn(fb), self.tn(base));
                    let msg = format!("no impl of `From<{fbn}>` for `{tn}`");
                    self.err("L0612", span, msg, "Add a literal suffix, or change the target type.");
                    return Some(ERROR);
                }
                return None;
            }
        }
        if self.name(name) == "default"
            && args.is_empty()
            && matches!(self.kind(base), TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit)
        {
            self.set_res(callee, Res::DefaultVal);
            self.set_res(e, Res::DefaultVal);
            return Some(base);
        }
        // `<dyn P as Tr>::m(d)` and `<dyn P>::m(d)` (ARCH 2.8): an
        // `impl dyn P` method, or an object candidate through the vtable.
        if let Some(t) = self.dyn_assoc_call(e, base, hint, name, args, span) {
            return Some(t);
        }
        // The trait: written, or the template check's pick, or the
        // where clauses of a type parameter (rustc probes those as
        // inherent candidates first), or every trait in scope.
        let bound = if hint.is_none() { self.bound_traits_with(base, name) } else { Vec::new() };
        let traits: Vec<DefId> = match (hint, self.replay_pick(e)) {
            (Some(tr), _) => vec![tr.def],
            (None, Some(pick)) => vec![pick.trait_def],
            (None, None) if !bound.is_empty() => bound,
            (None, None) => {
                p.gx.traits_by_method
                    .get(&name)
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .filter(|&d| method::trait_in_scope_pub(self, d))
                    .collect()
            }
        };
        let mut hits: Vec<(LocalDefId, Vec<Ty>, Ty)> = Vec::new();
        let mut hit_traits: Vec<DefId> = Vec::new();
        // The env predicate of the first param-env hit (`record_pick_env`).
        let mut hit_env: Option<usize> = None;
        // Traits whose selection the open inputs left ambiguous.
        let mut ambiguous: Vec<DefId> = Vec::new();
        // A `Default` impl with no method fn (a derive, or core's
        // impl for a builtin type) that builds its value by
        // structure: lowering emits the `default` glue.
        let mut default_glue = false;
        for trait_def in traits {
            let Some(rec) = p.gx.index.trait_record(trait_def).cloned() else { continue };
            if rec.method_by_name(name).is_none() {
                continue;
            }
            let snap = self.snapshot_vars();
            let obl_len = self.obl_len();
            let sites_len = self.generic_sites.len();
            let tr = self.assoc_trait_ref(e, base, hint, trait_def, &rec);
            match self.select_obligation_at(tr, span, 0) {
                Selection::Impl { id, args: impl_args, .. } => {
                    let mname = self.name(name).to_string();
                    if let Some(found) = self.method_instance_for_impl(e, id, tr, impl_args, &mname, span) {
                        hits.push(found);
                        hit_traits.push(trait_def);
                        continue;
                    }
                    if trait_def == p.gx.lang.default
                        && mname == "default"
                        && p.gx.index.get(id).synthetic != crate::traits::index::Synthetic::None
                        && has_default(p, &self.tys, base)
                    {
                        default_glue = true;
                        hit_traits.push(trait_def);
                        continue;
                    }
                }
                // A structural answer (tuples, arrays: no impl
                // record) is not a bound: `Default` builds by glue,
                // and no other trait method has a body to call.
                Selection::ParamEvidence(usize::MAX) => {
                    if trait_def == p.gx.lang.default && self.name(name) == "default" && has_default(p, &self.tys, base) {
                        default_glue = true;
                        hit_traits.push(trait_def);
                        continue;
                    }
                }
                Selection::ParamEvidence(i) => {
                    if let Some(found) = self.stub_instance(e, tr, name, span) {
                        hits.push(found);
                        hit_traits.push(trait_def);
                        hit_env.get_or_insert(i);
                        continue;
                    }
                }
                // The trait's inputs are open (`S::conv(3u8)` with impls
                // of `Conv<u8>` and `Conv<u16>`; `S::from(o)`, where
                // core's identity impl also applies): the args may fix
                // them (`assoc_call_deferred`).
                Selection::Ambiguous if rec.generics.params.len() > 1 => ambiguous.push(trait_def),
                _ => {}
            }
            self.rollback_vars(snap);
            self.obl_truncate(obl_len);
            self.generic_sites.truncate(sites_len);
        }
        if hits.is_empty()
            && !default_glue
            && let [trait_def] = ambiguous[..]
        {
            return self.assoc_call_deferred(e, base, hint, trait_def, name, args, span);
        }
        match hits.len() {
            0 if default_glue && hit_traits.len() == 1 => {
                self.record_glue_reads(p.gx.lang.default, base);
                self.record_pick(e, hit_traits[0], 0, ReceiverForm::Value);
                self.set_res(callee, Res::DefaultVal);
                self.set_res(e, Res::DefaultVal);
                self.check_args(&[], args, span);
                Some(base)
            }
            1 if !default_glue => {
                let (local, params, ret) = hits.into_iter().next().unwrap();
                self.record_pick_env(e, hit_traits[0], 0, ReceiverForm::Value, hit_env);
                self.set_res(e, Res::Fn(local));
                self.check_args(&params, args, span);
                Some(self.normalize_use(ret, span))
            }
            0 => None,
            _ => {
                self.err(
                    "L0720",
                    span,
                    format!("multiple trait methods named `{}` apply here", self.name(name)),
                    "Call the method with a fully qualified path, such as `<Type as Trait>::method(...)`.",
                );
                for &a in args {
                    self.expr(a, None);
                }
                Some(ERROR)
            }
        }
    }

    /// Records the reads behind a structural answer of the derive
    /// glue (`has_clone`, `has_default`): the layout of every Adt in
    /// `t`, whose fingerprint covers derives, nested field types, and
    /// the written impls the glue calls (`glue_methods`), so a warm
    /// body rechecks when one of those changes (section 8.2; the
    /// predicates themselves record nothing).
    fn record_glue_reads(&mut self, _trait_def: DefId, t: Ty) {
        let t = self.deep(t);
        self.p.record_layout_reads(&mut self.out.reads, &self.tys, t);
    }

    /// The trait ref an assoc call on `base` asks of `trait_def`: the
    /// written one, or Self with the template's replayed inputs, or
    /// fresh variables for them.
    fn assoc_trait_ref(&mut self, e: ExprId, base: Ty, hint: Option<TraitRef>, trait_def: DefId, rec: &crate::traits::index::TraitRecord) -> TraitRef {
        if let Some(written) = hint.filter(|h| h.def == trait_def) {
            return written;
        }
        let replayed = self.replayed_trait_ref(e, trait_def);
        let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(base)];
        for (i, param) in rec.generics.params.iter().enumerate().skip(1) {
            let arg = match replayed.and_then(|r| self.tys.args(r.args).get(i).copied()) {
                Some(g) => g,
                None => match param.kind {
                    ParamKind::Const(_) => GenericArg::Const(self.fresh_const_var()),
                    _ => GenericArg::Ty(self.new_var(false)),
                },
            };
            tr_args.push(arg);
        }
        let args_id = self.tys.intern_args(&tr_args);
        TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS }
    }

    /// An assoc call whose trait inputs only the args fix (see
    /// `assoc_call`), deferred as rustc does and as method calls do
    /// (`method::confirm_deferred`): the call is typed by the trait's
    /// own signature, the trait obligation stays queued (its error is
    /// rustc's E0277), and body end selects the impl
    /// (`method::finish_deferred_methods`).
    #[allow(clippy::too_many_arguments)]
    fn assoc_call_deferred(
        &mut self,
        e: ExprId,
        base: Ty,
        hint: Option<TraitRef>,
        trait_def: DefId,
        name: Sym,
        args: &[ExprId],
        span: Span,
    ) -> Option<Ty> {
        let p = self.p;
        let rec = p.gx.index.trait_record(trait_def)?;
        let method_def = rec.method_by_name(name)?;
        let n_trait = rec.generics.params.len();
        let tr = self.assoc_trait_ref(e, base, hint, trait_def, rec);
        let mut full: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
        let (sig_params, sig_ret, preds) = match p.gx.trait_methods.get(&method_def) {
            Some(t) => {
                for param in t.generics.params.iter().skip(n_trait) {
                    full.push(match param.kind {
                        ParamKind::Type => GenericArg::Ty(self.new_var(false)),
                        ParamKind::Lifetime => GenericArg::Lifetime(Region::Erased),
                        ParamKind::Const(_) => GenericArg::Const(self.fresh_const_var()),
                    });
                }
                (t.params.clone(), t.ret, t.generics.predicates.clone())
            }
            None => {
                let s = p.gx.lang_method_sigs.get(&method_def)?;
                (s.params.clone(), s.ret, Vec::new())
            }
        };
        let mut params: Vec<Ty> = sig_params.iter().map(|&t| subst(&mut self.tys, t, &full)).collect();
        let ret = subst(&mut self.tys, sig_ret, &full);
        self.normalize_params(&mut params, span);
        self.push_predicates(&preds, &full, span);
        self.obl.push_trait_at(tr, span, 0);
        method::defer_path_call(self, e, tr, name, full[n_trait..].to_vec());
        self.record_pick(e, trait_def, 0, ReceiverForm::Value);
        self.check_args(&params, args, span);
        Some(self.normalize_use(ret, span))
    }

    /// `Default::default()`, `From::from(x)`, and a user trait's fn
    /// with no `self` (`Mk::mk(8)`) written through the trait name,
    /// where no arg names Self: the expected type does (rustc infers it
    /// the same way), and the call is the assoc call on that type. With
    /// the expected type not known yet, a user trait's call is typed by
    /// the trait's signature with Self open (`assoc_call_deferred`), so
    /// a later use can fix it; nothing fixing it is rustc's E0790. None
    /// when the callee is another form or a type of that name shadows
    /// the trait.
    fn self_from_expected_call(&mut self, e: ExprId, callee: ExprId, args: &[ExprId], expected: Option<Ty>, span: Span) -> Option<Ty> {
        let p = self.p;
        let Expr::Path(segs) = p.ast.expr(callee) else { return None };
        if segs.len() != 2 || p.type_names.contains_key(&segs[0].name) || p.aliases.contains_key(&segs[0].name) {
            return None;
        }
        if self.body_scope.param_tys.iter().any(|(n, _)| *n == segs[0].name) {
            return None;
        }
        let lang = &p.gx.lang;
        let tdef = p.gx.resolve_cx(&p.type_names, &p.aliases).trait_by_bare_name(p.interner, segs[0].name)?;
        let rec = p.gx.index.trait_record(tdef)?;
        let lang_fn = match self.name(segs[1].name) {
            "default" => tdef == lang.default && args.is_empty(),
            "from" => tdef == lang.from && args.len() == 1,
            _ => false,
        };
        let user_fn = !lang_fn
            && rec.method_by_name(segs[1].name).and_then(|m| p.gx.trait_methods.get(&m)).is_some_and(|t| t.self_kind.is_none());
        if !lang_fn && !user_fn {
            return None;
        }
        let known = expected.map(|t| self.deep(t)).filter(|&b| b != ERROR && !self.unbound_general(b));
        let Some(base) = known else {
            if !user_fn {
                return None;
            }
            let base = self.new_var(false);
            return self.assoc_call_deferred(e, base, None, tdef, segs[1].name, args, span);
        };
        let hint = self.assoc_trait_ref(e, base, None, tdef, rec);
        self.assoc_call(e, callee, base, Some(hint), segs[1].name, args, span)
    }

    /// The trait method's signature stub for a call the param env
    /// proves (a template check), instantiated at the trait ref's
    /// args and the method's own fresh ones: (stub, params, ret).
    fn stub_instance(&mut self, e: ExprId, tr: TraitRef, name: Sym, span: Span) -> Option<(LocalDefId, Vec<Ty>, Ty)> {
        let p = self.p;
        let method_def = p.gx.index.trait_record(tr.def)?.method_by_name(name)?;
        let stub = *p.gx.trait_method_stubs.get(&method_def)?;
        let generics = p.gx.fn_templates.get(stub.0 as usize)?.as_ref()?.generics.clone();
        let raw: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
        let prefix: Vec<Option<GenericArg>> = raw
            .iter()
            .map(|&g| {
                Some(match g {
                    GenericArg::Ty(t) => GenericArg::Ty(self.deep(t)),
                    other => other,
                })
            })
            .collect();
        let (mut params, ret, _) = self.instantiate_template(e, stub, &generics, &prefix, span);
        self.normalize_params(&mut params, span);
        Some((stub, params, ret))
    }

    /// A call through an Fn-family bound of a type parameter or
    /// projection in this body's env (a template check). Rust calls
    /// through `Fn` when the bounds give it, else `FnMut`, else
    /// `FnOnce`: (the trait method's stub, the receiver form, the
    /// input types, the output type).
    fn fn_bound_call(&mut self, callee: Ty) -> Option<(LocalDefId, Autoref, Vec<Ty>, Ty)> {
        let p = self.p;
        let lang = p.gx.lang;
        for (tr, method, autoref) in
            [(lang.fn_, "call", Autoref::Ref), (lang.fn_mut, "call_mut", Autoref::RefMut), (lang.fn_once, "call_once", Autoref::None)]
        {
            self.note_opaques(callee);
            let env = self.solve_env();
            let Some(bound) = env.iter().find_map(|pred| match pred {
                Predicate::Trait(b)
                    if b.count == 0 && b.value.def == tr && self.tys.args(b.value.args).first().and_then(|g| g.as_ty()) == Some(callee) =>
                {
                    Some(b.value)
                }
                _ => None,
            }) else {
                continue;
            };
            let inputs = match self.tys.args(bound.args).get(1).and_then(|g| g.as_ty()).map(|t| self.tys.kind(t)) {
                Some(TyKind::Tuple(ts)) => self.tys.tys_of(ts).to_vec(),
                _ => Vec::new(),
            };
            // The output: the bound's own binding when written there,
            // else its projection, which the env's equalities settle.
            let out_assoc = lang.output_of(tr)?;
            let out = match self.tys.bindings(bound.bindings).iter().find(|(d, _)| *d == out_assoc).and_then(|(_, g)| g.as_ty()) {
                Some(t) => t,
                None => self.tys.intern(TyKind::Projection(AssocId(out_assoc), bound.args)),
            };
            let method_def = p.gx.index.trait_record(tr)?.method_by_name(p.interner.intern(method))?;
            let stub = *p.gx.trait_method_stubs.get(&method_def)?;
            return Some((stub, autoref, inputs, out));
        }
        None
    }

    /// The call resolution for a callable value's type: a fn pointer
    /// calls indirectly, a fn item calls its fn directly, and a
    /// constructor item builds its variant.
    fn callable_res(&mut self, ct: Ty) -> Option<Res> {
        match self.kind(ct) {
            TyKind::FnPtr(_) => Some(Res::Indirect),
            TyKind::FnDef(def, cargs) => match self.p.adt_by_def(def) {
                Some(a) => Some(Res::Variant(a, self.ctor_variant(cargs))),
                None => self.builtin_item_res(def, cargs).map(|(r, _, _)| r).or_else(|| self.p.local_def(def.hash).map(Res::Fn)),
            },
            _ => None,
        }
    }

    /// A trait ref written in a body path (`<T as Tr<u8, _>>`,
    /// `Tr::<u8>::m`) with `base` as Self; `_` args become body
    /// variables.
    fn written_trait_ref(&mut self, base: Ty, tref: &ast::TraitRefExpr, span: Span) -> Result<TraitRef, Diag> {
        let p = self.p;
        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
        let tr = generics::resolve_trait_ref(p.ast, p.interner, p.known, &cx, &mut self.tys, &self.body_scope.clone(), base, tref, span)?;
        let old: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
        let new: Vec<GenericArg> = old
            .into_iter()
            .map(|g| match g {
                GenericArg::Ty(t) => GenericArg::Ty(self.instantiate_infers(t)),
                g => g,
            })
            .collect();
        Ok(TraitRef { args: self.tys.intern_args(&new), ..tr })
    }

    /// True when the trait args of `hint` past Self can name the
    /// existential trait ref `owner`: each equal, or still inferred.
    fn trait_args_fit(&mut self, hint: TraitRef, owner: TraitRef) -> bool {
        let (hs, os) = (self.tys.args(hint.args).to_vec(), self.tys.args(owner.args).to_vec());
        hs.len() == os.len()
            && hs.iter().zip(&os).skip(1).all(|(a, b)| match (a.as_ty(), b.as_ty()) {
                (Some(a), Some(b)) => {
                    let a = self.deep(a);
                    matches!(self.tys.kind(a), TyKind::Infer(_)) || a == self.deep(b)
                }
                _ => true,
            })
    }

    /// A path call on a dyn Self type: the `impl dyn P` method of that
    /// name, else the one object candidate (of the hinted trait, when
    /// written, or of the template's pick when this body replays one),
    /// called through the vtable with the receiver as the first
    /// argument. None when `base` is not a dyn type or nothing matches
    /// (the caller reports).
    fn dyn_assoc_call(&mut self, e: ExprId, base: Ty, hint: Option<TraitRef>, name: Sym, args: &[ExprId], span: Span) -> Option<Ty> {
        let p = self.p;
        let base = self.resolve(base);
        let principal = object::principal_of(&self.tys, base)?;
        let key = object::erase_dyn_region(&mut self.tys, base);
        let only = hint.map(|h| h.def).or_else(|| self.replay_pick(e).map(|pick| pick.trait_def));
        if only.is_none()
            && let Some(&f) = p.gx.dyn_inherent.get(&(key, name))
        {
            // Object candidates are inherent too, so a trait method of
            // the same name makes the path ambiguous (rustc E0034).
            if !object::object_cands(p, &mut self.tys, principal, name).is_empty() {
                self.err(
                    "L0720",
                    span,
                    format!("multiple applicable items named `{}` are in scope for this `dyn` type", self.name(name)),
                    "Name the trait: `<dyn Trait as Trait>::method(receiver)`.",
                );
                for &a in args {
                    self.expr(a, None);
                }
                return Some(ERROR);
            }
            self.check_dyn_method_vis(f, span);
            let (params, ret) = {
                let info = p.fn_info(f);
                (info.params.clone(), p.ret_view(f))
            };
            let ret = self.callee_ret(ret);
            self.set_res(e, Res::Fn(f));
            self.check_args(&params, args, span);
            return Some(ret);
        }
        let mut cands: Vec<(usize, object::ObjectCand)> = object::object_cands(p, &mut self.tys, principal, name)
            .into_iter()
            .enumerate()
            .filter(|(_, c)| only.is_none_or(|t| t == c.owner.def))
            .collect();
        // Written trait args pick the ref of that trait (`<dyn P as
        // B<u16>>::m` with `P: B<u8> + B<u16>`), or none.
        if let Some(h) = hint {
            cands.retain(|(_, c)| self.trait_args_fit(h, c.owner));
        }
        if cands.len() != 1 {
            return None;
        }
        let (ci, c) = cands.into_iter().next().unwrap();
        if let Some(h) = hint {
            let (hs, os) = (self.tys.args(h.args).to_vec(), self.tys.args(c.owner.args).to_vec());
            for (a, b) in hs.iter().zip(&os).skip(1) {
                if let (Some(a), Some(b)) = (a.as_ty(), b.as_ty()) {
                    self.unify(a, b);
                }
            }
        }
        let slot = match c.call {
            Ok((slot, _)) => slot,
            Err(why) => {
                let tn = self.tn(base);
                self.err(
                    "L0703",
                    span,
                    format!("the method `{}` cannot be called on `{tn}`: {why}", self.name(name)),
                    "Call it on a concrete type.",
                );
                return Some(ERROR);
            }
        };
        let tm = p.gx.trait_methods.get(&c.def)?;
        let (tparams, tret) = (tm.params.clone(), tm.ret);
        let mut sargs: Vec<GenericArg> = self.tys.args(c.owner.args).to_vec();
        sargs[0] = GenericArg::Ty(base);
        let params: Vec<Ty> = tparams.iter().map(|&t| subst(&mut self.tys, t, &sargs)).collect();
        let ret = subst(&mut self.tys, tret, &sargs);
        let cand = u8::try_from(ci).expect("at most 256 object candidates");
        self.set_res(e, Res::DynMethod { owner: c.owner.def, cand, slot, derefs: 0, autoref: Autoref::None });
        if c.needs_static && !object::dyn_is_static(p, &self.tys, base) {
            self.obl.push(obligations::Obligation::DynStatic { span });
        }
        self.check_args(&params, args, span);
        Some(self.normalize_here(ret))
    }

    /// Some(true) for a callee that names std's `align_of_val`, Some(false)
    /// for `size_of_val`: the bare prelude name (since Rust 1.80) unless a
    /// user fn of that name shadows it, or a `std::mem`/`core::mem` path.
    fn layout_of_val_callee(&mut self, callee: ExprId) -> Option<bool> {
        let Expr::Path(segs) = self.p.ast.expr(callee) else { return None };
        let last = match segs.iter().map(|s| self.name(s.name)).collect::<Vec<_>>().as_slice() {
            [n] | ["std" | "core", "mem", n] => *n,
            _ => return None,
        };
        let align = match last {
            "size_of_val" => false,
            "align_of_val" => true,
            _ => return None,
        };
        if let [seg] = segs.as_slice()
            && (self.body_item_of(seg.name, self.span(callee).ctxt).is_some() || self.binding_fn(seg.name).is_some())
        {
            return None;
        }
        Some(align)
    }

    /// `size_of_val(&value)` or `align_of_val(&value)`: a constant from
    /// the layout of the value's type, or for a dyn value the size or
    /// align word of its vtable.
    fn layout_of_val(&mut self, e: ExprId, args: &[ExprId], align: bool, span: Span) -> Ty {
        let p = self.p;
        let what = if align { "align_of_val" } else { "size_of_val" };
        if args.len() != 1 {
            self.err("L0105", span, "this function takes 1 argument but a different number was given", "Pass exactly one reference.");
            for &a in args {
                self.expr(a, None);
            }
            return ERROR;
        }
        let at = self.expr(args[0], None);
        let at = self.deep(at);
        let inner = match self.kind(at) {
            TyKind::Ref(_, _, inner) => inner,
            _ => {
                let tn = self.tn(at);
                self.err("L0110", span, format!("`{what}` takes a reference, found `{tn}`"), "Pass `&value`.");
                return ERROR;
            }
        };
        let inner = self.deep(inner);
        if matches!(self.kind(inner), TyKind::Dyn(..)) {
            self.set_res(e, Res::DynMeta(if align { object::VT_ALIGN } else { object::VT_SIZE }));
            return USIZE;
        }
        p.record_layout_reads(&mut self.out.reads, &self.tys, inner);
        // A template check has no layout for a type over its
        // params (`size_of_val(t)` with `T: ?Sized` included);
        // each instance answers with its own, as in
        // `layout_query`. No Sized proof is needed here.
        if self.is_template_check() && self.tys.flags(inner).contains_param() {
            self.set_res(e, Res::ConstUsize(0));
            return USIZE;
        }
        match crate::ty::layout::layout_of_ty(&self.tys, &UserLayout(p), inner) {
            Ok(l) => {
                self.set_res(e, Res::ConstUsize(if align { l.align } else { l.size }));
                USIZE
            }
            Err(()) => {
                // Unsized tails with a runtime length: a slice is
                // `len * size_of::<elem>()`, a `str` is its byte
                // length; the align of both is the element's. Other
                // unsized forms (a generic Adt with an unsized last
                // field) stay the layout reject.
                let tail = match self.kind(inner) {
                    TyKind::Slice(elem) => {
                        crate::ty::layout::layout_of_ty(&self.tys, &UserLayout(p), elem).ok().map(|l| (Builtin::SliceLen, l.size, l.align))
                    }
                    TyKind::Str => Some((Builtin::StrLen, 1, 1)),
                    _ => None,
                };
                match tail {
                    Some((_, _, elem_align)) if align => {
                        self.set_res(e, Res::ConstUsize(elem_align));
                        USIZE
                    }
                    Some((len, elem, _)) => {
                        self.set_res(e, Res::SizeOfVal { len, elem });
                        USIZE
                    }
                    None => {
                        self.err(
                            "L0652",
                            span,
                            format!("unsupported layout form: `{}`", self.tn(inner)),
                            "Use a type inside the supported layout grammar.",
                        );
                        ERROR
                    }
                }
            }
        }
    }

    fn call(&mut self, e: ExprId, callee: ExprId, args: &[ExprId], span: Span, expected: Option<Ty>) -> Ty {
        let p = self.p;
        // A callee that names a local (or is not a path at all)
        // is a value call: closures and Fn-bound parameters.
        let is_value = match p.ast.expr(callee) {
            Expr::Path(segs) if segs.len() == 1 => self.lookup(segs[0].name, self.span(callee).ctxt).is_some(),
            Expr::Path(_) | Expr::QPath { .. } => false,
            _ => true,
        };
        if is_value {
            return self.value_call(e, callee, args, span);
        }
        // `std::mem::drop(value)`: move the value and drop it now.
        // A user fn or body item named `drop` shadows the prelude
        // name, so the one-segment form checks those first.
        if let Expr::Path(segs) = p.ast.expr(callee) {
            let names: Vec<&str> = segs.iter().map(|s| self.name(s.name)).collect();
            let qualified = matches!(names.as_slice(), ["std" | "core", "mem", "drop"] | ["mem", "drop"]);
            let bare = names.as_slice() == ["drop"]
                && self.binding_fn(segs[0].name).is_none()
                && self.body_item_of(segs[0].name, self.span(callee).ctxt).is_none();
            if qualified || bare {
                if args.len() != 1 {
                    self.err("L0105", span, "this function takes 1 argument but a different number was given", "Pass exactly one value.");
                    for &a in args {
                        self.expr(a, None);
                    }
                    return ERROR;
                }
                self.expr(args[0], None);
                self.reject_unsized_value(args[0]);
                self.set_res(e, Res::Builtin(Builtin::MemDrop));
                return UNIT;
            }
        }
        if let Some(align) = self.layout_of_val_callee(callee) {
            return self.layout_of_val(e, args, align, span);
        }
        let res = match p.ast.expr(callee) {
            Expr::Path(segs) if segs.len() == 1 => {
                let name = segs[0].name;
                match self.body_item_of(name, self.span(callee).ctxt) {
                    Some(crate::check::collect::BodyItem::Fn(f)) => Res::Fn(f),
                    _ => match self.binding_fn(name) {
                        Some(f) => Res::Fn(f),
                        None if name == p.known.Some => Res::OptSome,
                        None if name == p.known.Ok => Res::ResOk,
                        None if name == p.known.Err => Res::ResErr,
                        // The prelude re-exports `core::mem::drop` by
                        // this plain name (2024 prelude).
                        None if self.name(name) == "drop" => Res::Builtin(Builtin::MemDrop),
                        None if matches!(self.name(name), "size_of" | "align_of") && !segs[0].type_args().is_empty() => {
                            let align = self.name(name) == "align_of";
                            self.layout_query(&segs[0], align, span)
                        }
                        None => match self.tuple_struct_ctor(name) {
                            Some(a) => Res::Variant(a, 0),
                            None => {
                                let cs = self.span(callee);
                                self.err(
                                    "L0101",
                                    cs,
                                    format!("cannot find function `{}`", self.name(name)),
                                    "Check the spelling, or define the function.",
                                );
                                for &a in args {
                                    self.expr(a, None);
                                }
                                return ERROR;
                            }
                        },
                    },
                }
            }
            Expr::QPath { self_ty, trait_path, segs } => {
                if segs.len() == 1 {
                    let base = self.resolve_written(*self_ty);
                    let hint = if trait_path.is_empty() {
                        None
                    } else {
                        let tref = ast::TraitRefExpr { path: trait_path.clone() };
                        match self.written_trait_ref(base, &tref, span) {
                            Ok(tr) => Some(tr),
                            Err(d) => {
                                self.errs.push(d);
                                for &a in args {
                                    self.expr(a, None);
                                }
                                return ERROR;
                            }
                        }
                    };
                    if let Some(t) = self.assoc_call(e, callee, base, hint, segs[0].name, args, span) {
                        return t;
                    }
                }
                for &a in args {
                    self.expr(a, None);
                }
                self.err("L0101", span, "cannot find the associated function", "Check the trait and the name.");
                return ERROR;
            }
            Expr::Path(segs) => {
                // `T::assoc_fn(..)` on a type parameter, or `Self::f(..)`
                // in a trait default body (Self is the trait's param):
                // the trait comes from the bounds in scope here.
                let param_self = self.body_scope.self_ty.filter(|&t| matches!(self.tys.kind(t), TyKind::Param(_)));
                if segs.len() == 2
                    && let Some(base) = self
                        .body_scope
                        .param_tys
                        .iter()
                        .find(|(n, _)| *n == segs[0].name)
                        .map(|&(_, t)| t)
                        .or(if segs[0].name == p.known.self_type { param_self } else { None })
                {
                    // In an instance, the template's bound fixes the trait
                    // args (`U: From<u8>` at U = u16 calls `<u16 as
                    // From<u8>>::from`); a builtin Self's own impls can be
                    // ambiguous (`u16: From<{integer}>`).
                    let hint = self.instance_bound_ref(segs[1].name, base);
                    if let Some(t) = self.assoc_call(e, callee, base, hint, segs[1].name, args, span) {
                        return t;
                    }
                }
                // `Trait::method(self_arg, ..)`: the trait name
                // heads the path and the first argument is the
                // receiver. The Self type comes from that
                // argument (trial-checked, then rechecked by the
                // assoc call itself).
                if segs.len() == 2 && !args.is_empty() {
                    let cxr = p.gx.resolve_cx(&p.type_names, &p.aliases);
                    if let Some(tdef) = cxr.trait_by_bare_name(p.interner, segs[0].name)
                        && let Some(rec) = p.gx.index.trait_record(tdef).cloned()
                        && rec.method_by_name(segs[1].name).is_some()
                    {
                        let snap = self.snapshot_vars();
                        let obl_len = self.obl_len();
                        let sites_len = self.generic_sites.len();
                        let err_len = self.errs.len();
                        let at = self.expr(args[0], None);
                        let at = self.deep(at);
                        self.rollback_vars(snap);
                        self.obl_truncate(obl_len);
                        self.generic_sites.truncate(sites_len);
                        self.errs.truncate(err_len);
                        let mut bases = vec![at];
                        if let TyKind::Ref(_, _, inner) = self.tys.kind(at) {
                            bases.insert(0, self.deep(inner));
                        }
                        for base in bases {
                            // Written trait args (`Tr::<u8>::m(x)`) fix the
                            // trait ref, as in `<_ as Tr<u8>>::m(x)`.
                            let hint = if matches!(segs[0].args, ast::GenericArgs::Angle(_)) {
                                let tref = ast::TraitRefExpr { path: vec![segs[0].clone()] };
                                match self.written_trait_ref(base, &tref, span) {
                                    Ok(tr) => tr,
                                    Err(d) => {
                                        self.errs.push(d);
                                        for &a in args {
                                            self.expr(a, None);
                                        }
                                        return ERROR;
                                    }
                                }
                            } else {
                                let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(base)];
                                for _ in 1..rec.generics.params.len() {
                                    tr_args.push(GenericArg::Ty(self.new_var(false)));
                                }
                                let args_id = self.tys.intern_args(&tr_args);
                                TraitRef { def: tdef, args: args_id, bindings: EMPTY_BINDINGS }
                            };
                            if let Some(t) = self.assoc_call(e, callee, base, Some(hint), segs[1].name, args, span) {
                                return t;
                            }
                        }
                        if matches!(segs[0].args, ast::GenericArgs::Angle(_)) {
                            let shown = match self.tys.kind(at) {
                                TyKind::Ref(_, _, inner) => self.deep(inner),
                                _ => at,
                            };
                            let (tr_name, tn) = (self.trait_name(tdef), self.tn(shown));
                            self.err(
                                "L0612",
                                span,
                                format!("no impl of `{tr_name}` with these trait arguments for `{tn}`"),
                                "Change the trait arguments, or add the impl.",
                            );
                            for &a in args {
                                self.expr(a, None);
                            }
                            return ERROR;
                        }
                    }
                }
                // `M::from(x)`: an Adt with no variant or inherent fn of
                // that name finds it in the traits in scope (rustc
                // probes inherent items first, then traits). A call the
                // template check resolved through a trait keeps that
                // trait (`Self::mk()` in a trait default body).
                if segs.len() == 2
                    && !(segs[1].name == p.known.clone
                        && [p.known.String, p.known.Vec, p.known.Box, p.known.Rc].contains(&segs[0].name))
                    && let Some(base) = self.trait_assoc_base(segs, self.replay_pick(e).is_some(), span)
                    && let Some(t) = self.assoc_call(e, callee, base, None, segs[1].name, args, span)
                {
                    return t;
                }
                let cs = self.span(callee);
                let r = if self.is_type_id_of(segs) { self.type_id_of_path(e, segs.last().unwrap(), cs) } else { self.resolve_assoc(segs, cs) };
                match r {
                    Some(r) => r,
                    None => {
                        for &a in args {
                            self.expr(a, None);
                        }
                        return ERROR;
                    }
                }
            }
            _ => return self.value_call(e, callee, args, span),
        };
        // An indirect call's callee is a value expression with a
        // resolution of its own (a local, an index): keep it.
        if res != Res::Indirect {
            self.set_res(callee, res);
        }
        self.set_res(e, res);
        if res == Res::OptSome {
            if args.len() != 1 {
                self.err("L0105", span, "`Some` takes one argument", "Write `Some(value)`.");
                return ERROR;
            }
            // Turbofish (`Some::<u8>(..)`, `Option::<u8>::Some(..)`) fixes
            // the element type; the argument is a coercion site for it.
            if let Expr::Path(segs) = p.ast.expr(callee)
                && let Some(a) = self.builtin_ctor_args(segs, 1, span)
            {
                self.expect_expr(args[0], a[0]);
                return self.tys.mk_option(a[0]);
            }
            // Under an `Option<&dyn Tr>` expectation the argument is a
            // coercion site for `&dyn Tr`, as rustc's expected inputs make it.
            let elem = expected.and_then(|t| self.tys.option_elem(self.resolve(t)));
            if let Some(want) = elem.filter(|&t| self.dyn_ref_expectation(Some(t)).is_some()) {
                self.expect_expr(args[0], want);
                return self.tys.mk_option(want);
            }
            // A dyn deeper in (`Option<(&dyn Tr, u8)>`): the expectation
            // reaches the coercion sites inside the argument.
            let hint = elem.filter(|&t| object::mentions_dyn(&self.tys, t));
            let t = self.expr(args[0], hint);
            return self.tys.mk_option(t);
        }
        if res == Res::ResOk || res == Res::ResErr {
            let who = if res == Res::ResOk { "Ok" } else { "Err" };
            if args.len() != 1 {
                self.err("L0105", span, format!("`{who}` takes one argument"), format!("Write `{who}(value)`."));
                return ERROR;
            }
            // Turbofish on the constructor or on `Result` itself pins
            // both sides (`_` is a fresh var); otherwise the other side
            // is a fresh var.
            let turbo: Vec<Ty> = match p.ast.expr(callee) {
                Expr::Path(segs) => self.builtin_ctor_args(segs, 2, span).unwrap_or_default(),
                _ => Vec::new(),
            };
            // Under a `Result<&dyn Tr, _>` expectation the argument is a
            // coercion site, as for `Some`; a dyn deeper in gets the hint.
            let side = if turbo.len() == 2 { None } else { expected.and_then(|t| self.tys.result_args(self.resolve(t))) };
            let side = side.map(|(ok, err)| if res == Res::ResOk { ok } else { err });
            if let Some(want) = side.filter(|&t| self.dyn_ref_expectation(Some(t)).is_some()) {
                self.expect_expr(args[0], want);
                let other = self.new_var(false);
                return if res == Res::ResOk { self.tys.mk_result(want, other) } else { self.tys.mk_result(other, want) };
            }
            let (want, other) = if turbo.len() == 2 {
                if res == Res::ResOk { (Some(turbo[0]), turbo[1]) } else { (Some(turbo[1]), turbo[0]) }
            } else {
                (side.filter(|&t| object::mentions_dyn(&self.tys, t)), self.new_var(false))
            };
            let t = self.expr(args[0], want);
            return if res == Res::ResOk { self.tys.mk_result(t, other) } else { self.tys.mk_result(other, t) };
        }
        match res {
            Res::ConstUsize(_) => {
                if !args.is_empty() {
                    self.err("L0105", span, "this function takes no arguments", "Write `size_of::<Type>()`.");
                }
                USIZE
            }
            Res::Any { .. } => {
                if !args.is_empty() {
                    self.err("L0105", span, "this function takes no arguments", "Write `TypeId::of::<Type>()`.");
                }
                generics::type_id_ty(&mut self.tys)
            }
            Res::Fn(f) => {
                // Path calls such as `Type::method(x)` pass `self` explicitly, so all params apply.
                if let Some(Some(tmpl)) = p.gx.fn_templates.get(f.0 as usize).cloned() {
                    let explicit = self.explicit_call_args(callee);
                    let (mut params, ret, inst_args) = self.instantiate_template(e, f, &tmpl.generics.clone(), &explicit, span);
                    self.unify_written_self(callee, f, &inst_args, span);
                    self.normalize_params(&mut params, span);
                    self.expected_output_first(ret, expected, args);
                    self.check_args(&params, args, span);
                    return self.normalize_use(ret, span);
                }
                let (params, ret) = match p.sig_of(&mut self.out.reads, p.def_id(f)) {
                    SigOf::Fn(info) => (info.params.clone(), p.ret_view(f)),
                    _ => return ERROR,
                };
                let ret = self.callee_ret(ret);
                self.unify_written_self(callee, f, &[], span);
                self.check_args(&params, args, span);
                ret
            }
            Res::Variant(a, v) => {
                if !p.adt(a).is_enum {
                    self.check_ctor_vis(a, span);
                }
                let adef = p.def_of_adt(a);
                let _ = p.sig_of(&mut self.out.reads, adef);
                let variant = &p.adt(a).variants[v as usize];
                if variant.shape != VariantShape::Tuple {
                    self.err("L0114", span, "this variant is not a tuple variant", "Use `Type::Variant` or `Type::Variant { .. }`.");
                    return ERROR;
                }
                let n = p.gx.adt_generics[a.0 as usize].params.len();
                if n == 0 {
                    let params: Vec<Ty> = variant.fields.iter().map(|f| f.ty).collect();
                    self.check_args(&params, args, span);
                    self.tys.adt_ty(a)
                } else {
                    let gen_args: Vec<GenericArg> = match p.ast.expr(callee) {
                        Expr::Path(segs) => self.value_path_args(a, segs, span),
                        _ => self.fresh_args(&p.gx.adt_generics[a.0 as usize].clone()),
                    };
                    // The expected type fixes the params first (rustc's
                    // expected inputs), so a closure or a reference
                    // argument sees its field's type (`S<u8>(|x| ..)`).
                    if let Some(want) = expected.map(|t| self.resolve(t))
                        && self.tys.adt_parts(want).is_some_and(|(d, _)| d == adef)
                    {
                        let snap = self.snapshot_vars();
                        let mine = self.tys.mk_adt(adef, &gen_args);
                        if !self.unify(mine, want) {
                            self.rollback_vars(snap);
                        }
                    }
                    let params: Vec<Ty> = variant.fields.iter().map(|f| self.subst_norm(f.ty, &gen_args, span)).collect();
                    self.check_args(&params, args, span);
                    // Forming the type owes its parameter bounds.
                    let preds = p.gx.adt_generics[a.0 as usize].predicates.clone();
                    if !preds.is_empty() {
                        self.push_predicates(&preds, &gen_args, span);
                    }
                    self.tys.mk_adt(adef, &gen_args)
                }
            }
            Res::Indirect => {
                let ct = self.out.expr_ty[self.ei(callee)];
                match self.callable_sig(ct) {
                    Some((params, ret)) => {
                        self.check_args(&params, args, span);
                        ret
                    }
                    None => ERROR,
                }
            }
            Res::Builtin(b) => {
                // rustc's expected inputs: `Box::new(|x| ..)` (or `Rc::new`)
                // where `Box<dyn Fn(A) -> R>` is expected checks the
                // argument against the dyn type, so a closure takes that
                // signature; the box of its own type then unsizes at the
                // caller's coercion.
                if matches!(b, Builtin::BoxNew | Builtin::RcNew)
                    && args.len() == 1
                    && let Expr::Path(segs) = p.ast.expr(callee)
                    && segs[0].type_args().is_empty()
                    && let Some(want) = expected.map(|t| self.resolve(t))
                    && let Some(inner) = if b == Builtin::BoxNew { self.tys.boxed_elem(want) } else { self.tys.rc_elem(want) }
                    && matches!(self.kind(inner), TyKind::Dyn(..))
                {
                    let at = self.expr(args[0], Some(inner));
                    return if b == Builtin::BoxNew { self.tys.mk_boxed(at) } else { self.tys.mk_rc(at) };
                }
                let (params, ret): (Vec<Ty>, Ty) = match b {
                    Builtin::Sync(op) => self.sync_call_sig(op, callee, span),
                    Builtin::Clone => {
                        // The associated form `Type::clone(&x)`:
                        // the argument fixes the type.
                        let base = self.new_var(false);
                        self.deferred_clone.push((base, span));
                        let r = self.tys.mk_ref(false, base);
                        (vec![r], base)
                    }
                    Builtin::StringNew => (vec![], STRING),
                    Builtin::StringFrom => {
                        // The forms lust takes: `&str` (and `&String`
                        // through deref), a String by value, and a
                        // char. Picked from the argument's type;
                        // `check_args` then checks it as itself.
                        let at = if args.len() == 1 { self.expr(args[0], None) } else { ERROR };
                        let at = self.resolve(at);
                        if at == CHAR || at == STRING { (vec![at], STRING) } else { (vec![REF_STR], STRING) }
                    }
                    Builtin::StringWithCapacity => (vec![USIZE], STRING),
                    Builtin::EnvArgs => (vec![], ARGS),
                    Builtin::F64FromBits => (vec![int(IntTy::U64)], self.tys.float_ty(FloatTy::F64)),
                    Builtin::F32FromBits => (vec![int(IntTy::U32)], self.tys.float_ty(FloatTy::F32)),
                    Builtin::CharFromU32 => (vec![int(IntTy::U32)], self.tys.mk_option(CHAR)),
                    Builtin::CharFromDigit => (vec![int(IntTy::U32), int(IntTy::U32)], self.tys.mk_option(CHAR)),
                    Builtin::CharIsAlphabeticUnicode
                    | Builtin::CharIsNumericUnicode
                    | Builtin::CharIsAlphanumericUnicode
                    | Builtin::CharIsLowercaseUnicode
                    | Builtin::CharIsUppercaseUnicode
                    | Builtin::CharIsWhitespaceUnicode
                    | Builtin::CharIsControlUnicode => (vec![CHAR], BOOL),
                    Builtin::VecFrom => {
                        // The three forms lust takes: `&[T]` and
                        // `&[T; N]` (clone each element, exact
                        // capacity) and `[T; N]` (move each element).
                        // The argument is checked once here to pick
                        // the form; `check_args` below then checks it
                        // against its own type.
                        let at = if args.len() == 1 { self.expr(args[0], None) } else { ERROR };
                        let at = self.resolve(at);
                        let elem = match self.kind(at) {
                            TyKind::Ref(_, _, inner) => match self.kind(self.resolve(inner)) {
                                TyKind::Slice(e) | TyKind::Array(e, _) => {
                                    self.deferred_clone.push((e, span));
                                    Some(e)
                                }
                                _ => None,
                            },
                            TyKind::Array(e, _) => Some(e),
                            TyKind::Error => Some(ERROR),
                            TyKind::Infer(_) => Some(ERROR),
                            _ => None,
                        };
                        match elem {
                            Some(e) => (vec![at], self.tys.mk_vec(e)),
                            None => {
                                let tn = self.tn(at);
                                self.err(
                                    "L0110",
                                    span,
                                    format!("`Vec::from` needs a slice or an array, found `{tn}`"),
                                    "Pass `&[T]`, `&[T; N]`, or `[T; N]`.",
                                );
                                (vec![at], ERROR)
                            }
                        }
                    }
                    Builtin::BoxNew => {
                        let generics = match p.ast.expr(callee) {
                            Expr::Path(segs) => segs[0].type_args(),
                            _ => Vec::new(),
                        };
                        let elem = match generics.first() {
                            Some(&g) => self.resolve_written(g),
                            None => self.new_var(false),
                        };
                        (vec![elem], self.tys.mk_boxed(elem))
                    }
                    Builtin::BoxLeak => {
                        let elem = self.new_var(false);
                        let bx = self.tys.mk_boxed(elem);
                        let r = self.tys.mk_ref(true, elem);
                        (vec![bx], r)
                    }
                    Builtin::RcNew => {
                        let generics = match p.ast.expr(callee) {
                            Expr::Path(segs) => segs[0].type_args(),
                            _ => Vec::new(),
                        };
                        let elem = match generics.first() {
                            Some(&g) => self.resolve_written(g),
                            None => self.new_var(false),
                        };
                        (vec![elem], self.tys.mk_rc(elem))
                    }
                    Builtin::RcStrongCount | Builtin::RcWeakCount => {
                        let elem = self.new_var(false);
                        let rc = self.tys.mk_rc(elem);
                        let r = self.tys.mk_ref(false, rc);
                        (vec![r], USIZE)
                    }
                    Builtin::RcMakeMut => {
                        let elem = self.new_var(false);
                        self.deferred_sized.push((elem, span));
                        self.deferred_clone.push((elem, span));
                        let rc = self.tys.mk_rc(elem);
                        let rm = self.tys.mk_ref(true, rc);
                        let r = self.tys.mk_ref(true, elem);
                        (vec![rm], r)
                    }
                    Builtin::RcGetMut => {
                        let elem = self.new_var(false);
                        self.deferred_sized.push((elem, span));
                        let rc = self.tys.mk_rc(elem);
                        let rm = self.tys.mk_ref(true, rc);
                        let r = self.tys.mk_ref(true, elem);
                        let opt = self.tys.mk_option(r);
                        (vec![rm], opt)
                    }
                    Builtin::RcDowngrade | Builtin::RcPtrEq | Builtin::WeakNew | Builtin::WeakPtrEq | Builtin::RefCellNew | Builtin::CellNew => {
                        self.cell_call_sig(b, callee)
                    }
                    Builtin::ExitCodeFrom => (vec![int(IntTy::U8)], self.tys.exit_code_ty()),
                    Builtin::StringFromUtf8 | Builtin::StrFromUtf8 => self.utf8_call_sig(b),
                    Builtin::RcTryUnwrap => {
                        let elem = self.new_var(false);
                        self.deferred_sized.push((elem, span));
                        let rc = self.tys.mk_rc(elem);
                        let res = self.tys.mk_result(elem, rc);
                        (vec![rc], res)
                    }
                    Builtin::RcIntoInner => {
                        let elem = self.new_var(false);
                        self.deferred_sized.push((elem, span));
                        let rc = self.tys.mk_rc(elem);
                        (vec![rc], self.tys.mk_option(elem))
                    }
                    Builtin::RcUnwrapOrClone => {
                        let elem = self.new_var(false);
                        self.deferred_sized.push((elem, span));
                        let rc = self.tys.mk_rc(elem);
                        self.deferred_clone.push((elem, span));
                        (vec![rc], elem)
                    }
                    Builtin::VecNew | Builtin::VecWithCapacity => {
                        let generics = match p.ast.expr(callee) {
                            Expr::Path(segs) => segs.iter().find(|s| s.name == p.known.Vec).map(|s| s.type_args()).unwrap_or_default(),
                            _ => Vec::new(),
                        };
                        let elem = match generics.first() {
                            Some(&g) => self.resolve_written(g),
                            None => self.new_var(false),
                        };
                        let params = if b == Builtin::VecNew { vec![] } else { vec![USIZE] };
                        (params, self.tys.mk_vec(elem))
                    }
                    Builtin::MemDrop => {
                        let t = self.callee_turbo_ty(callee, span);
                        (vec![t], UNIT)
                    }
                    Builtin::MemSwap => {
                        let t = self.callee_turbo_ty(callee, span);
                        let r = self.tys.mk_ref(true, t);
                        (vec![r, r], UNIT)
                    }
                    Builtin::MemReplace => {
                        let t = self.callee_turbo_ty(callee, span);
                        let r = self.tys.mk_ref(true, t);
                        (vec![r, t], t)
                    }
                    Builtin::MemTake => {
                        let t = self.callee_turbo_ty(callee, span);
                        let r = self.tys.mk_ref(true, t);
                        (vec![r], t)
                    }
                    Builtin::CmpMax | Builtin::CmpMin => {
                        let t = self.callee_turbo_ty(callee, span);
                        (vec![t, t], t)
                    }
                    _ => unreachable!(),
                };
                self.check_args(&params, args, span);
                // `Rc::try_unwrap` needs `T: Sized` (rustc E0277), and
                // the other value-reaching Rc builtins are not built for
                // `Rc<dyn Tr>` yet; the counts are.
                if matches!(b, Builtin::RcMakeMut | Builtin::RcGetMut | Builtin::RcTryUnwrap)
                    && let Some(&pt) = params.first()
                    && let t = self.deep(pt)
                    && let Some(rc) = Some(match self.kind(t) {
                        TyKind::Ref(_, _, inner) => inner,
                        _ => t,
                    })
                    && self.tys.rc_elem(rc).is_some_and(|e| matches!(self.kind(e), TyKind::Dyn(..)))
                {
                    if b == Builtin::RcTryUnwrap {
                        self.err("L0110", span, "`Rc::try_unwrap` needs a sized value, not a `dyn` one", "Keep the `Rc<dyn Tr>` and call through it.");
                    } else {
                        self.errs.push(generics::dyn_not_yet(span, "this `Rc` function on an `Rc<dyn Tr>`"));
                    }
                    return ERROR;
                }
                if let Builtin::Sync(op) = b {
                    self.lint_atomic_ordering(op, args);
                }
                // The byte-move and scalar-cmp builtins have type
                // limits rustc states as `Sized`, `Default`, and
                // `Ord` bounds; outside the exact supported shapes
                // lust rejects (a safe false reject) instead of
                // guessing a value.
                let elem_of = |this: &mut Self, i: usize| {
                    let t = this.resolve(params[i]);
                    match this.tys.kind(t) {
                        TyKind::Ref(_, _, inner) => this.resolve(inner),
                        _ => t,
                    }
                };
                match b {
                    Builtin::MemDrop | Builtin::MemSwap | Builtin::MemReplace => {
                        // For `drop`, T is the argument itself (a
                        // reference to an unsized value is sized);
                        // for swap/replace, T sits behind the `&mut`.
                        let t = if b == Builtin::MemDrop { self.resolve(params[0]) } else { elem_of(self, 0) };
                        if matches!(self.tys.kind(t), TyKind::Slice(_) | TyKind::Str | TyKind::Dyn(..)) {
                            let tn = self.tn(t);
                            self.err(
                                "L0110",
                                span,
                                format!("the size for values of type `{tn}` cannot be known at compilation time"),
                                "Use a sized value, or move through a sized place.",
                            );
                        }
                    }
                    Builtin::MemTake => {
                        let t = elem_of(self, 0);
                        let k = self.tys.kind(t);
                        // The default glue builds any value `has_default`
                        // accepts (derived `Default` included).
                        let ok = matches!(k, TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Unit)
                            || k.is_int_infer()
                            || k.is_float_infer()
                            || (!matches!(k, TyKind::Param(_) | TyKind::Projection(..)) && has_default(self.p, &self.tys, t));
                        if ok {
                            self.record_glue_reads(self.p.gx.lang.default, t);
                        }
                        if !ok {
                            self.errs.push(unsupported(span, "`mem::take` on this type"));
                        }
                    }
                    Builtin::CmpMax | Builtin::CmpMin => {
                        let t = elem_of(self, 0);
                        let k = self.tys.kind(t);
                        if !(matches!(k, TyKind::Int(_) | TyKind::Char | TyKind::Bool) || k.is_int_infer()) {
                            self.errs.push(unsupported(span, "`cmp::max`/`cmp::min` on this type"));
                        }
                    }
                    _ => {}
                }
                ret
            }
            Res::Intrinsic(id) => {
                let def = lang::intrinsic(id);
                let params: Vec<Ty> = def.params.iter().map(|s| s.resolve(&mut self.tys)).collect();
                self.check_args(&params, args, span);
                def.ret.resolve(&mut self.tys)
            }
            _ => ERROR,
        }
    }

    fn check_args(&mut self, params: &[Ty], args: &[ExprId], span: Span) {
        if params.len() != args.len() {
            self.err(
                "L0105",
                span,
                format!("this function takes {} argument(s) but {} were given", params.len(), args.len()),
                "Pass exactly the declared arguments.",
            );
        }
        // Closure arguments check last, as rustc does: their parameter
        // types often come from the other arguments (`apply(|x| .., 5u8)`).
        for closures in [false, true] {
            for (i, &a) in args.iter().enumerate() {
                if matches!(self.p.ast.expr(a), Expr::Closure { .. }) != closures {
                    continue;
                }
                match params.get(i) {
                    Some(&pt) => {
                        self.expect_expr(a, pt);
                    }
                    None => {
                        self.expr(a, None);
                    }
                }
                self.reject_unsized_value(a);
                let at = self.out.expr_ty[self.ei(a)];
                if let TyKind::FnDef(def, _) = self.kind(self.resolve(at)) {
                    let b = self.tys.builtins();
                    if [b.option, b.result, b.boxed, b.rc].contains(&def) {
                        let sp = self.span(a);
                        self.deferred_item_args.push((at, sp));
                    }
                }
            }
        }
    }

    /// An argument moves its value, which needs a statically known size
    /// (rustc E0277): `drop(*b)` for `b: Box<dyn Tr>`.
    fn reject_unsized_value(&mut self, a: ExprId) {
        let t = self.deep(self.out.expr_ty[self.ei(a)]);
        if self.out.coerce[self.ei(a)] == Coerce::None && matches!(self.kind(t), TyKind::Dyn(..) | TyKind::Str | TyKind::Slice(_)) {
            let (tn, span) = (self.tn(t), self.span(a));
            self.err(
                "L0110",
                span,
                format!("the size for values of type `{tn}` cannot be known, so it cannot be passed by value"),
                "Pass a reference instead: `&*b`.",
            );
        }
    }

    /// The ambiguity guard of the scalar lang-method probes: a
    /// second in-scope trait with an impl of the same method name
    /// for this receiver makes the call ambiguous in rustc
    /// (E0034). Reports it and returns true. (Declining instead
    /// would let the generic search take the other trait alone:
    /// the lang candidate has no impl method fn there, so the
    /// generic search would silently accept.)
    fn prim_lang_guard(&mut self, name: Sym, name_span: Span, args: &[ExprId], trait_def: DefId, base: Ty) -> bool {
        let p = self.p;
        let others: Vec<DefId> = p
            .gx
            .traits_by_method
            .get(&name)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .filter(|&d| d != trait_def && method::trait_in_scope_pub(self, d))
            .collect();
        for other in others {
            let Some(rec) = p.gx.index.trait_record(other) else { continue };
            let snap = self.snapshot_vars();
            let obl_len = self.obl_len();
            let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(base)];
            for _ in 1..rec.generics.params.len() {
                tr_args.push(GenericArg::Ty(self.new_var(false)));
            }
            let args_id = self.tys.intern_args(&tr_args);
            let tr = TraitRef { def: other, args: args_id, bindings: EMPTY_BINDINGS };
            let hits = matches!(self.select_obligation(tr), Selection::Impl { .. } | Selection::ParamEvidence(_));
            self.rollback_vars(snap);
            self.obl_truncate(obl_len);
            if hits {
                self.err(
                    "L0720",
                    name_span,
                    format!("multiple trait methods named `{}` apply here", self.name(name)),
                    "Call the method with a fully qualified path, such as `<Type as Trait>::method(...)`.",
                );
                for &a in args {
                    self.expr(a, None);
                }
                return true;
            }
        }
        false
    }

    /// An operator trait method on a scalar receiver in method
    /// form (`a.add(b)`, `a.neg()`, `a.add_assign(b)`): the same
    /// shape as `prim_cmp_method`, through `Res::PrimOp`. The
    /// operator traits are not in the prelude, so without a pick
    /// replay the trait must be in scope, as in rustc. Operand
    /// sets are core's exactly (see the synthetic impls in
    /// `generics::add_synthetic_impls`): arithmetic on ints and
    /// floats, bit operators on ints and bool, shifts on ints
    /// with any int right side, `Neg` on signed ints and floats,
    /// `Not` on ints and bool.
    #[allow(clippy::too_many_arguments)]
    fn prim_op_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        derefs: u8,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        builtin_only: bool,
    ) -> Option<Ty> {
        if !turbofish.is_empty() {
            return None;
        }
        let p = self.p;
        let lang = &p.gx.lang;
        // `String::add(&str)`: the one non-scalar operator impl
        // with a builtin body (the same value `String + &str`
        // builds). Scope and ambiguity follow the scalar rules.
        if self.name(name) == "add" && self.tys.is_string_ty(self.resolve(base)) {
            if !builtin_only && !method::trait_in_scope_pub(self, lang.add) {
                return None;
            }
            if !builtin_only && self.prim_lang_guard(name, name_span, args, lang.add, base) {
                return Some(ERROR);
            }
            self.check_args(&[REF_STR], args, name_span);
            self.set_res(e, Res::PrimOp { kind: PrimOpKind::Bin(BinOp::Add), derefs });
            return Some(STRING);
        }
        let bk = self.kind(base);
        let intlike = matches!(bk, TyKind::Int(_)) || bk.is_int_infer();
        let floatlike = matches!(bk, TyKind::Float(_)) || bk.is_float_infer();
        let signed = matches!(bk, TyKind::Int(i) if i.signed());
        let arith = intlike || floatlike;
        let bits = intlike || matches!(bk, TyKind::Bool);
        use BinOp::*;
        use PrimOpKind as K;
        let (kind, trait_def) = match self.name(name) {
            "add" if arith => (K::Bin(Add), lang.add),
            "sub" if arith => (K::Bin(Sub), lang.sub),
            "mul" if arith => (K::Bin(Mul), lang.mul),
            "div" if arith => (K::Bin(Div), lang.div),
            "rem" if arith => (K::Bin(Rem), lang.rem),
            "bitand" if bits => (K::Bin(BitAnd), lang.bit_and),
            "bitor" if bits => (K::Bin(BitOr), lang.bit_or),
            "bitxor" if bits => (K::Bin(BitXor), lang.bit_xor),
            "shl" if intlike => (K::Bin(Shl), lang.shl),
            "shr" if intlike => (K::Bin(Shr), lang.shr),
            "neg" if floatlike || signed || bk.is_int_infer() => (K::Un(ast::UnOp::Neg), lang.neg),
            "not" if bits => (K::Un(ast::UnOp::Not), lang.not),
            "add_assign" if arith => (K::Assign(Add), lang.add_assign),
            "sub_assign" if arith => (K::Assign(Sub), lang.sub_assign),
            "mul_assign" if arith => (K::Assign(Mul), lang.mul_assign),
            "div_assign" if arith => (K::Assign(Div), lang.div_assign),
            "rem_assign" if arith => (K::Assign(Rem), lang.rem_assign),
            "bitand_assign" if bits => (K::Assign(BitAnd), lang.bit_and_assign),
            "bitor_assign" if bits => (K::Assign(BitOr), lang.bit_or_assign),
            "bitxor_assign" if bits => (K::Assign(BitXor), lang.bit_xor_assign),
            "shl_assign" if intlike => (K::Assign(Shl), lang.shl_assign),
            "shr_assign" if intlike => (K::Assign(Shr), lang.shr_assign),
            _ => return None,
        };
        if !builtin_only && !method::trait_in_scope_pub(self, trait_def) {
            return None;
        }
        if !builtin_only && self.prim_lang_guard(name, name_span, args, trait_def, base) {
            return Some(ERROR);
        }
        // An unsuffixed literal receiver of `neg` can still bind
        // to an unsigned type from context; the bound then has no
        // impl in rustc. Queue the obligation so body end (after
        // fallback settles the type) makes that call.
        if matches!(kind, K::Un(ast::UnOp::Neg)) && bk.is_int_infer() {
            let args_id = self.tys.intern_args(&[GenericArg::Ty(base)]);
            let tr = TraitRef { def: lang.neg, args: args_id, bindings: EMPTY_BINDINGS };
            self.obl.push_trait_at(tr, name_span, 0);
        }
        let ret = match kind {
            K::Bin(op) => {
                // Shifts take any int right side; the rest take Self.
                let rhs_ty = if matches!(op, Shl | Shr) { self.new_var(true) } else { base };
                self.check_args(&[rhs_ty], args, name_span);
                base
            }
            K::Un(_) => {
                self.check_args(&[], args, name_span);
                base
            }
            K::Assign(op) => {
                self.check_packed_borrow(recv, name_span);
                let rhs_ty = if matches!(op, Shl | Shr) { self.new_var(true) } else { base };
                self.check_args(&[rhs_ty], args, name_span);
                UNIT
            }
            // `prim_into_method` and `into_iter_self` build these
            // kinds, never this match.
            K::IntoCast | K::IntoIterSelf => unreachable!(),
        };
        self.set_res(e, Res::PrimOp { kind, derefs });
        Some(ret)
    }

    /// A comparison trait method on a scalar receiver in method
    /// form (`a.partial_cmp(b)`, `a.cmp(b)`, `a.eq(b)`, `a.lt(b)`,
    /// and kin): core's impls for the scalar types are the scalar
    /// comparisons themselves, so the call resolves here and
    /// lowering emits them (`Res::PrimCmp`). This is also where a
    /// template pick for one of these traits lands in an instance
    /// (`builtin_only`: the trait was fixed by the template check,
    /// so no ambiguity question is asked again). Without a pick,
    /// another in-scope trait with an impl of the same method name
    /// for this receiver makes the call ambiguous in rustc: the
    /// probe then reports the ambiguity itself.
    #[allow(clippy::too_many_arguments)]
    fn prim_cmp_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        derefs: u8,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        builtin_only: bool,
    ) -> Option<Ty> {
        if !turbofish.is_empty() {
            return None;
        }
        let p = self.p;
        let lang = &p.gx.lang;
        let bk = self.kind(base);
        let intlike = matches!(bk, TyKind::Int(_)) || bk.is_int_infer();
        let floatlike = matches!(bk, TyKind::Float(_)) || bk.is_float_infer();
        if !intlike && !floatlike && !matches!(bk, TyKind::Bool | TyKind::Char) {
            // Other types compare by structure when every part does
            // (strings, tuples, containers, derived impls): lowering
            // uses the `eq` and `cmp` glue for them.
            self.record_glue_reads(p.gx.lang.partial_eq, base);
            let ok = match self.name(name) {
                "partial_cmp" | "lt" | "le" | "gt" | "ge" => has_ord(p, &self.tys, base),
                "cmp" => has_total_ord(p, &self.tys, base),
                "eq" | "ne" => has_eq(p, &self.tys, base),
                _ => false,
            };
            if !ok || matches!(bk, TyKind::Param(_) | TyKind::Projection(..) | TyKind::Infer(_) | TyKind::Error) {
                return None;
            }
        }
        let (kind, trait_def) = match self.name(name) {
            "partial_cmp" => (PrimCmpKind::Partial(p.tys.local_adt_of(generics::ordering_def())?), lang.partial_ord),
            "cmp" if !floatlike => (PrimCmpKind::Total(p.tys.local_adt_of(generics::ordering_def())?), lang.ord),
            "eq" => (PrimCmpKind::Op(BinOp::Eq), lang.partial_eq),
            "ne" => (PrimCmpKind::Op(BinOp::Ne), lang.partial_eq),
            "lt" => (PrimCmpKind::Op(BinOp::Lt), lang.partial_ord),
            "le" => (PrimCmpKind::Op(BinOp::Le), lang.partial_ord),
            "gt" => (PrimCmpKind::Op(BinOp::Gt), lang.partial_ord),
            "ge" => (PrimCmpKind::Op(BinOp::Ge), lang.partial_ord),
            _ => return None,
        };
        if !builtin_only && self.prim_lang_guard(name, name_span, args, trait_def, base) {
            return Some(ERROR);
        }
        self.check_packed_borrow(recv, name_span);
        let other_ty = self.tys.mk_ref(false, base);
        self.check_args(&[other_ty], args, name_span);
        self.set_res(e, Res::PrimCmp { kind, derefs });
        Some(match kind {
            PrimCmpKind::Partial(_) => {
                let ord = generics::ordering_ty(&mut self.tys);
                self.tys.mk_option(ord)
            }
            PrimCmpKind::Total(_) => generics::ordering_ty(&mut self.tys),
            PrimCmpKind::Op(_) => BOOL,
        })
    }

    /// `x.into()` where the target is a scalar type core has a
    /// `From` impl for: the call is the same widening cast as
    /// `Target::from(x)` (lowered as `PrimOpKind::IntoCast`). The target must be
    /// known here (an annotation, a return type, a template
    /// replay through an `Into` bound): a target fixed only
    /// later declines to the trait search, which handles user
    /// types. A scalar target with no core impl also declines,
    /// so the plain obligation error can report.
    #[allow(clippy::too_many_arguments)]
    fn prim_into_method(
        &mut self,
        e: ExprId,
        base: Ty,
        derefs: u8,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        expected: Option<Ty>,
        builtin_only: bool,
    ) -> Option<Ty> {
        // Core's blanket `Into` applies at the first autoderef step, so
        // on a receiver reached through a deref Self is the reference
        // (or Box) type, which no scalar `From` impl takes (rustc E0277
        // for `let x: i64 = (&3i32).into()`).
        if !turbofish.is_empty() || self.name(name) != "into" || derefs > 0 {
            return None;
        }
        // An instance replays the template's `T: Into<U>` evidence, so
        // the target is known even with no expected type.
        let into = self.p.gx.lang.into;
        let replayed = self.replayed_trait_ref(e, into).and_then(|r| self.tys.args(r.args).get(1).and_then(|g| g.as_ty()));
        let dst = match replayed {
            Some(t) => t,
            None => self.deep(expected?),
        };
        let src_kind = self.kind(base);
        let dst_kind = self.kind(dst);
        if !Self::numeric_from_ok(src_kind, dst_kind) {
            return None;
        }
        // Core's set is between concrete scalar types; an
        // inference-variable side stays the trait search's call.
        if !matches!(src_kind, TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char) {
            return None;
        }
        if !builtin_only && self.prim_lang_guard(name, name_span, args, self.p.gx.lang.into, base) {
            return Some(ERROR);
        }
        self.check_args(&[], args, name_span);
        self.set_res(e, Res::PrimOp { kind: PrimOpKind::IntoCast, derefs });
        Some(dst)
    }

    /// `x.into_iter()` where `x` is an iterator (a builtin iterator, a
    /// range, a user `impl Iterator`, or `T: Iterator` in a template):
    /// core's blanket `impl<I: Iterator> IntoIterator for I` returns the
    /// receiver itself. By value only: through a deref rustc would move
    /// out of a borrow.
    fn into_iter_self(&mut self, e: ExprId, base: Ty, derefs: u8, name: Sym, args: &[ExprId], turbofish: &[ast::GenericArg]) -> Option<Ty> {
        if derefs > 0 || !args.is_empty() || !turbofish.is_empty() || self.name(name) != "into_iter" {
            return None;
        }
        let base = self.deep(base);
        if matches!(self.kind(base), TyKind::Infer(_) | TyKind::Error) {
            return None;
        }
        let args_id = self.tys.intern_args(&[GenericArg::Ty(base)]);
        let tr = TraitRef { def: self.p.gx.lang.iterator, args: args_id, bindings: EMPTY_BINDINGS };
        let snap = self.snapshot_vars();
        let is_iter = crate::ty::iter::is_iter(&self.tys, base)
            || self.tys.is_chars_ty(base)
            || matches!(self.select_obligation(tr), Selection::Impl { .. } | Selection::ParamEvidence(_));
        self.rollback_vars(snap);
        if !is_iter {
            return None;
        }
        self.set_res(e, Res::PrimOp { kind: PrimOpKind::IntoIterSelf, derefs });
        Some(base)
    }

    /// Checks a method call, walking a receiver chain (`x.m().m()...`,
    /// up to the parser's 2000-link cap) in a loop: collect the spine,
    /// run the turbofish lifetime rejects outermost first (the order
    /// the recursive walk ran them), check the base receiver, then
    /// fold `method_call_with_rt` back up. A spine of one goes through
    /// `method_call` exactly as before.
    fn method_chain(
        &mut self,
        e: ExprId,
        recv: ExprId,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        generic_args: &[ast::GenericArg],
        expected: Option<Ty>,
    ) -> Ty {
        let p = self.p;
        let mut spine: Vec<(ExprId, ExprId, Sym, Span, &[ExprId], &[ast::GenericArg])> =
            vec![(e, recv, name, name_span, args, generic_args)];
        let mut cur = recv;
        while let Expr::MethodCall { recv: r, name: n, name_span: ns, generic_args: g, args: a } = p.ast.expr(cur) {
            spine.push((cur, *r, *n, *ns, a, g));
            cur = *r;
        }
        for (_, _, n, _, a, g) in &spine {
            let seg = ast::PathSeg { name: *n, args: ast::GenericArgs::Angle(g.to_vec()) };
            self.lifetime_turbofish(std::slice::from_ref(&seg));
            // `write!` into an `io::Write` value (W-SHIM): the
            // `format_args!` argument is an `Arguments` value.
            if let [arg] = a
                && p.interner.get(*n) == "write_fmt"
                && matches!(p.ast.expr(*arg), Expr::Macro { kind: MacroKind::FormatArgs, .. })
                && p.resolved.as_ref().is_some_and(|r| r.std_platform.is_some())
            {
                self.format_args_ok.push(*arg);
            }
        }
        let writes: Vec<(ExprId, ExprId, Span)> =
            spine.iter().filter(|s| p.interner.get(s.2) == "write_fmt").map(|s| (s.0, s.1, s.3)).collect();
        let rt = if spine.len() == 1 {
            self.method_call(e, recv, name, name_span, args, generic_args, expected)
        } else {
            let mut rt = self.expr(cur, None);
            let n = spine.len();
            for (i, (node, r, nm, ns, a, g)) in spine.into_iter().rev().enumerate() {
                let outer = i + 1 == n;
                rt = self.method_call_with_rt(node, r, rt, nm, ns, a, g, if outer { expected } else { None });
                if !outer {
                    self.set(node, rt);
                }
            }
            rt
        };
        // `write!` into a user `io::Write` type (W-SHIM, check/platform.rs).
        for (node, r, ns) in writes {
            if let Res::Method { f, .. } = self.out.res(node) {
                let mut w = self.deep(self.out.ty(r));
                while let TyKind::Ref(_, _, inner) = self.kind(w) {
                    w = inner;
                }
                if let Some(d) = crate::check::platform::user_write_fmt_call(p, &self.tys, f, w, ns) {
                    self.errs.push(d);
                }
            }
        }
        rt
    }

    fn method_call(
        &mut self,
        e: ExprId,
        recv: ExprId,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        expected: Option<Ty>,
    ) -> Ty {
        let rt = self.expr(recv, None);
        self.method_call_with_rt(e, recv, rt, name, name_span, args, turbofish, expected)
    }

    /// `method_call` with the receiver already checked to type `rt`
    /// (before `deep`); `recv` is still named for the borrow and
    /// packed-field checks inside. Split out so `expr_inner` can check
    /// a method chain (`x.m().m()...`) in a loop instead of recursing
    /// down its receiver spine.
    fn method_call_with_rt(
        &mut self,
        e: ExprId,
        recv: ExprId,
        rt: Ty,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        expected: Option<Ty>,
    ) -> Ty {
        let p = self.p;
        let k = p.known;
        let rt = self.deep(rt);
        self.call_expected = expected.map(|t| (e, t));
        // ARCH 2.12 run point: a method call must know the receiver type. The
        // obligation queue runs just before that head is required (ARCH 2.4).
        self.run_obligations(false);
        // `Box` is a builtin deref step for method calls, as in
        // Rust. Its own `clone` is found before the step (it is
        // the one Box method this wave resolves at step zero),
        // so that name keeps the unpeeled receiver.
        // `Box<[T]>`'s by-value methods, found before the deref step.
        if let Some(el) = self.tys.boxed_slice_elem(self.resolve(rt)) {
            match self.name(name) {
                "into_vec" => {
                    self.set_res(e, Res::BuiltinMethod { b: Builtin::BoxSliceIntoVec, derefs: 0, autoref: Autoref::None });
                    self.check_args(&[], args, name_span);
                    return self.tys.mk_vec(el);
                }
                // Rust 2024 iterates a boxed slice by value here.
                "into_iter" => {
                    self.set_res(e, Res::BuiltinMethod { b: Builtin::BoxSliceIntoIter, derefs: 0, autoref: Autoref::None });
                    self.check_args(&[], args, name_span);
                    return crate::ty::iter::mk_iter(&mut self.tys, crate::ty::iter::IterKind::VecIntoIter, &[el]);
                }
                _ => {}
            }
        }
        let (derefs, base) = if name == k.clone {
            // A `RefCell` guard has no `clone` method of its own (only
            // the associated `Ref::clone`): the call clones the value.
            let (mut d, mut b) = self.autoderef(rt);
            while let Some((inner, _)) = self.tys.guard_elem(b) {
                let (d2, b2) = self.autoderef(self.resolve(inner));
                d += 1 + d2;
                b = b2;
            }
            (d, b)
        } else {
            self.autoderef_smart(rt)
        };
        self.check_method_vis(base, name, name_span);
        let bk = self.tys.kind(base);
        // ARCH 2.12: a method call needs a known receiver head (rustc
        // E0282, also for a closure parameter a later call would fix).
        if let TyKind::Infer(v) = bk
            && !v.is_int()
            && !v.is_float()
        {
            self.err(
                "L0610",
                name_span,
                "type annotations needed: the receiver type must be known here",
                "Annotate the receiver's type, for example the closure parameter as `|x: Vec<u8>|`.",
            );
            for &a in args {
                self.expr(a, None);
            }
            return ERROR;
        }
        // User methods, through the method-set probes of section 2.10: every
        // form is probed in order and recorded, hit or miss, before the
        // builtin compat dispatch below runs.
        let head = Head::of(&self.tys, base);
        // Turbofish args of the method (`x.m::<U>(..)`), resolved
        // in this body's scope for the generic probes below.
        let explicit: Vec<Option<GenericArg>> = turbofish
            .iter()
            .map(|a| match a {
                ast::GenericArg::Type(t) => Some(GenericArg::Ty(self.resolve_written(*t))),
                ast::GenericArg::Const(e2) => Some(self.const_call_arg(*e2)),
                _ => None,
            })
            .collect();
        // A call the template check resolved through a trait keeps
        // that trait in every other check of the body (ARCH 4.1):
        // selection on this body's Self type picks the impl, and no
        // method lookup runs again.
        let mut builtin_only = false;
        if let Some(pick) = self.replay_pick(e) {
            match picks::replay_method(self, e, rt, pick, name, name_span, args, &explicit, expected) {
                Some(ret) => return ret,
                None => builtin_only = true,
            }
        }
        // The inherent methods of `core::cmp::Ordering` (no user
        // impl can add inherent methods to it).
        if let Some(ret) = self.ordering_method(e, base, derefs, name, name_span, args) {
            return ret;
        }
        // `type_id`, `is`, and the downcasts of `core::any` (check/any.rs).
        if let Some(ret) = self.any_method(e, rt, name, name_span, args, turbofish, &explicit, expected) {
            return ret;
        }
        // Generic and trait receivers go through the full 2.10
        // search (check/method.rs), which probes plain inherent
        // methods with the same recorded reads, in step+form
        // order. Builtin and scalar receivers stay on the path
        // below.
        if p.gx.has_generics
            && !builtin_only
            && (self.tys.local_adt(base).is_some()
                || matches!(self.tys.kind(base), TyKind::Param(_) | TyKind::Projection(..) | TyKind::Dyn(..) | TyKind::Opaque(..)))
        {
            match method::generic_method_search(self, e, rt, name, name_span, args, &explicit, expected) {
                method::Probe::Hit(ret) => return ret,
                method::Probe::Failed => return ERROR,
                method::Probe::Miss => {}
            }
        }
        // Every candidate of every form, in probe order. The set
        // is keyed by the template Adt head, so a candidate only
        // counts when its receiver type unifies with this
        // receiver (a method of `impl W<u8>` does not apply to
        // `W<u32>`); templates confirm inside their probe.
        let mut assoc_fn_seen = false;
        for form in ReceiverForm::PROBE_ORDER {
            if builtin_only {
                break;
            }
            let set = p.method_set(&mut self.out.reads, head, name, form);
            for c in set.candidates {
                let Some(cform) = c.receiver else {
                    assoc_fn_seen = true;
                    continue;
                };
                let f = p.local_def(c.def.hash).expect("a method candidate names a local fn");
                if !turbofish.is_empty() && p.gx.fn_templates.get(f.0 as usize).is_none_or(|t| t.is_none()) {
                    self.errs.push(not_yet("L0721", name_span, "turbofish on method calls"));
                    for &a in args {
                        self.expr(a, None);
                    }
                    return ERROR;
                }
                // A generic inherent method: instantiate it like a
                // generic call, with the receiver unifying the impl
                // and method parameters.
                if p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
                    let probe = method::RcvProbe::at(self, base, cform);
                    match method::inherent_template_probe(self, e, probe, derefs, name, name_span, args, &explicit) {
                        method::Probe::Hit(ret) => return ret,
                        method::Probe::Failed => return ERROR,
                        method::Probe::Miss => continue,
                    }
                }
                let probe = method::RcvProbe::at(self, base, cform);
                let (params, ret) = match p.sig_of(&mut self.out.reads, c.def) {
                    SigOf::Fn(info) => (info.params.clone(), p.local_def(c.def.hash).map_or(info.ret, |f| p.ret_view(f))),
                    _ => return ERROR,
                };
                let ret = self.callee_ret(ret);
                let snap_vars = self.snapshot_vars();
                let obl_len = self.obl_len();
                if params.first().is_none_or(|&want| !self.unify(want, probe.recv_ty)) {
                    self.rollback_vars(snap_vars);
                    self.obl_truncate(obl_len);
                    // A typed receiver (`self: Box<Self>`, `self:
                    // &Rc<Self>`): it buckets as Value, so match
                    // it by its written receiver type against the
                    // unpeeled receiver (ARCH 2.10 step 3).
                    if p.fn_info(f).self_kind == Some(ast::SelfKind::Typed)
                        && let Some(&want) = params.first()
                        && let Some((td, ta)) = self.typed_receiver_adjust(rt, want)
                    {
                        if ta != Autoref::None {
                            self.check_packed_borrow(recv, name_span);
                        }
                        self.set_res(e, Res::Method { f, derefs: td, autoref: ta });
                        self.check_args(&params[1.min(params.len())..], args, name_span);
                        return ret;
                    }
                    continue;
                }
                if probe.autoref != Autoref::None {
                    self.check_packed_borrow(recv, name_span);
                }
                self.set_res(e, Res::Method { f, derefs, autoref: probe.autoref });
                self.check_args(&params[1.min(params.len())..], args, name_span);
                return ret;
            }
        }
        if assoc_fn_seen {
            self.err(
                "L0104",
                name_span,
                format!("`{}` is an associated function, not a method", self.name(name)),
                "Call it as `Type::name(...)`.",
            );
            return ERROR;
        }
        // `clone` on a reference to a non-Clone type clones the reference.
        if name == k.clone {
            if !has_clone(p, &self.tys, base) && derefs > 0 {
                self.record_glue_reads(p.gx.lang.clone, base);
                // Peel all but the last reference; the clone copies that reference.
                let mut cur = self.resolve(rt);
                for _ in 0..derefs - 1 {
                    if let TyKind::Ref(_, _, inner) = self.tys.kind(cur) {
                        cur = self.resolve(inner);
                    }
                }
                self.check_packed_borrow(recv, name_span);
                self.set_res(e, Res::BuiltinMethod { b: Builtin::Clone, derefs: derefs - 1, autoref: Autoref::Ref });
                self.check_args(&[], args, name_span);
                return cur;
            }
            if has_clone(p, &self.tys, base) {
                self.record_glue_reads(p.gx.lang.clone, base);
                self.check_packed_borrow(recv, name_span);
                self.set_res(e, Res::BuiltinMethod { b: Builtin::Clone, derefs, autoref: Autoref::Ref });
                self.check_args(&[], args, name_span);
                return base;
            }
        }
        // Comparison trait methods on a scalar receiver
        // (`partial_cmp`, `cmp`, `eq`, `lt`, and kin in method
        // form): the template side is the lang stub, the instance
        // side is the scalar comparison itself.
        if let Some(ret) = self.prim_cmp_method(e, recv, base, derefs, name, name_span, args, turbofish, builtin_only) {
            return ret;
        }
        // Operator trait methods on a scalar receiver, likewise.
        if let Some(ret) = self.prim_op_method(e, recv, base, derefs, name, name_span, args, turbofish, builtin_only) {
            return ret;
        }
        // `into()` to a scalar target core has a `From` impl for.
        if let Some(ret) = self.prim_into_method(e, base, derefs, name, name_span, args, turbofish, expected, builtin_only) {
            return ret;
        }
        // `into_iter()` on a value that is its own iterator.
        if let Some(ret) = self.into_iter_self(e, base, derefs, name, args, turbofish) {
            return ret;
        }
        // Iterator sources on sequences and every method on a builtin
        // iterator (check/iter.rs, W-STD-A).
        if let Some(ret) = self.iter_method(e, recv, rt, base, derefs, name, name_span, args, turbofish, expected) {
            return ret;
        }
        // `write!` (`write_fmt(format_args!(..))`), Formatter and builder
        // methods, and `fmt` on builtin values (check/fmt.rs, W-STD-B).
        if turbofish.is_empty() {
            if self.p.interner.get(name) == "write_fmt"
                && let Some(ret) = self.write_fmt_call(e, recv, base, derefs, name_span, args)
            {
                return ret;
            }
            if let Some(ret) = self.fmt_method(e, recv, rt, base, derefs, name, name_span, args) {
                return ret;
            }
            // AsRef, AsMut, Borrow, BorrowMut, ToOwned on builtin values
            // (check/convert.rs, W-STD-B).
            if let Some(ret) = self.convert_method(e, recv, rt, name, name_span, args, expected) {
                return ret;
            }
        }
        // `Ord::max`/`min`/`clamp` on a receiver reached through a
        // deref resolve at the first autoderef step when the receiver
        // type itself is `Ord` (`&A`, `Box<A>`): Self is that type, so
        // the arguments and the result have it too (`(&3).max(5)` is
        // rustc E0308). A user trait with a method of the name could
        // also apply there (rustc E0034); that case stays unsupported.
        if derefs > 0 && matches!(self.name(name), "max" | "min" | "clamp") && has_total_ord(p, &self.tys, rt) {
            let user_trait = p.gx.traits_by_method.get(&name).is_some_and(|ds| ds.iter().any(|&d| d != p.gx.lang.ord));
            if !user_trait && let Some(ret) = self.ord_pick_method(e, recv, rt, 0, name, name_span, args) {
                return ret;
            }
            for &a in args {
                self.expr(a, None);
            }
            self.errs.push(not_yet("L0614", name_span, "`Ord` methods on this receiver type"));
            return ERROR;
        }
        // `Weak`, `RefCell`, and `Cell` methods (check/cells.rs).
        if let Some(ret) = self.cell_method(e, recv, base, derefs, name, name_span, args) {
            return ret;
        }
        // Atomic and other sync methods (check/sync.rs).
        if let Some(ret) = self.sync_method(e, recv, base, derefs, name, name_span, args) {
            return ret;
        }
        if let Some(ret) = self.utf8_method(e, recv, base, derefs, name, name_span, args) {
            return ret;
        }
        use Builtin as B;
        // Builtin methods dispatch on the v2 builtin def in the first slot and on
        // the general kind in the second; user Adts were handled above.
        let found: Option<(B, Autoref, Vec<Ty>, Ty)> = match (self.tys.builtin_of(base), bk) {
            (Some(BuiltinTy::String), _) => {
                if name == k.len {
                    Some((B::StringLen, Autoref::Ref, vec![], USIZE))
                } else if name == k.is_empty {
                    Some((B::StringIsEmpty, Autoref::Ref, vec![], BOOL))
                } else if name == k.push_str {
                    Some((B::StringPushStr, Autoref::RefMut, vec![REF_STR], UNIT))
                } else if name == k.push {
                    Some((B::StringPush, Autoref::RefMut, vec![CHAR], UNIT))
                } else if name == k.as_str {
                    Some((B::StringAsStr, Autoref::Ref, vec![], REF_STR))
                } else if name == k.to_string {
                    Some((B::ToString, Autoref::Ref, vec![], STRING))
                } else if name == k.capacity {
                    Some((B::StringCapacity, Autoref::Ref, vec![], USIZE))
                } else if name == k.reserve {
                    Some((B::StringReserve, Autoref::RefMut, vec![USIZE], UNIT))
                } else if name == k.reserve_exact {
                    Some((B::StringReserveExact, Autoref::RefMut, vec![USIZE], UNIT))
                } else if name == k.shrink_to_fit {
                    Some((B::StringShrinkToFit, Autoref::RefMut, vec![], UNIT))
                } else if name == k.shrink_to {
                    Some((B::StringShrinkTo, Autoref::RefMut, vec![USIZE], UNIT))
                } else if name == k.pop {
                    let opt = self.tys.mk_option(CHAR);
                    Some((B::StringPop, Autoref::RefMut, vec![], opt))
                } else if name == k.remove {
                    Some((B::StringRemove, Autoref::RefMut, vec![USIZE], CHAR))
                } else if name == k.insert {
                    Some((B::StringInsert, Autoref::RefMut, vec![USIZE, CHAR], UNIT))
                } else if name == k.insert_str {
                    Some((B::StringInsertStr, Autoref::RefMut, vec![USIZE, REF_STR], UNIT))
                } else if name == k.truncate {
                    Some((B::StringTruncate, Autoref::RefMut, vec![USIZE], UNIT))
                } else if name == k.clear {
                    Some((B::StringClear, Autoref::RefMut, vec![], UNIT))
                } else if name == k.split_off {
                    Some((B::StringSplitOff, Autoref::RefMut, vec![USIZE], STRING))
                } else if name == k.as_bytes {
                    let sl = self.tys.intern(TyKind::Slice(int(IntTy::U8)));
                    let r = self.tys.mk_ref(false, sl);
                    Some((B::StringAsBytes, Autoref::Ref, vec![], r))
                } else if name == k.into_bytes {
                    let v = self.tys.mk_vec(int(IntTy::U8));
                    Some((B::StringIntoBytes, Autoref::None, vec![], v))
                } else {
                    // String derefs to str, so it has every str method.
                    self.str_method(name)
                }
            }
            (None, TyKind::Str) => {
                if name == k.len {
                    Some((B::StrLen, Autoref::Ref, vec![], USIZE))
                } else if name == k.is_empty {
                    Some((B::StrIsEmpty, Autoref::Ref, vec![], BOOL))
                } else if name == k.to_string || name == k.to_owned {
                    Some((B::StrToString, Autoref::Ref, vec![], STRING))
                } else {
                    self.str_method(name)
                }
            }
            (Some(BuiltinTy::Vec), _) => {
                let elem = self.tys.adt_first_ty_arg(base).unwrap_or(ERROR);
                // Return types are built only in the arms that return them:
                // interning has no visible effect, so the common arms skip it.
                if name == k.len {
                    Some((B::VecLen, Autoref::Ref, vec![], USIZE))
                } else if name == k.is_empty {
                    Some((B::VecIsEmpty, Autoref::Ref, vec![], BOOL))
                } else if name == k.push {
                    Some((B::VecPush, Autoref::RefMut, vec![elem], UNIT))
                } else if name == k.pop {
                    let opt = self.tys.mk_option(elem);
                    Some((B::VecPop, Autoref::RefMut, vec![], opt))
                } else if name == k.get {
                    let r = self.tys.mk_ref(false, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecGet, Autoref::Ref, vec![USIZE], opt_ref))
                } else if name == k.first {
                    let r = self.tys.mk_ref(false, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecFirst, Autoref::Ref, vec![], opt_ref))
                } else if name == k.last {
                    let r = self.tys.mk_ref(false, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecLast, Autoref::Ref, vec![], opt_ref))
                } else if name == k.contains {
                    self.deferred_eq.push((elem, name_span));
                    let r = self.tys.mk_ref(false, elem);
                    Some((B::VecContains, Autoref::Ref, vec![r], BOOL))
                } else if name == k.swap {
                    Some((B::VecSwap, Autoref::RefMut, vec![USIZE, USIZE], UNIT))
                } else if name == k.clear {
                    Some((B::VecClear, Autoref::RefMut, vec![], UNIT))
                } else if name == k.insert {
                    Some((B::VecInsert, Autoref::RefMut, vec![USIZE, elem], UNIT))
                } else if name == k.remove {
                    Some((B::VecRemove, Autoref::RefMut, vec![USIZE], elem))
                } else if name == k.truncate {
                    Some((B::VecTruncate, Autoref::RefMut, vec![USIZE], UNIT))
                } else if name == k.capacity {
                    Some((B::VecCapacity, Autoref::Ref, vec![], USIZE))
                } else if name == k.reserve {
                    Some((B::VecReserve, Autoref::RefMut, vec![USIZE], UNIT))
                } else if name == k.reserve_exact {
                    Some((B::VecReserveExact, Autoref::RefMut, vec![USIZE], UNIT))
                } else if name == k.shrink_to_fit {
                    Some((B::VecShrinkToFit, Autoref::RefMut, vec![], UNIT))
                } else if derefs == 0 && self.name(name) == "into_boxed_slice" {
                    let sl = self.tys.intern(TyKind::Slice(elem));
                    Some((B::VecIntoBoxedSlice, Autoref::None, vec![], self.tys.mk_boxed(sl)))
                } else if name == k.shrink_to {
                    Some((B::VecShrinkTo, Autoref::RefMut, vec![USIZE], UNIT))
                } else if name == k.swap_remove {
                    Some((B::VecSwapRemove, Autoref::RefMut, vec![USIZE], elem))
                } else if name == k.append {
                    let r = self.tys.mk_ref(true, base);
                    Some((B::VecAppend, Autoref::RefMut, vec![r], UNIT))
                } else if name == k.extend_from_slice {
                    self.deferred_clone.push((elem, name_span));
                    let sl = self.tys.intern(TyKind::Slice(elem));
                    let r = self.tys.mk_ref(false, sl);
                    Some((B::VecExtendFromSlice, Autoref::RefMut, vec![r], UNIT))
                } else if name == k.split_off {
                    Some((B::VecSplitOff, Autoref::RefMut, vec![USIZE], base))
                } else if name == k.resize {
                    self.deferred_clone.push((elem, name_span));
                    Some((B::VecResize, Autoref::RefMut, vec![USIZE, elem], UNIT))
                } else if name == k.dedup {
                    self.deferred_eq.push((elem, name_span));
                    Some((B::VecDedup, Autoref::RefMut, vec![], UNIT))
                } else if name == k.reverse {
                    Some((B::VecReverse, Autoref::RefMut, vec![], UNIT))
                } else if name == k.first_mut {
                    let r = self.tys.mk_ref(true, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecFirstMut, Autoref::RefMut, vec![], opt_ref))
                } else if name == k.last_mut {
                    let r = self.tys.mk_ref(true, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecLastMut, Autoref::RefMut, vec![], opt_ref))
                } else if name == k.get_mut {
                    let r = self.tys.mk_ref(true, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecGetMut, Autoref::RefMut, vec![USIZE], opt_ref))
                } else if name == k.as_slice {
                    let sl = self.tys.intern(TyKind::Slice(elem));
                    let r = self.tys.mk_ref(false, sl);
                    Some((B::VecAsSlice, Autoref::Ref, vec![], r))
                } else if name == k.as_mut_slice {
                    let sl = self.tys.intern(TyKind::Slice(elem));
                    let r = self.tys.mk_ref(true, sl);
                    Some((B::VecAsMutSlice, Autoref::RefMut, vec![], r))
                } else {
                    None
                }
            }
            (None, TyKind::Slice(_)) | (None, TyKind::Array(..)) => {
                let elem = match bk {
                    TyKind::Slice(e) | TyKind::Array(e, _) => e,
                    _ => ERROR,
                };
                if name == k.len {
                    Some((B::SliceLen, Autoref::Ref, vec![], USIZE))
                } else if name == k.is_empty {
                    Some((B::SliceIsEmpty, Autoref::Ref, vec![], BOOL))
                } else if name == k.to_vec {
                    self.deferred_clone.push((elem, name_span));
                    let v = self.tys.mk_vec(elem);
                    Some((B::SliceToVec, Autoref::Ref, vec![], v))
                } else if name == k.reverse {
                    Some((B::VecReverse, Autoref::RefMut, vec![], UNIT))
                } else if name == k.first {
                    let r = self.tys.mk_ref(false, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecFirst, Autoref::Ref, vec![], opt_ref))
                } else if name == k.last {
                    let r = self.tys.mk_ref(false, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecLast, Autoref::Ref, vec![], opt_ref))
                } else if name == k.get {
                    let r = self.tys.mk_ref(false, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecGet, Autoref::Ref, vec![USIZE], opt_ref))
                } else if name == k.first_mut {
                    let r = self.tys.mk_ref(true, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecFirstMut, Autoref::RefMut, vec![], opt_ref))
                } else if name == k.last_mut {
                    let r = self.tys.mk_ref(true, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecLastMut, Autoref::RefMut, vec![], opt_ref))
                } else if name == k.get_mut {
                    let r = self.tys.mk_ref(true, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecGetMut, Autoref::RefMut, vec![USIZE], opt_ref))
                } else if name == k.contains {
                    self.deferred_eq.push((elem, name_span));
                    let r = self.tys.mk_ref(false, elem);
                    Some((B::VecContains, Autoref::Ref, vec![r], BOOL))
                } else {
                    None
                }
            }
            (Some(BuiltinTy::Option), _) => {
                let inner = self.tys.adt_first_ty_arg(base).unwrap_or(ERROR);
                if name == k.is_some {
                    Some((B::OptIsSome, Autoref::Ref, vec![], BOOL))
                } else if name == k.is_none {
                    Some((B::OptIsNone, Autoref::Ref, vec![], BOOL))
                } else if name == k.unwrap {
                    Some((B::OptUnwrap, Autoref::None, vec![], inner))
                } else if name == k.expect {
                    Some((B::OptExpect, Autoref::None, vec![REF_STR], inner))
                } else if name == k.unwrap_or {
                    Some((B::OptUnwrapOr, Autoref::None, vec![inner], inner))
                } else if name == k.unwrap_or_default && has_default(p, &self.tys, inner) {
                    // `T: Default`: the `default` glue builds the value
                    // only on `None`.
                    self.record_glue_reads(p.gx.lang.default, inner);
                    Some((B::OptUnwrapOrDefault, Autoref::None, vec![], inner))
                } else {
                    match self.name(name) {
                        "as_ref" => {
                            let r = self.tys.mk_ref(false, inner);
                            Some((B::OptAsRef, Autoref::Ref, vec![], self.tys.mk_option(r)))
                        }
                        "as_mut" => {
                            let r = self.tys.mk_ref(true, inner);
                            Some((B::OptAsMut, Autoref::RefMut, vec![], self.tys.mk_option(r)))
                        }
                        "take" => Some((B::OptTake, Autoref::RefMut, vec![], base)),
                        "replace" => Some((B::OptReplace, Autoref::RefMut, vec![inner], base)),
                        _ => None,
                    }
                }
            }
            (Some(BuiltinTy::Result), _) => {
                let (ok, err) = self.tys.result_args(base).unwrap_or((ERROR, ERROR));
                match self.name(name) {
                    "is_ok" => Some((B::ResIsOk, Autoref::Ref, vec![], BOOL)),
                    "is_err" => Some((B::ResIsErr, Autoref::Ref, vec![], BOOL)),
                    "unwrap" | "expect" => {
                        // The panic message shows the error with Debug.
                        self.deferred_debug.push((err, name_span));
                        if name == k.unwrap { Some((B::ResUnwrap, Autoref::None, vec![], ok)) } else { Some((B::ResExpect, Autoref::None, vec![REF_STR], ok)) }
                    }
                    "unwrap_err" => {
                        self.deferred_debug.push((ok, name_span));
                        Some((B::ResUnwrapErr, Autoref::None, vec![], err))
                    }
                    "expect_err" => {
                        self.deferred_debug.push((ok, name_span));
                        Some((B::ResExpectErr, Autoref::None, vec![REF_STR], err))
                    }
                    "ok" => Some((B::ResOk, Autoref::None, vec![], self.tys.mk_option(ok))),
                    "err" => Some((B::ResErr, Autoref::None, vec![], self.tys.mk_option(err))),
                    "unwrap_or" => Some((B::ResUnwrapOr, Autoref::None, vec![ok], ok)),
                    "as_ref" | "as_mut" => {
                        let m = self.name(name) == "as_mut";
                        let (ro, re) = (self.tys.mk_ref(m, ok), self.tys.mk_ref(m, err));
                        let b = if m { B::ResAsMut } else { B::ResAsRef };
                        Some((b, if m { Autoref::RefMut } else { Autoref::Ref }, vec![], self.tys.mk_result(ro, re)))
                    }
                    _ => None,
                }
            }
            (Some(BuiltinTy::Chars), _) => {
                let opt = self.tys.mk_option(CHAR);
                if name == k.next {
                    Some((B::CharsNext, Autoref::RefMut, vec![], opt))
                } else if name == k.count {
                    Some((B::CharsCount, Autoref::None, vec![], USIZE))
                } else {
                    None
                }
            }
            (None, TyKind::Char) if name != k.to_string => {
                let b = [
                    (k.is_ascii_digit, B::CharIsDigit),
                    (k.is_ascii_alphabetic, B::CharIsAlphabetic),
                    (k.is_ascii_alphanumeric, B::CharIsAlphanumeric),
                    (k.is_ascii_whitespace, B::CharIsWhitespace),
                    (k.is_ascii_uppercase, B::CharIsUppercase),
                    (k.is_ascii_lowercase, B::CharIsLowercase),
                ];
                // The Unicode predicates take `self`, not `&self`.
                let u = [
                    (k.is_alphabetic, B::CharIsAlphabeticUnicode),
                    (k.is_numeric, B::CharIsNumericUnicode),
                    (k.is_alphanumeric, B::CharIsAlphanumericUnicode),
                    (k.is_lowercase, B::CharIsLowercaseUnicode),
                    (k.is_uppercase, B::CharIsUppercaseUnicode),
                    (k.is_whitespace, B::CharIsWhitespaceUnicode),
                    (k.is_control, B::CharIsControlUnicode),
                ];
                if let Some(&(_, b)) = u.iter().find(|(n, _)| *n == name) {
                    Some((b, Autoref::None, vec![], BOOL))
                } else if let Some(&(_, b)) = b.iter().find(|(n, _)| *n == name) {
                    Some((b, Autoref::Ref, vec![], BOOL))
                } else if name == k.to_ascii_uppercase {
                    Some((B::CharToUppercase, Autoref::Ref, vec![], CHAR))
                } else if name == k.to_ascii_lowercase {
                    Some((B::CharToLowercase, Autoref::Ref, vec![], CHAR))
                } else if name == k.to_digit {
                    let o = self.tys.mk_option(int(IntTy::U32));
                    Some((B::CharToDigit, Autoref::None, vec![int(IntTy::U32)], o))
                } else if name == k.is_digit {
                    Some((B::CharIsDigitRadix, Autoref::None, vec![int(IntTy::U32)], BOOL))
                } else if name == k.len_utf8 {
                    Some((B::CharLenUtf8, Autoref::None, vec![], USIZE))
                } else if name == k.len_utf16 {
                    Some((B::CharLenUtf16, Autoref::None, vec![], USIZE))
                } else if name == k.is_ascii {
                    Some((B::CharIsAscii, Autoref::Ref, vec![], BOOL))
                } else if name == k.is_ascii_punctuation {
                    Some((B::CharIsAsciiPunctuation, Autoref::Ref, vec![], BOOL))
                } else if name == k.is_ascii_graphic {
                    Some((B::CharIsAsciiGraphic, Autoref::Ref, vec![], BOOL))
                } else if name == k.is_ascii_hexdigit {
                    Some((B::CharIsAsciiHexdigit, Autoref::Ref, vec![], BOOL))
                } else if name == k.is_ascii_control {
                    Some((B::CharIsAsciiControl, Autoref::Ref, vec![], BOOL))
                } else {
                    None
                }
            }
            (None, TyKind::Int(i)) => self.int_method(name, base, i),
            (None, TyKind::Float(f)) => self.float_method(name, base, f),
            // A float of unknown width: float-returning methods return
            // the variable itself, so a later use can still settle it.
            (None, k2) if k2.is_float_infer() => self.float_method(name, base, FloatTy::F64),
            (None, TyKind::Bool | TyKind::Char) if name == k.to_string => Some((B::ToString, Autoref::Ref, vec![], STRING)),
            (Some(BuiltinTy::Args), _) if name == k.count => Some((B::ArgsCount, Autoref::None, vec![], USIZE)),
            // Trait methods work on an integer of unknown type; inherent ones (pow, abs) do not.
            (None, k2) if k2.is_int_infer() && name == k.min => Some((B::Min, Autoref::None, vec![base], base)),
            (None, k2) if k2.is_int_infer() && name == k.max => Some((B::Max, Autoref::None, vec![base], base)),
            (None, k2) if k2.is_int_infer() && name == k.to_string => Some((B::ToString, Autoref::Ref, vec![], STRING)),
            (None, k2) if k2.is_int_infer() => {
                // A trait method still applies: selection fixes the
                // integer type when exactly one impl matches, as in
                // rustc. Inherent integer methods need the type.
                if p.gx.has_generics && !builtin_only {
                    match method::generic_method_search(self, e, rt, name, name_span, args, &explicit, expected) {
                        method::Probe::Hit(ret) => return ret,
                        method::Probe::Failed => return ERROR,
                        method::Probe::Miss => {}
                    }
                }
                // `Ord::clamp` holds for every integer type.
                if self.name(name) == "clamp"
                    && let Some(ret) = self.ord_pick_method(e, recv, base, derefs, name, name_span, args)
                {
                    return ret;
                }
                self.err(
                    "L0111",
                    name_span,
                    format!("cannot call method `{}` on an integer whose type is not known yet", self.name(name)),
                    "Add a type suffix such as `5i64`, or a type annotation on the variable.",
                );
                return ERROR;
            }
            (_, TyKind::Error) => return ERROR,
            _ => None,
        };
        match found {
            Some((b, autoref, params, ret)) => {
                if autoref != Autoref::None {
                    self.check_packed_borrow(recv, name_span);
                }
                // `to_string` binds Self where rustc's probe does: the
                // first step whose `&Self` is the receiver (one reference
                // peeled), else the receiver by autoref. Self picks the
                // capacity rule (W-STD-B): `&&u8` is the generic path.
                let derefs = if b == B::ToString { u8::from(matches!(self.tys.kind(rt), TyKind::Ref(..))) } else { derefs };
                self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
                self.check_args(&params, args, name_span);
                ret
            }
            None => {
                // Generic and trait methods over the full autoderef
                // chain (check/method.rs).
                if p.gx.has_generics && !builtin_only {
                    match method::generic_method_search(self, e, rt, name, name_span, args, &explicit, expected) {
                        method::Probe::Hit(ret) => return ret,
                        method::Probe::Failed => return ERROR,
                        method::Probe::Miss => {}
                    }
                }
                if let Some(ret) = self.lang_default_method(e, recv, base, derefs, name, name_span, args) {
                    return ret;
                }
                if let Some(ret) = self.method_via_user_deref(e, recv, base, derefs, name, name_span, args, turbofish, expected) {
                    return ret;
                }
                for &a in args {
                    self.expr(a, None);
                }
                let tn = self.tn(base);
                self.err(
                    "L0104",
                    name_span,
                    format!("no method `{}` on type `{tn}`", self.name(name)),
                    "Check the method name. The prototype supports a small std subset (see README).",
                );
                ERROR
            }
        }
    }

    /// Inherent integer methods (`checked_add`, `count_ones`, and kin).
    /// All take the receiver by value. The 128-bit checked, saturating,
    /// and overflowing families (plus euclid division) are not
    /// implemented yet and answer None, like a missing method.
    fn int_method(&mut self, name: Sym, t: Ty, i: IntTy) -> Option<(Builtin, Autoref, Vec<Ty>, Ty)> {
        use Builtin as B;
        let k = self.p.known;
        let s = i.signed();
        let w128 = i.bits() >= 128;
        let u32t = int(IntTy::U32);
        let bin = |b: Builtin| Some((b, Autoref::None, vec![t], t));
        let chk = |b: Builtin, cx: &mut Self| {
            let o = cx.tys.mk_option(t);
            Some((b, Autoref::None, vec![t], o))
        };
        let ovf = |b: Builtin, cx: &mut Self| {
            let ts = cx.tys.intern_tys(&[t, BOOL]);
            let tt = cx.tys.intern(TyKind::Tuple(ts));
            Some((b, Autoref::None, vec![t], tt))
        };
        let sh = |b: Builtin| Some((b, Autoref::None, vec![u32t], t));
        let un = |b: Builtin| Some((b, Autoref::None, vec![], t));
        let n = name;
        // The families that stay within the value (wrapping and plain).
        if n == k.wrapping_add {
            return bin(B::WrappingAdd);
        }
        if n == k.wrapping_sub {
            return bin(B::WrappingSub);
        }
        if n == k.wrapping_mul {
            return bin(B::WrappingMul);
        }
        if n == k.wrapping_div && !w128 {
            return bin(B::WrappingDiv);
        }
        if n == k.wrapping_rem && !w128 {
            return bin(B::WrappingRem);
        }
        if n == k.wrapping_neg {
            return un(B::WrappingNeg);
        }
        if n == k.wrapping_pow && !w128 {
            return sh(B::WrappingPow);
        }
        if n == k.wrapping_shl {
            return sh(B::WrappingShl);
        }
        if n == k.wrapping_shr {
            return sh(B::WrappingShr);
        }
        if n == k.wrapping_abs && s {
            return un(B::WrappingAbs);
        }
        if n == k.abs && s {
            return un(B::Abs);
        }
        if n == k.pow {
            return sh(B::Pow);
        }
        if n == k.min {
            return bin(B::Min);
        }
        if n == k.max {
            return bin(B::Max);
        }
        if n == k.div_euclid && !w128 {
            return bin(B::DivEuclid);
        }
        if n == k.rem_euclid && !w128 {
            return bin(B::RemEuclid);
        }
        if n == k.signum && s {
            return un(B::Signum);
        }
        if n == k.is_positive && s {
            return Some((B::IsPositive, Autoref::None, vec![], BOOL));
        }
        if n == k.is_negative && s {
            return Some((B::IsNegative, Autoref::None, vec![], BOOL));
        }
        if n == k.is_power_of_two && !s {
            return Some((B::IsPowerOfTwo, Autoref::None, vec![], BOOL));
        }
        if n == k.count_ones {
            return Some((B::CountOnes, Autoref::None, vec![], u32t));
        }
        if n == k.count_zeros {
            return Some((B::CountZeros, Autoref::None, vec![], u32t));
        }
        if n == k.leading_zeros {
            return Some((B::LeadingZeros, Autoref::None, vec![], u32t));
        }
        if n == k.trailing_zeros {
            return Some((B::TrailingZeros, Autoref::None, vec![], u32t));
        }
        if n == k.leading_ones {
            return Some((B::LeadingOnes, Autoref::None, vec![], u32t));
        }
        if n == k.trailing_ones {
            return Some((B::TrailingOnes, Autoref::None, vec![], u32t));
        }
        if n == k.rotate_left {
            return sh(B::RotateLeft);
        }
        if n == k.rotate_right {
            return sh(B::RotateRight);
        }
        if n == k.swap_bytes {
            return un(B::SwapBytes);
        }
        if n == k.reverse_bits {
            return un(B::ReverseBits);
        }
        if n == k.to_string {
            return Some((B::ToString, Autoref::Ref, vec![], STRING));
        }
        if w128 {
            return None;
        }
        // Checked, saturating, and overflowing families (64-bit and below).
        if n == k.checked_add {
            return chk(B::CheckedAdd, self);
        }
        if n == k.checked_sub {
            return chk(B::CheckedSub, self);
        }
        if n == k.checked_mul {
            return chk(B::CheckedMul, self);
        }
        if n == k.checked_div {
            return chk(B::CheckedDiv, self);
        }
        if n == k.checked_rem {
            return chk(B::CheckedRem, self);
        }
        if n == k.checked_neg {
            let o = self.tys.mk_option(t);
            return Some((B::CheckedNeg, Autoref::None, vec![], o));
        }
        if n == k.checked_abs && s {
            let o = self.tys.mk_option(t);
            return Some((B::CheckedAbs, Autoref::None, vec![], o));
        }
        if n == k.checked_pow {
            let o = self.tys.mk_option(t);
            return Some((B::CheckedPow, Autoref::None, vec![u32t], o));
        }
        if n == k.checked_shl {
            let o = self.tys.mk_option(t);
            return Some((B::CheckedShl, Autoref::None, vec![u32t], o));
        }
        if n == k.checked_shr {
            let o = self.tys.mk_option(t);
            return Some((B::CheckedShr, Autoref::None, vec![u32t], o));
        }
        if n == k.saturating_add {
            return bin(B::SaturatingAdd);
        }
        if n == k.saturating_sub {
            return bin(B::SaturatingSub);
        }
        if n == k.saturating_mul {
            return bin(B::SaturatingMul);
        }
        if n == k.saturating_div {
            return bin(B::SaturatingDiv);
        }
        if n == k.saturating_neg && s {
            return un(B::SaturatingNeg);
        }
        if n == k.saturating_abs && s {
            return un(B::SaturatingAbs);
        }
        if n == k.saturating_pow {
            return sh(B::SaturatingPow);
        }
        if n == k.overflowing_add {
            return ovf(B::OverflowingAdd, self);
        }
        if n == k.overflowing_sub {
            return ovf(B::OverflowingSub, self);
        }
        if n == k.overflowing_mul {
            return ovf(B::OverflowingMul, self);
        }
        if n == k.overflowing_div {
            return ovf(B::OverflowingDiv, self);
        }
        if n == k.overflowing_rem {
            return ovf(B::OverflowingRem, self);
        }
        if n == k.overflowing_neg {
            let ts = self.tys.intern_tys(&[t, BOOL]);
            let tt = self.tys.intern(TyKind::Tuple(ts));
            return Some((B::OverflowingNeg, Autoref::None, vec![], tt));
        }
        if n == k.overflowing_abs && s {
            let ts = self.tys.intern_tys(&[t, BOOL]);
            let tt = self.tys.intern(TyKind::Tuple(ts));
            return Some((B::OverflowingAbs, Autoref::None, vec![], tt));
        }
        if n == k.overflowing_pow {
            let ts = self.tys.intern_tys(&[t, BOOL]);
            let tt = self.tys.intern(TyKind::Tuple(ts));
            return Some((B::OverflowingPow, Autoref::None, vec![u32t], tt));
        }
        if n == k.overflowing_shl {
            let ts = self.tys.intern_tys(&[t, BOOL]);
            let tt = self.tys.intern(TyKind::Tuple(ts));
            return Some((B::OverflowingShl, Autoref::None, vec![u32t], tt));
        }
        if n == k.overflowing_shr {
            let ts = self.tys.intern_tys(&[t, BOOL]);
            let tt = self.tys.intern(TyKind::Tuple(ts));
            return Some((B::OverflowingShr, Autoref::None, vec![u32t], tt));
        }
        None
    }

    /// Inherent float methods (`sqrt`, `powi`, `to_bits`, and kin).
    /// `t` is the receiver type (a float variable for an unsuffixed
    /// literal), `f` its width when known (f64 for a variable).
    fn float_method(&mut self, name: Sym, t: Ty, f: FloatTy) -> Option<(Builtin, Autoref, Vec<Ty>, Ty)> {
        use Builtin as B;
        let k = self.p.known;
        let un = |b: Builtin| Some((b, Autoref::None, vec![], t));
        let n = name;
        if n == k.sqrt {
            return un(B::FloatSqrt);
        }
        if n == k.abs {
            return un(B::FloatAbs);
        }
        if n == k.floor {
            return un(B::FloatFloor);
        }
        if n == k.ceil {
            return un(B::FloatCeil);
        }
        if n == k.round {
            return un(B::FloatRound);
        }
        if n == k.trunc {
            return un(B::FloatTrunc);
        }
        if n == k.fract {
            return un(B::FloatFract);
        }
        if n == k.signum {
            return un(B::FloatSignum);
        }
        if n == k.recip {
            return un(B::FloatRecip);
        }
        if n == k.exp {
            return un(B::FloatExp);
        }
        if n == k.ln {
            return un(B::FloatLn);
        }
        if n == k.log2 {
            return un(B::FloatLog2);
        }
        if n == k.log10 {
            return un(B::FloatLog10);
        }
        if n == k.powi {
            return Some((B::FloatPowi, Autoref::None, vec![int(IntTy::I32)], t));
        }
        if n == k.powf {
            return Some((B::FloatPowf, Autoref::None, vec![t], t));
        }
        if n == k.log {
            return Some((B::FloatLog, Autoref::None, vec![t], t));
        }
        if n == k.mul_add {
            return Some((B::FloatMulAdd, Autoref::None, vec![t, t], t));
        }
        if n == k.min {
            return Some((B::FloatMin, Autoref::None, vec![t], t));
        }
        if n == k.max {
            return Some((B::FloatMax, Autoref::None, vec![t], t));
        }
        if n == k.copysign {
            return Some((B::FloatCopysign, Autoref::None, vec![t], t));
        }
        if n == k.is_nan {
            return Some((B::FloatIsNan, Autoref::None, vec![], BOOL));
        }
        if n == k.is_infinite {
            return Some((B::FloatIsInfinite, Autoref::None, vec![], BOOL));
        }
        if n == k.is_finite {
            return Some((B::FloatIsFinite, Autoref::None, vec![], BOOL));
        }
        if n == k.is_sign_positive {
            return Some((B::FloatIsSignPositive, Autoref::None, vec![], BOOL));
        }
        if n == k.is_sign_negative {
            return Some((B::FloatIsSignNegative, Autoref::None, vec![], BOOL));
        }
        if n == k.to_bits {
            let bt = int(if f == FloatTy::F32 { IntTy::U32 } else { IntTy::U64 });
            return Some((B::FloatToBits, Autoref::None, vec![], bt));
        }
        if n == k.to_string {
            return Some((B::ToString, Autoref::Ref, vec![], STRING));
        }
        None
    }

    /// For `String == &str` style comparisons between different string types: the deref counts
    /// that reach each side's `String` or `str`. None if the types are not a valid mixed pair.
    fn mixed_string_eq(&self, a: Ty, b: Ty) -> Option<(u8, u8)> {
        let (ld, lb) = self.autoderef(a);
        let (rd, rb) = self.autoderef(b);
        let stringy = |t: Ty| self.tys.kind(t) == TyKind::Str || self.tys.is_string_ty(t);
        if lb == rb || !stringy(lb) || !stringy(rb) {
            return None;
        }
        string_eq_ok(ld, self.tys.is_string_ty(lb), rd, self.tys.is_string_ty(rb)).then_some((ld, rd))
    }

    /// Methods shared by `str` and `String` (through Deref). The receiver is always `&self`.
    fn str_method(&mut self, name: Sym) -> Option<(Builtin, Autoref, Vec<Ty>, Ty)> {
        use Builtin as B;
        let k = self.p.known;
        let chars = CHARS;
        let opt_str = self.tys.mk_option(REF_STR);
        let table = [
            (k.contains, B::StrContains, vec![REF_STR], BOOL),
            (k.starts_with, B::StrStartsWith, vec![REF_STR], BOOL),
            (k.ends_with, B::StrEndsWith, vec![REF_STR], BOOL),
            (k.trim, B::StrTrim, vec![], REF_STR),
            (k.to_uppercase, B::StrToUppercase, vec![], STRING),
            (k.to_lowercase, B::StrToLowercase, vec![], STRING),
            (k.chars, B::StrChars, vec![], chars),
            (k.strip_prefix, B::StrStripPrefix, vec![REF_STR], opt_str),
            (k.strip_suffix, B::StrStripSuffix, vec![REF_STR], opt_str),
            (k.trim_start, B::StrTrimStart, vec![], REF_STR),
            (k.trim_end, B::StrTrimEnd, vec![], REF_STR),
            (k.replace, B::StrReplace, vec![REF_STR, REF_STR], STRING),
            (k.repeat, B::StrRepeat, vec![USIZE], STRING),
            (k.is_char_boundary, B::StrIsCharBoundary, vec![USIZE], BOOL),
        ];
        table.into_iter().find(|(n, ..)| *n == name).map(|(_, b, params, ret)| (b, Autoref::Ref, params, ret))
    }

    /// One binary operator through its operator trait, with the
    /// result type normalized through `Output`. None when no
    /// impl applies (the caller reports the plain operator error).
    fn trait_binop(&mut self, e: ExprId, op: BinOp, li: Ty, ri: Ty, ld: u8, rd: u8, span: Span) -> Option<Ty> {
        use BinOp::*;
        let p = self.p;
        if !p.gx.has_generics {
            return None;
        }
        let lang = &p.gx.lang;
        let (trait_def, method_name) = match op {
            Add => (lang.add, "add"),
            Sub => (lang.sub, "sub"),
            Mul => (lang.mul, "mul"),
            Div => (lang.div, "div"),
            Rem => (lang.rem, "rem"),
            BitAnd => (lang.bit_and, "bitand"),
            BitOr => (lang.bit_or, "bitor"),
            BitXor => (lang.bit_xor, "bitxor"),
            Shl => (lang.shl, "shl"),
            Shr => (lang.shr, "shr"),
            _ => return None,
        };
        let out_var = self.new_var(false);
        let args_id = self.tys.intern_args(&[GenericArg::Ty(li), GenericArg::Ty(ri)]);
        let bindings = match lang.output_of(trait_def) {
            Some(assoc) => self.tys.intern_bindings(&[(assoc, GenericArg::Ty(out_var))]),
            None => EMPTY_BINDINGS,
        };
        let tr = TraitRef { def: trait_def, args: args_id, bindings };
        self.replay_operands(e, trait_def, &[li, ri]);
        let (id, impl_args) = match self.select_obligation(tr) {
            Selection::Impl { id, args, .. } => (id, args),
            Selection::ParamEvidence(i) => {
                self.record_pick_env(e, trait_def, 0, ReceiverForm::Value, Some(i));
                // A template check: the bound proves the operator. The
                // call is the trait method's stub; the result is the
                // bound's `Output`, or its rigid projection.
                let method_def = p.gx.index.trait_record(trait_def)?.method_by_name(p.interner.intern(method_name))?;
                let stub = *p.gx.trait_method_stubs.get(&method_def)?;
                if let Some(assoc) = lang.output_of(trait_def) {
                    let proj = self.tys.intern(TyKind::Projection(AssocId(assoc), args_id));
                    let normed = self.normalize_here(proj);
                    self.unify(out_var, normed);
                }
                self.set_res(e, Res::TraitBin { f: stub, ld, rd });
                return Some(self.normalize_here(out_var));
            }
            _ => return None,
        };
        let local = self.method_instance_for_impl(e, id, tr, impl_args, method_name, span)?;
        // The selected method's receiver and rhs are unified by
        // selection's probe through the trait ref above; record
        // the call for lowering.
        self.set_res(e, Res::TraitBin { f: local.0, ld, rd });
        Some(self.normalize_here(out_var))
    }

    /// A comparison operator through a written `PartialEq` or
    /// `PartialOrd` impl (`l` and `r` are the operand types with the
    /// same number of references peeled, as core's reference impls
    /// forward): records `Res::TraitCmp`. None when no written impl
    /// or bound applies; derived and core impls compare by structure
    /// (`has_eq`, `has_ord`) before this runs.
    #[allow(clippy::too_many_arguments)]
    fn trait_cmp(&mut self, e: ExprId, op: BinOp, l: Ty, r: Ty, ld: u8, rd: u8, span: Span) -> Option<Ty> {
        let lang = &self.p.gx.lang;
        let trait_def = if matches!(op, BinOp::Eq | BinOp::Ne) { lang.partial_eq } else { lang.partial_ord };
        let (f, via) = self.written_cmp_method(e, trait_def, op, l, r, span)?;
        self.set_res(e, Res::TraitCmp { f, ld, rd, via });
        Some(BOOL)
    }

    /// The method that answers comparison `op` between `l` and `r`
    /// through `trait_def` (`PartialEq` or `PartialOrd`): a written
    /// impl's own method for the operator, else the method core's
    /// default body calls (`eq` for `ne`, `partial_cmp` for `lt` and
    /// kin); in a template, the bound's stub. None for derived and
    /// core impls (they compare by structure) and when nothing applies.
    fn written_cmp_method(&mut self, e: ExprId, trait_def: DefId, op: BinOp, l: Ty, r: Ty, span: Span) -> Option<(LocalDefId, CmpVia)> {
        use crate::traits::index::Synthetic;
        let p = self.p;
        let direct = match op {
            BinOp::Eq => "eq",
            BinOp::Ne => "ne",
            BinOp::Lt => "lt",
            BinOp::Le => "le",
            BinOp::Gt => "gt",
            _ => "ge",
        };
        let args_id = self.tys.intern_args(&[GenericArg::Ty(l), GenericArg::Ty(r)]);
        let tr = TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS };
        self.replay_operands(e, trait_def, &[l, r]);
        match self.select_obligation_at(tr, span, 0) {
            Selection::Impl { id, args: impl_args, .. } => {
                let rec = p.gx.index.get(id).clone();
                if rec.synthetic != Synthetic::None {
                    return None;
                }
                let has = |n: &str| rec.items.iter().any(|d| p.local_def(d.hash).is_some_and(|f| p.name(p.fn_info(f).name) == n));
                let (method, via) = if has(direct) {
                    (direct, CmpVia::Direct)
                } else if op == BinOp::Ne {
                    ("eq", CmpVia::NotEq)
                } else if op == BinOp::Eq {
                    return None;
                } else {
                    ("partial_cmp", CmpVia::Partial(op))
                };
                let (f, _, _) = self.method_instance_for_impl(e, id, tr, impl_args, method, span)?;
                Some((f, via))
            }
            Selection::ParamEvidence(i) if i != usize::MAX => {
                let method_def = p.gx.index.trait_record(trait_def)?.method_by_name(p.interner.intern(direct))?;
                let stub = *p.gx.trait_method_stubs.get(&method_def)?;
                self.record_pick_env(e, trait_def, 0, ReceiverForm::Value, Some(i));
                Some((stub, CmpVia::Direct))
            }
            _ => None,
        }
    }

    /// Core's default bodies of the comparison traits, for a method
    /// call no impl method answers: `ne` through `eq` and `lt`/`le`/
    /// `gt`/`ge` through `partial_cmp` of a written impl
    /// (`Res::TraitCmpMethod`), and `Ord::max`/`min`/`clamp`
    /// (`Res::OrdPick`), which compare with Self's `PartialOrd`. None
    /// when another form or no impl applies (the caller reports the
    /// missing method). `base` is the receiver after `derefs` derefs.
    #[allow(clippy::too_many_arguments)]
    fn lang_default_method(&mut self, e: ExprId, recv: ExprId, base: Ty, derefs: u8, name: Sym, name_span: Span, args: &[ExprId]) -> Option<Ty> {
        let p = self.p;
        let lang = p.gx.lang;
        let op = match self.name(name) {
            "ne" => BinOp::Ne,
            "lt" => BinOp::Lt,
            "le" => BinOp::Le,
            "gt" => BinOp::Gt,
            "ge" => BinOp::Ge,
            "max" | "min" | "clamp" => return self.ord_pick_method(e, recv, base, derefs, name, name_span, args),
            _ => return None,
        };
        if args.len() != 1 || matches!(self.kind(base), TyKind::Param(_) | TyKind::Projection(..) | TyKind::Infer(_) | TyKind::Error) {
            return None;
        }
        // The argument is `&Rhs`: its type names Rhs.
        let at = self.expr(args[0], None);
        let at = self.deep(at);
        let TyKind::Ref(_, _, rhs) = self.kind(at) else { return None };
        let rhs = self.deep(rhs);
        let trait_def = if op == BinOp::Ne { lang.partial_eq } else { lang.partial_ord };
        let (f, via) = self.written_cmp_method(e, trait_def, op, base, rhs, name_span)?;
        let want = self.tys.mk_ref(false, rhs);
        self.coerce_expr(args[0], at, want);
        self.check_packed_borrow(recv, name_span);
        self.set_res(e, Res::TraitCmpMethod { f, derefs, via });
        Some(BOOL)
    }

    /// The inherent methods of `core::cmp::Ordering` lust computes in
    /// lowering (`Res::OrderingOp`): `is_eq`, `is_ne`, `is_lt`,
    /// `is_gt`, `is_le`, `is_ge`, `reverse`, and `then`. All take
    /// `self` by value (`Ordering` is `Copy`). None for another
    /// receiver, a user type named `Ordering`, or another name.
    fn ordering_method(&mut self, e: ExprId, base: Ty, derefs: u8, name: Sym, name_span: Span, args: &[ExprId]) -> Option<Ty> {
        if self.tys.adt_parts(base).map(|(d, _)| d) != Some(generics::ordering_def()) {
            return None;
        }
        use OrderingOpKind as K;
        let kind = match self.name(name) {
            "is_eq" => K::IsEq,
            "is_ne" => K::IsNe,
            "is_lt" => K::IsLt,
            "is_gt" => K::IsGt,
            "is_le" => K::IsLe,
            "is_ge" => K::IsGe,
            "reverse" => K::Reverse,
            "then" => K::Then,
            "then_with" => K::ThenWith,
            _ => return None,
        };
        // A local trait method of the same name could apply to a
        // reference receiver first, by rustc's probe order; that
        // mix is not supported (a reject, never a guess).
        let p = self.p;
        if p.gx.traits_by_method.get(&name).is_some_and(|ts| ts.iter().any(|t| p.gx.index.trait_record(*t).is_some_and(|r| r.local))) {
            for &a in args {
                self.expr(a, None);
            }
            self.errs.push(not_yet("L0720", name_span, "a local trait method named like an `Ordering` method"));
            return Some(ERROR);
        }
        let (params, ret) = match kind {
            K::Reverse => (vec![], base),
            K::Then => (vec![base], base),
            // `F: FnOnce() -> Ordering`; lowering calls closures only.
            K::ThenWith => {
                let lang = p.gx.lang;
                let f = self.new_var(false);
                let unit_args = self.tys.intern_tys(&[]);
                let unit = self.tys.intern(TyKind::Tuple(unit_args));
                let args_id = self.tys.intern_args(&[GenericArg::Ty(f), GenericArg::Ty(unit)]);
                self.obl.push(obligations::Obligation::Trait {
                    trait_ref: TraitRef { def: lang.fn_once, args: args_id, bindings: EMPTY_BINDINGS },
                    span: name_span,
                    depth: 0,
                });
                if let Some(out) = lang.output_of(lang.fn_once) {
                    self.obl.push(obligations::Obligation::AssocEq { eq: AssocEqData { assoc: out, trait_args: args_id, ty: base }, span: name_span });
                }
                (vec![f], base)
            }
            _ => (vec![], BOOL),
        };
        self.check_args(&params, args, name_span);
        if kind == K::ThenWith
            && let Some(&f) = params.first()
        {
            let at = self.deep(f);
            if !matches!(self.kind(at), TyKind::Closure(..) | TyKind::Error | TyKind::Infer(_)) {
                self.errs.push(not_yet("L0820", name_span, "`then_with` with an argument other than a closure"));
                return Some(ERROR);
            }
        }
        self.set_res(e, Res::OrderingOp { kind, derefs });
        Some(ret)
    }

    /// `Ord::max`, `min`, and `clamp` by core's default bodies
    /// (`Res::OrdPick`): Self must be `Ord`; the bodies compare with
    /// `PartialOrd::lt` (`clamp`: `le`, `lt`, `gt`) on Self, through a
    /// written impl's method or by structure. A written impl that
    /// replaces several of those methods is not supported for
    /// `clamp`. The receiver must be the value itself (no autoderef:
    /// core's `Ord for &A` would answer a reference receiver).
    #[allow(clippy::too_many_arguments)]
    fn ord_pick_method(&mut self, e: ExprId, recv: ExprId, base: Ty, derefs: u8, name: Sym, name_span: Span, args: &[ExprId]) -> Option<Ty> {
        use crate::traits::index::Synthetic;
        let p = self.p;
        let lang = p.gx.lang;
        let kind = match self.name(name) {
            "max" => OrdPickKind::Max,
            "min" => OrdPickKind::Min,
            _ => OrdPickKind::Clamp,
        };
        let n_args = if kind == OrdPickKind::Clamp { 2 } else { 1 };
        let bk = self.kind(base);
        let int_var = bk.is_int_infer();
        if derefs != 0
            || args.len() != n_args
            || (!int_var && matches!(bk, TyKind::Param(_) | TyKind::Projection(..) | TyKind::Infer(_) | TyKind::Error))
        {
            return None;
        }
        let _ = recv;
        // An integer variable is `Ord` at every type it can take.
        let ord_args = self.tys.intern_args(&[GenericArg::Ty(base)]);
        let ord_tr = TraitRef { def: lang.ord, args: ord_args, bindings: EMPTY_BINDINGS };
        if !int_var && !matches!(self.select_obligation_at(ord_tr, name_span, 0), Selection::Impl { .. } | Selection::ParamEvidence(_)) {
            return None;
        }
        self.record_glue_reads(lang.partial_ord, base);
        let (f, via) = if has_ord(p, &self.tys, base) {
            (None, CmpVia::Partial(BinOp::Lt))
        } else {
            let po_args = self.tys.intern_args(&[GenericArg::Ty(base), GenericArg::Ty(base)]);
            let po = TraitRef { def: lang.partial_ord, args: po_args, bindings: EMPTY_BINDINGS };
            let Selection::Impl { id, args: impl_args, .. } = self.select_obligation_at(po, name_span, 0) else { return None };
            let rec = p.gx.index.get(id).clone();
            if rec.synthetic != Synthetic::None {
                return None;
            }
            let has = |n: &str| rec.items.iter().any(|d| p.local_def(d.hash).is_some_and(|f| p.name(p.fn_info(f).name) == n));
            let (method, via) = if kind == OrdPickKind::Clamp {
                if ["lt", "le", "gt", "ge"].iter().any(|m| has(m)) {
                    return None;
                }
                ("partial_cmp", CmpVia::Partial(BinOp::Lt))
            } else if has("lt") {
                ("lt", CmpVia::Direct)
            } else {
                ("partial_cmp", CmpVia::Partial(BinOp::Lt))
            };
            let (f, _, _) = self.method_instance_for_impl(e, id, po, impl_args, method, name_span)?;
            (Some(f), via)
        };
        let params = vec![base; n_args];
        self.check_args(&params, args, name_span);
        self.set_res(e, Res::OrdPick { kind, f, via });
        Some(base)
    }

    /// One unary operator through its operator trait, like
    /// `trait_binop` with no right side. The result type is the
    /// bound's `Output`, normalized.
    fn trait_unop(&mut self, e: ExprId, op: ast::UnOp, inner: Ty, ld: u8, span: Span) -> Option<Ty> {
        let p = self.p;
        if !p.gx.has_generics {
            return None;
        }
        let lang = &p.gx.lang;
        let (trait_def, method_name) = match op {
            ast::UnOp::Neg => (lang.neg, "neg"),
            ast::UnOp::Not => (lang.not, "not"),
        };
        let out_var = self.new_var(false);
        let args_id = self.tys.intern_args(&[GenericArg::Ty(inner)]);
        let bindings = match lang.output_of(trait_def) {
            Some(assoc) => self.tys.intern_bindings(&[(assoc, GenericArg::Ty(out_var))]),
            None => EMPTY_BINDINGS,
        };
        let tr = TraitRef { def: trait_def, args: args_id, bindings };
        let (id, impl_args) = match self.select_obligation(tr) {
            Selection::Impl { id, args, .. } => (id, args),
            Selection::ParamEvidence(_) => {
                let method_def = p.gx.index.trait_record(trait_def)?.method_by_name(p.interner.intern(method_name))?;
                let stub = *p.gx.trait_method_stubs.get(&method_def)?;
                if let Some(assoc) = lang.output_of(trait_def) {
                    let proj = self.tys.intern(TyKind::Projection(AssocId(assoc), args_id));
                    let normed = self.normalize_here(proj);
                    self.unify(out_var, normed);
                }
                self.set_res(e, Res::TraitBin { f: stub, ld, rd: 0 });
                return Some(self.normalize_here(out_var));
            }
            _ => return None,
        };
        let local = self.method_instance_for_impl(e, id, tr, impl_args, method_name, span)?;
        self.set_res(e, Res::TraitBin { f: local.0, ld, rd: 0 });
        Some(self.normalize_here(out_var))
    }

    /// One compound assignment through its assignment trait
    /// (`a += b` as `AddAssign::add_assign(&mut a, b)`). True
    /// when the trait path applies; the call is recorded as a
    /// `TraitBin` like the binary operators.
    fn trait_assign_op(&mut self, e: ExprId, op: BinOp, lt: Ty, rinner: Ty, rd: u8, span: Span) -> bool {
        use BinOp::*;
        let p = self.p;
        if !p.gx.has_generics {
            return false;
        }
        let lang = &p.gx.lang;
        let (trait_def, method_name) = match op {
            Add => (lang.add_assign, "add_assign"),
            Sub => (lang.sub_assign, "sub_assign"),
            Mul => (lang.mul_assign, "mul_assign"),
            Div => (lang.div_assign, "div_assign"),
            Rem => (lang.rem_assign, "rem_assign"),
            BitAnd => (lang.bit_and_assign, "bitand_assign"),
            BitOr => (lang.bit_or_assign, "bitor_assign"),
            BitXor => (lang.bit_xor_assign, "bitxor_assign"),
            Shl => (lang.shl_assign, "shl_assign"),
            Shr => (lang.shr_assign, "shr_assign"),
            _ => return false,
        };
        let args_id = self.tys.intern_args(&[GenericArg::Ty(lt), GenericArg::Ty(rinner)]);
        let tr = TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS };
        self.replay_operands(e, trait_def, &[lt, rinner]);
        let local = match self.select_obligation(tr) {
            Selection::Impl { id, args, .. } => self.method_instance_for_impl(e, id, tr, args, method_name, span).map(|l| l.0),
            Selection::ParamEvidence(i) => {
                self.record_pick_env(e, trait_def, 0, ReceiverForm::Value, Some(i));
                let method_def = p.gx.index.trait_record(trait_def).and_then(|r| r.method_by_name(p.interner.intern(method_name)));
                method_def.and_then(|m| p.gx.trait_method_stubs.get(&m).copied())
            }
            _ => None,
        };
        match local {
            Some(f) => {
                self.set_res(e, Res::TraitBin { f, ld: 0, rd });
                true
            }
            None => false,
        }
    }

    /// Checks a binary expression, walking a left-leaning chain of
    /// non-`&&`/`||` operators (`a + b + c + ...`, up to the parser's
    /// 2000-term cap) in a loop: collect the left spine, check its
    /// base, then fold `binary_with_lt` back up. A spine of one, and
    /// `&&`/`||` (whose operands check against `bool`, not against
    /// each other), go through `binary` exactly as before.
    fn binary_chain(&mut self, e: ExprId, op: BinOp, lhs: ExprId, rhs: ExprId, span: Span) -> Ty {
        use BinOp::*;
        if matches!(op, And | Or) {
            return self.binary(e, op, lhs, rhs, span);
        }
        let p = self.p;
        let mut spine: Vec<(ExprId, BinOp, ExprId, Span)> = vec![(e, op, rhs, span)];
        let mut cur = lhs;
        while let Expr::Binary { op: o, lhs: l, rhs: r } = p.ast.expr(cur) {
            if matches!(o, And | Or) {
                break;
            }
            spine.push((cur, *o, *r, self.span(cur)));
            cur = *l;
        }
        if spine.len() == 1 {
            return self.binary(e, op, lhs, rhs, span);
        }
        let mut lt = self.expr(cur, None);
        let n = spine.len();
        for (i, (node, o, r, sp)) in spine.into_iter().rev().enumerate() {
            lt = self.binary_with_lt(node, o, lt, r, sp);
            // The outermost node's type is set by `expr` on return,
            // as `expr_inner` results always are; inner spine nodes
            // were set by the recursive `expr(lhs)` call they replace.
            if i + 1 < n {
                self.set(node, lt);
            }
        }
        lt
    }

    fn binary(&mut self, e: ExprId, op: BinOp, lhs: ExprId, rhs: ExprId, span: Span) -> Ty {
        use BinOp::*;
        if matches!(op, And | Or) {
            self.expect_expr(lhs, BOOL);
            self.expect_expr(rhs, BOOL);
            return BOOL;
        }
        let lt = self.expr(lhs, None);
        self.binary_with_lt(e, op, lt, rhs, span)
    }

    /// `binary` for a non-`&&`/`||` operator whose left operand type
    /// `lt` is already checked. Split out so `expr_inner` can check a
    /// left-leaning operator chain (`a + b + c + ...`) in a loop
    /// instead of recursing down its left spine.
    fn binary_with_lt(&mut self, e: ExprId, op: BinOp, lt: Ty, rhs: ExprId, span: Span) -> Ty {
        use BinOp::*;
        debug_assert!(!matches!(op, And | Or));
        let rt = self.expr(rhs, Some(lt));
        // ARCH 2.12 run point: an operator on a non-scalar must know the left
        // operand type. The scalar path above and below needs no trait search.
        self.run_obligations(false);
        self.replay_pick_operands(e, &[lt, rt]);
        let (lk, rk) = (self.kind(lt), self.kind(rt));
        if lk == TyKind::Error || rk == TyKind::Error {
            return if op.is_cmp() { BOOL } else { ERROR };
        }
        let bad = |cx: &mut Self| {
            let (a, b) = (cx.tn(lt), cx.tn(rt));
            let fix = if op.is_cmp() && (a.starts_with('&') != b.starts_with('&')) {
                "Compare values of the same type: dereference the reference with `*`, or borrow the other side."
            } else {
                "Both operands must have the same type, and the type must support this operator."
            };
            cx.err("L0113", span, format!("cannot apply `{}` to `{a}` and `{b}`", op.symbol()), fix);
            if op.is_cmp() { BOOL } else { ERROR }
        };
        // Both operand types still open (closure parameters a later
        // call fixes, `|a, b| a + b`): assume the builtin scalar
        // operator (Rhs = Self), check at body end that the types are
        // scalar, and take the result from the operator's `Output`
        // as rustc's `Op<Rhs>` selection does (see the int arm below).
        if self.unbound_general(lt) && self.unbound_general(rt) {
            if !self.unify(lt, rt) {
                return bad(self);
            }
            self.open_binops.push((e, op, lt));
            self.set_res(e, Res::Bin { ld: 0, rd: 0 });
            if op.is_cmp() {
                return BOOL;
            }
            let lang = &self.p.gx.lang;
            let tr = match op {
                Add => lang.add,
                Sub => lang.sub,
                Mul => lang.mul,
                Div => lang.div,
                Rem => lang.rem,
                BitAnd => lang.bit_and,
                BitOr => lang.bit_or,
                BitXor => lang.bit_xor,
                Shl => lang.shl,
                _ => lang.shr,
            };
            let out = self.new_var(false);
            if let Some(assoc) = lang.output_of(tr) {
                let trait_args = self.tys.intern_args(&[GenericArg::Ty(lt), GenericArg::Ty(rt)]);
                self.obl.push(obligations::Obligation::AssocEq { eq: AssocEqData { assoc, trait_args, ty: out }, span });
            }
            return out;
        }
        if op.is_cmp() {
            // String equality across String and &str.
            let (ld, lb) = self.autoderef(lt);
            let (rd, rb) = self.autoderef(rt);
            let stringy = |t: Ty| self.tys.kind(t) == TyKind::Str || self.tys.is_string_ty(t);
            if stringy(lb) && stringy(rb) && matches!(op, Eq | Ne) {
                if !string_eq_ok(ld, self.tys.is_string_ty(lb), rd, self.tys.is_string_ty(rb)) {
                    return bad(self);
                }
                self.set_res(e, Res::Bin { ld, rd });
                return BOOL;
            }
            // Equality allows `&T` against `&mut T`; ordering needs the same mutability.
            if !matches!(op, Eq | Ne) && self.ref_layers(lt) != self.ref_layers(rt) {
                return bad(self);
            }
            if ld != rd {
                return bad(self);
            }
            let snap = self.snapshot_vars();
            if !self.unify(lb, rb) {
                // Operands of two types compare only through a
                // written impl (`impl PartialEq<u8> for P`).
                self.rollback_vars(snap);
                let (lb, rb) = (self.deep(lb), self.deep(rb));
                if let Some(t) = self.trait_cmp(e, op, lb, rb, ld, rd, span) {
                    return t;
                }
                return bad(self);
            }
            let lb = self.deep(lb);
            let ok = match self.tys.kind(lb) {
                TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Str => true,
                k if k.is_int_infer() || k.is_float_infer() || self.tys.is_string_ty(lb) => true,
                _ if matches!(op, Eq | Ne) => has_eq(self.p, &self.tys, lb),
                _ => has_ord(self.p, &self.tys, lb),
            };
            if !ok && let Some(t) = self.trait_cmp(e, op, lb, lb, ld, rd, span) {
                return t;
            }
            // A structural answer depends on derives and on the written
            // `eq` impls the glue calls: both are in the Adt layouts read.
            if ok {
                self.record_glue_reads(self.p.gx.lang.partial_eq, lb);
            }
            if !ok {
                let tn = self.tn(lb);
                let fix = if matches!(op, Eq | Ne) {
                    "Add #[derive(PartialEq)] to the type."
                } else {
                    "Add #[derive(PartialOrd)] to the type, or implement `PartialOrd` for it."
                };
                self.err("L0112", span, format!("type `{tn}` cannot be compared with `{}`", op.symbol()), fix);
            }
            self.set_res(e, Res::Bin { ld, rd });
            return BOOL;
        }
        // String + &str.
        if op == Add && self.tys.is_string_ty(self.resolve(lt)) {
            self.coerce_expr(rhs, rt, REF_STR);
            self.set_res(e, Res::Bin { ld: 0, rd: 0 });
            return STRING;
        }
        // Arithmetic and bit operations exist for `&T` operands, but not for `&mut T`.
        if matches!(lk, TyKind::Ref(_, Mut::Mut, _)) || matches!(rk, TyKind::Ref(_, Mut::Mut, _)) {
            return bad(self);
        }
        let (ld, li) = self.peel_one_ref(lt);
        let (rd, ri) = self.peel_one_ref(rt);
        let (lik, rik) = (self.kind(li), self.kind(ri));
        let int_like = |k: TyKind| matches!(k, TyKind::Int(_)) || k.is_int_infer();
        // Operator traits on non-scalars (section 2.5): the
        // builtin scalar path above stays first, as ARCH requires.
        // A scalar left side with a user type on the right (`2 * v`
        // through `impl Mul<V> for i32`) also goes through the trait.
        let user_rhs = self.tys.local_adt(self.resolve(ri)).is_some();
        if (user_rhs || (!int_like(lik) && !matches!(lik, TyKind::Bool)))
            && let Some(t) = self.trait_binop(e, op, lt, rt, 0, 0, span)
        {
            return t;
        }
        let result = match op {
            Add | Sub | Mul | Div | Rem
                if (matches!(lik, TyKind::Float(_)) || lik.is_float_infer())
                    && (matches!(rik, TyKind::Float(_)) || rik.is_float_infer()) =>
            {
                if !self.unify(li, ri) {
                    return bad(self);
                }
                li
            }
            Shl | Shr if int_like(lik) && int_like(rik) => li,
            BitAnd | BitOr | BitXor if lik == TyKind::Bool && rik == TyKind::Bool => BOOL,
            // One concrete int side fixes an unbound variable on
            // the other: scalar `Add` (and friends) have
            // Rhs = Self, Output = Self, so this is the same
            // binding the trait impl would make. Closure
            // signature inference depends on it.
            Add | Sub | Mul | Div | Rem | BitAnd | BitOr | BitXor
                if (int_like(lik) && (int_like(rik) || matches!(rik, TyKind::Infer(_))))
                    || (int_like(rik) && matches!(lik, TyKind::Infer(_))) =>
            {
                let general = |k: TyKind| matches!(k, TyKind::Infer(v) if !v.is_int() && !v.is_float());
                // A second check of a closure body (`deferred_closures`)
                // sees the operand fixed by then; rustc checks the body
                // once, so an operator deferred there stays deferred.
                let deferred = general(lik) || general(rik) || self.deferred_binops.contains(&e);
                if deferred && !self.deferred_binops.contains(&e) {
                    self.deferred_binops.push(e);
                }
                if !self.unify(li, ri) {
                    return bad(self);
                }
                if deferred {
                    // An operand that is a general variable (a closure
                    // parameter not known yet): rustc resolves the
                    // operator through `Op<Rhs>` selection, so the
                    // result is that impl's `Output`, known once the
                    // operand is (after literal fallback at the
                    // latest), not the operand itself. `|x| x + 1`
                    // called with a literal into a `u64` is then
                    // `i32 + i32`: a mismatch (rustc E0271).
                    let lang = &self.p.gx.lang;
                    let tr = match op {
                        Add => lang.add,
                        Sub => lang.sub,
                        Mul => lang.mul,
                        Div => lang.div,
                        Rem => lang.rem,
                        BitAnd => lang.bit_and,
                        BitOr => lang.bit_or,
                        _ => lang.bit_xor,
                    };
                    let out = self.new_var(false);
                    if let Some(assoc) = lang.output_of(tr) {
                        let trait_args = self.tys.intern_args(&[GenericArg::Ty(li), GenericArg::Ty(ri)]);
                        self.obl.push(obligations::Obligation::AssocEq { eq: AssocEqData { assoc, trait_args, ty: out }, span });
                    }
                    out
                } else {
                    li
                }
            }
            _ => return bad(self),
        };
        self.set_res(e, Res::Bin { ld, rd });
        result
    }

    fn struct_lit(
        &mut self,
        e: ExprId,
        path: &[ast::PathSeg],
        fields: &[(Sym, Span, ExprId)],
        update: Option<ExprId>,
        span: Span,
        expected: Option<Ty>,
    ) -> Ty {
        let p = self.p;
        let target = if path.len() == 1 {
            let n = path[0].name;
            // The flat type table answers below; the binding query is the
            // recorded read of that answer (ARCH 8.2).
            if n != p.known.self_type {
                self.binding(Namespace::Type, n);
            }
            let a = if n == p.known.self_type { self.self_adt() } else { p.type_names.get(&n).copied() };
            let a = a.or_else(|| self.alias_adt(n).map(|(a, _)| a));
            match a.filter(|&a| !p.adt(a).is_enum).map(|a| (a, 0u32)) {
                Some(v) => Some(v),
                // An imported struct-like variant (`use E::*; C { .. }`).
                None => match self.pat_ident(n) {
                    PatIdent::Variant(a, v) => Some((a, v)),
                    _ => None,
                },
            }
        } else {
            match self.resolve_assoc(path, span) {
                Some(Res::Variant(a, v)) => Some((a, v)),
                _ => return ERROR,
            }
        };
        let Some((a, v)) = target else {
            for &(_, _, fe) in fields {
                self.expr(fe, None);
            }
            if let Some(u) = update {
                self.expr(u, None);
            }
            self.err("L0102", span, "unknown struct", "Check the struct name.");
            return ERROR;
        };
        self.set_res(e, Res::Variant(a, v));
        // A generic Adt literal instantiates its parameters from any
        // turbofish (with defaults) and the written fields: field types
        // are the template's, substituted with those args.
        let gen_args: Vec<GenericArg> = self.value_path_args(a, path, span);
        // An expectation that names dyn types (`W<&dyn Tr>`) fixes the
        // params first, so the fields become coercion sites for them,
        // as rustc's expected inputs make them (ARCH 2.8).
        if !gen_args.is_empty()
            && let Some(want) = expected.map(|t| self.deep(t))
            && let Some((def, eargs)) = self.tys.adt_parts(want)
            && def == p.gx.adt_info[a.0 as usize].0
            && object::mentions_dyn(&self.tys, want)
        {
            let eargs: Vec<GenericArg> = self.tys.args(eargs).to_vec();
            for (g, w) in gen_args.iter().zip(eargs) {
                if let (GenericArg::Ty(x), GenericArg::Ty(y)) = (*g, w) {
                    self.unify(x, y);
                }
            }
        }
        let variant = &p.adt(a).variants[v as usize];
        // Tuple structs take index fields here (`T { 0: 5, ..a }`); their
        // field names are the index as a synthetic Sym, so the matching
        // below works for both shapes.
        if !matches!(variant.shape, VariantShape::Named | VariantShape::Tuple) && !(variant.fields.is_empty() && fields.is_empty()) {
            self.err("L0110", span, "this is not a struct with named fields", "Use the tuple or unit form.");
            return ERROR;
        }
        let mut seen = vec![false; variant.fields.len()];
        for &(fname, fspan, fe) in fields {
            match variant.fields.iter().position(|f| f.name == fname) {
                Some(i) => {
                    if seen[i] {
                        self.err("L0106", fspan, format!("field `{}` is set twice", self.name(fname)), "Remove one of them.");
                    }
                    seen[i] = true;
                    self.check_field_vis(a, fname, fspan);
                    let want = if gen_args.is_empty() { variant.fields[i].ty } else { self.subst_norm(variant.fields[i].ty, &gen_args, fspan) };
                    self.expect_expr(fe, want);
                }
                None => {
                    self.expr(fe, None);
                    self.err("L0103", fspan, format!("no field `{}` on this struct", self.name(fname)), "Check the field name.");
                }
            }
        }
        // Struct update: the fields not written come from the base value.
        if let Some(u) = update {
            if self.is_rest_elem(u) {
                self.set(u, ERROR);
                self.err("L0110", self.span(u), "base expression required after `..`", "Add the value to fill the rest from, as in `..base`.");
                return ERROR;
            }
            if p.adt(a).is_enum {
                self.expr(u, None);
                self.err("L0110", span, "functional record update syntax requires a struct", "Set every field of the variant.");
                return ERROR;
            }
            // A field filled from the base must be visible here too
            // (rustc E0451): building a value with a private field from
            // another module is not allowed even by moving it through.
            for (i, f) in variant.fields.iter().enumerate() {
                if !seen[i] {
                    if variant.shape == VariantShape::Tuple {
                        self.check_tuple_field_vis(a, i as u32, span);
                    } else {
                        self.check_field_vis(a, f.name, span);
                    }
                }
            }
            let at = self.tys.adt_ty(a);
            self.expect_expr(u, at);
            return at;
        }
        let missing: Vec<String> =
            variant.fields.iter().zip(&seen).filter(|(_, s)| !**s).map(|(f, _)| self.name(f.name).to_string()).collect();
        if !missing.is_empty() {
            self.err(
                "L0107",
                span,
                format!("missing fields: {}", missing.join(", ")),
                "Set every field, or fill the rest from another value with `..base`.",
            );
        }
        // Forming the type owes its parameter bounds.
        if !gen_args.is_empty() {
            let preds = p.gx.adt_generics[a.0 as usize].predicates.clone();
            if !preds.is_empty() {
                self.push_predicates(&preds, &gen_args, span);
            }
        }
        if gen_args.is_empty() {
            self.tys.adt_ty(a)
        } else {
            let (def, _) = p.gx.adt_info[a.0 as usize];
            self.tys.mk_adt(def, &gen_args)
        }
    }

    fn for_iter(&mut self, for_e: ExprId, iter: ExprId) -> Ty {
        let p = self.p;
        if let Expr::Range { lo, hi, .. } = p.ast.expr(iter) {
            let (Some(lo), Some(hi)) = (*lo, *hi) else {
                let s = self.span(iter);
                self.errs.push(unsupported(s, "open ranges"));
                return ERROR;
            };
            let lt = self.expr(lo, None);
            let ht = self.expr(hi, Some(lt));
            let ok = (matches!(self.kind(lt), TyKind::Int(_)) || self.kind(lt).is_int_infer()) && self.unify(lt, ht);
            if !ok {
                let s = self.span(iter);
                let (a, b) = (self.tn(lt), self.tn(ht));
                self.err(
                    "L0110",
                    s,
                    format!("range bounds must be the same integer type, found `{a}` and `{b}`"),
                    "Use integers of one type.",
                );
            }
            self.set(iter, ERROR);
            return lt;
        }
        let t = self.expr(iter, None);
        match self.kind(t) {
            _ if self.tys.is_chars_ty(self.resolve(t)) => CHAR,
            _ if crate::ty::iter::is_iter(&self.tys, self.resolve(t)) => {
                let r = self.deep(t);
                crate::ty::iter::item_ty(&mut self.tys, r).unwrap_or(ERROR)
            }
            TyKind::Ref(r, m, inner) => {
                let elem = match self.kind(self.resolve(inner)) {
                    TyKind::Slice(elem) | TyKind::Array(elem, _) => Some(elem),
                    _ => self.tys.vec_elem(self.resolve(inner)),
                };
                match elem {
                    Some(elem) => self.tys.intern(TyKind::Ref(r, m, elem)),
                    None if self.recv_elem(t).is_some() => self.recv_elem(t).unwrap_or(ERROR),
                    None => {
                        let s = self.span(iter);
                        let tn = self.tn(t);
                        self.err("L0113", s, format!("cannot iterate over `{tn}`"), "Iterate over a range, `&vec`, or `&mut vec`.");
                        ERROR
                    }
                }
            }
            TyKind::Array(elem, _) => elem,
            _ if self.tys.vec_elem(self.resolve(t)).is_some() => self.tys.vec_elem(self.resolve(t)).unwrap_or(ERROR),
            // `for x in rx` and `for x in &rx` over an mpsc receiver
            // (W-THREADS): `recv` until every sender is gone.
            _ if self.recv_elem(t).is_some() => self.recv_elem(t).unwrap_or(ERROR),
            // A boxed slice by value (Rust 2024): its `vec::IntoIter`.
            _ if self.tys.boxed_slice_elem(self.resolve(t)).is_some() => self.tys.boxed_slice_elem(self.resolve(t)).unwrap_or(ERROR),
            TyKind::Error => ERROR,
            _ => match self.for_trait_iter(for_e, iter, t) {
                Some(item) => item,
                None => {
                    let s = self.span(iter);
                    let tn = self.tn(t);
                    self.err("L0113", s, format!("cannot iterate over `{tn}`"), "Iterate over a range, `&vec`, or `&mut vec`.");
                    ERROR
                }
            },
        }
    }

    /// A `for` loop through `IntoIterator` (section 2.4 in a
    /// loop head): select the impl, record the two method
    /// instances lowering calls, and answer the item type.
    fn for_trait_iter(&mut self, for_e: ExprId, iter: ExprId, t: Ty) -> Option<Ty> {
        let p = self.p;
        if !p.gx.has_generics {
            return None;
        }
        self.run_obligations(false);
        let span = self.span(iter);
        let args_id = self.tys.intern_args(&[GenericArg::Ty(t)]);
        let tr = TraitRef { def: p.gx.lang.into_iterator, args: args_id, bindings: EMPTY_BINDINGS };
        let lang = &p.gx.lang;
        // The into_iter call: an impl's method, the std blanket's
        // sentinel (no body: lowering uses the receiver as its own
        // iterator), or in a template check the bound's stub.
        let into_sel = self.select_obligation(tr);
        let into_from_env = matches!(into_sel, Selection::ParamEvidence(_));
        let into_local = match into_sel {
            Selection::Impl { id, args: impl_args, .. } => {
                let rec = p.gx.index.get(id);
                // core's synthetic collection impls (`Vec<T>`, `&[T]`)
                // keep their builtin loop; only the blanket over an
                // iterator uses the receiver as its own iterator.
                if rec.items.is_empty() && !matches!(p.tys.kind(rec.self_ty(&p.tys)), TyKind::Param(_)) {
                    return None;
                }
                if rec.items.is_empty() {
                    LocalDefId(u32::MAX)
                } else {
                    self.method_instance_for_impl(for_e, id, tr, impl_args, "into_iter", span)?.0
                }
            }
            Selection::ParamEvidence(_) => self.stub_instance(for_e, tr, p.interner.intern("into_iter"), span)?.0,
            _ => return None,
        };
        // The iterator type and item type, normalized.
        let into_iter_proj = self.tys.intern(TyKind::Projection(AssocId(lang.assoc_into_iter), args_id));
        let iter_ty = self.normalize_here(into_iter_proj);
        let item_proj = self.tys.intern(TyKind::Projection(AssocId(lang.assoc_into_item), args_id));
        let item_ty = self.normalize_here(item_proj);
        // next() on the iterator type.
        let iter_args_id = self.tys.intern_args(&[GenericArg::Ty(iter_ty)]);
        let tr2 = TraitRef { def: lang.iterator, args: iter_args_id, bindings: EMPTY_BINDINGS };
        let next_local = match self.select_obligation(tr2) {
            Selection::Impl { id: id2, args: impl_args2, .. } => self.method_instance_for_impl(iter, id2, tr2, impl_args2, "next", span)?.0,
            Selection::ParamEvidence(_) => self.stub_instance(iter, tr2, p.interner.intern("next"), span)?.0,
            // A template bound `T: IntoIterator` proves into_iter from
            // the env, but no env predicate states `Iterator` for the
            // `IntoIter` projection (assoc-type bounds of a trait
            // definition are not elaborated into the env). The bound
            // still proves `next` exists, so the stub answers here;
            // instances re-select with concrete types.
            _ if into_from_env => self.stub_instance(iter, tr2, p.interner.intern("next"), span)?.0,
            _ => return None,
        };
        self.set_res(for_e, Res::ForTrait { into_iter: into_local, next: next_local });
        Some(item_ty)
    }

    /// The method template of one selected impl by name,
    /// instantiated at the impl's args and recorded as an
    /// instance request at `site`. Trait defaults answer when
    /// the impl does not write the method.
    fn method_instance_for_impl(
        &mut self,
        site: ExprId,
        impl_id: crate::traits::ImplId,
        tr: TraitRef,
        impl_args: Vec<GenericArg>,
        name: &str,
        span: Span,
    ) -> Option<(LocalDefId, Vec<Ty>, Ty)> {
        let p = self.p;
        let record = p.gx.index.get(impl_id).clone();
        let local = record.items.iter().copied().find_map(|d| p.local_def(d.hash).filter(|&l| p.name(p.fn_info(l).name) == name)).or_else(
            || {
                // The trait default, materialized from its template
                // with the trait ref args as its prefix.
                let rec = p.gx.index.trait_record(record.trait_def)?;
                let name_sym = rec.methods.iter().find(|(_, n)| p.name(*n) == name).map(|(d, _)| *d)?;
                p.local_def(name_sym.hash)
            },
        )?;
        let Some(Some(tmpl)) = p.gx.fn_templates.get(local.0 as usize).cloned() else {
            let info = p.fn_info(local);
            return Some((local, info.params.clone(), p.ret_view(local)));
        };
        // Prefix: impl args for an impl method, trait ref args
        // for a trait default (its template generics are the
        // trait's). A default is the local whose def is a trait
        // method def, not an item of this impl.
        let is_default = !record.items.contains(&p.def_id(local));
        let prefix: Vec<GenericArg> = if is_default {
            let raw: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
            raw.iter()
                .map(|&g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(self.deep(t)),
                    other => other,
                })
                .collect()
        } else {
            impl_args
        };
        let explicit: Vec<Option<GenericArg>> = prefix.iter().map(|&g| Some(g)).collect();
        let (mut params, ret, _) = self.instantiate_template(site, local, &tmpl.generics.clone(), &explicit, span);
        self.normalize_params(&mut params, span);
        Some((local, params, ret))
    }

    /// One format argument against its spec: the kind must exist for
    /// the type. Errors name the trait a kind needs (`LowerHex` and
    /// kin). Every flag applies to every type, as in Rust: the impl
    /// reads the ones it uses (`{:05}` on a str pads with spaces).
    fn check_fmt_arg(&mut self, t: Ty, spec: FmtSpec, span: Span) {
        let (_, base) = self.autoderef(t);
        let bk = self.kind(base);
        // Valid Rust lust has no rendering for yet: integer exponent
        // formats, and `env::Args` Debug (`Args { inner: [..] }`).
        let int_exp = matches!(spec.kind, FmtKind::LowerExp | FmtKind::UpperExp) && (matches!(bk, TyKind::Int(_)) || bk.is_int_infer());
        if int_exp || (spec.kind == FmtKind::Debug && self.tys.builtin_of(base) == Some(BuiltinTy::Args)) {
            let what = if int_exp { "an integer exponent format" } else { "Debug of `std::env::Args`" };
            self.errs.push(not_yet("L0641", span, what));
            return;
        }
        let what = match spec.kind {
            // A type with a user fmt impl in it proves the trait through
            // the obligation queue (check/fmt.rs `require_fmt`).
            FmtKind::Display => {
                if has_display(self.p, &self.tys, t) || self.kind(t).is_int_infer() || self.require_fmt(t, FmtKind::Display, span) {
                    None
                } else {
                    Some("Display")
                }
            }
            FmtKind::Debug => {
                if has_debug(self.p, &self.tys, t) || self.require_fmt(t, FmtKind::Debug, span) {
                    None
                } else {
                    Some("Debug")
                }
            }
            FmtKind::LowerHex => {
                if matches!(bk, TyKind::Int(_)) || bk.is_int_infer() {
                    None
                } else {
                    Some("LowerHex")
                }
            }
            FmtKind::UpperHex => {
                if matches!(bk, TyKind::Int(_)) || bk.is_int_infer() {
                    None
                } else {
                    Some("UpperHex")
                }
            }
            FmtKind::Octal => {
                if matches!(bk, TyKind::Int(_)) || bk.is_int_infer() {
                    None
                } else {
                    Some("Octal")
                }
            }
            FmtKind::Binary => {
                if matches!(bk, TyKind::Int(_)) || bk.is_int_infer() {
                    None
                } else {
                    Some("Binary")
                }
            }
            FmtKind::LowerExp => {
                if matches!(bk, TyKind::Float(_)) || bk.is_float_infer() {
                    None
                } else {
                    Some("LowerExp")
                }
            }
            FmtKind::UpperExp => {
                if matches!(bk, TyKind::Float(_)) || bk.is_float_infer() {
                    None
                } else {
                    Some("UpperExp")
                }
            }
        };
        if let Some(what) = what {
            if self.kind(t) != TyKind::Error {
                let tn = self.tn(t);
                let fix = match what {
                    "Debug" => "Add #[derive(Debug)] to the type.",
                    "Display" => "Use `{:?}` with #[derive(Debug)], or format the fields yourself.",
                    _ => "This format only applies to integer or float types, as written.",
                };
                self.err("L0112", span, format!("`{tn}` does not implement {what}"), fix);
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn macro_expr(
        &mut self,
        e: ExprId,
        kind: MacroKind,
        args: &[ExprId],
        fmt: &[FmtPiece],
        repeat: bool,
        span: Span,
        expected: Option<Ty>,
    ) -> Ty {
        let fixed = match kind {
            MacroKind::Assert => 1,
            MacroKind::AssertEq | MacroKind::AssertNe => 2,
            MacroKind::Vec => args.len(),
            _ => 0,
        };
        let result = match kind {
            MacroKind::Vec => {
                let elem_expected = expected.and_then(|t| self.tys.vec_elem(self.resolve(t)));
                let elem = elem_expected.unwrap_or_else(|| self.new_var(false));
                if repeat {
                    self.expect_expr(args[0], elem);
                    self.expect_expr(args[1], USIZE);
                    let elem = self.deep(elem);
                    if !has_clone(self.p, &self.tys, elem) && !matches!(self.kind(elem), TyKind::Infer(_)) {
                        let tn = self.tn(elem);
                        self.err(
                            "L0112",
                            span,
                            format!("`vec![x; n]` needs Clone, but `{tn}` is not Clone"),
                            "Derive Clone on the element type.",
                        );
                    }
                } else {
                    for &a in args {
                        self.expect_expr(a, elem);
                    }
                }
                return self.tys.mk_vec(elem);
            }
            MacroKind::Assert => {
                if let Some(&c) = args.first() {
                    self.expect_expr(c, BOOL);
                }
                UNIT
            }
            MacroKind::AssertEq | MacroKind::AssertNe => {
                if args.len() < 2 {
                    self.err("L0105", span, "this macro takes 2 arguments", "Pass both values to compare.");
                } else {
                    let a = self.expr(args[0], None);
                    let b = self.expr(args[1], Some(a));
                    let s = self.span(args[1]);
                    if let Some((ld, rd)) = self.mixed_string_eq(a, b) {
                        // String against &str: compared as strings, as Rust's PartialEq impls do.
                        self.set_res(e, Res::Bin { ld, rd });
                    } else if self.unify(a, b) {
                        let a = self.deep(a);
                        if !has_eq(self.p, &self.tys, a) || !has_debug(self.p, &self.tys, a) {
                            let tn = self.tn(a);
                            self.err(
                                "L0112",
                                span,
                                format!("assert_eq! needs PartialEq and Debug, but `{tn}` lacks one"),
                                "Derive PartialEq and Debug on the type.",
                            );
                        }
                    } else {
                        self.mismatch(s, a, b);
                    }
                }
                UNIT
            }
            MacroKind::Println | MacroKind::Print | MacroKind::Eprintln | MacroKind::Eprint => UNIT,
            MacroKind::Format => STRING,
            MacroKind::FormatArgs => {
                if !self.format_args_ok.contains(&e) {
                    self.err(
                        "L0401",
                        span,
                        "this macro call has no expanded form yet: `format_args!` outside `write!` and `write_fmt`",
                        "Use `format!` for a String, or pass the arguments to `write!`.",
                    );
                }
                crate::ty::fmt::fmt_ty(&mut self.tys, crate::ty::fmt::FmtTy::Arguments)
            }
            MacroKind::Panic | MacroKind::Todo | MacroKind::Unreachable => NEVER,
        };
        for piece in fmt {
            if let FmtPiece::Arg { index, spec, .. } = piece {
                let a = args[*index];
                let t = self.expr(a, None);
                let t = self.deep(t);
                // A still-unbound variable defers the test to
                // finish: its type may be a closure signature
                // that only the second inference pass binds.
                if matches!(self.kind(t), TyKind::Infer(_)) && !self.kind(t).is_int_infer() {
                    self.deferred_fmt.push((t, *spec, self.span(a)));
                    continue;
                }
                let s = self.span(a);
                self.check_fmt_arg(t, *spec, s);
            }
        }
        // Arguments not referenced by the format string (only possible in assert macros).
        for (i, &a) in args.iter().enumerate() {
            if i >= fixed && !fmt.iter().any(|p| matches!(p, FmtPiece::Arg { index, .. } if *index == i)) {
                self.expr(a, None);
            }
        }
        // Format arguments are borrowed: a packed field may not be one.
        let borrowed_args: &[ExprId] = match kind {
            MacroKind::AssertEq | MacroKind::AssertNe => &args[..args.len().min(2)],
            MacroKind::Vec | MacroKind::Assert => &[],
            _ => args,
        };
        for &a in borrowed_args {
            self.check_packed_borrow(a, span);
        }
        result
    }

    // ---------- Patterns ----------

    /// Checks a pattern against a value of type `t`. Applies default binding modes.
    /// Records one pattern binding with the local type its mode gives it.
    fn bind_pattern_local(&mut self, pi: usize, name: Sym, mutable: bool, by_ref: bool, t: Ty, mode: BindMode, span: Span) {
        // Edition 2024: once a pattern is implicitly borrowing (a default
        // binding mode shift happened above it), an explicit `ref` borrow
        // in it is an error.
        if by_ref && mode != BindMode::Move {
            self.err(
                "L0122",
                span,
                "cannot explicitly borrow within an implicitly-borrowing pattern",
                "Remove `ref`: the binding already borrows by default. To borrow explicitly, dereference with `&` at the top of the pattern first.",
            );
        }
        let mode = if by_ref { BindMode::Ref(mutable) } else { mode };
        let lty = match mode {
            BindMode::Move => t,
            BindMode::Ref(m) => self.tys.mk_ref(m, t),
        };
        let mutable_local = mutable && !by_ref;
        if mutable_local && mode != BindMode::Move {
            self.err(
                "L0122",
                span,
                "`mut` binding under a reference is not allowed here",
                "Remove `mut`, or match on the value instead of a reference.",
            );
        }
        // Inside a non-first or-pattern alternative, a binding the
        // first alternative already made reuses that local: every
        // alternative binds the same names to the same checker
        // locals, with the same type and binding mode (rustc
        // E0408 and E0409). The frames nest like the patterns do.
        let key = (name, span.ctxt);
        let mut hit: Option<(usize, usize)> = None;
        for (fi, frame) in self.or_frames.iter().enumerate().rev() {
            if let Some(bi) = frame.expected.iter().position(|b| (b.name, b.ctxt) == key) {
                hit = Some((fi, bi));
                break;
            }
        }
        if let Some((fi, bi)) = hit {
            let exp = self.or_frames[fi].expected[bi].clone();
            if fi + 1 != self.or_frames.len() {
                // Found only in an outer alternative: this one
                // binds a name its own first alternative did not.
                self.or_frames.last_mut().unwrap().extra.push((name, span));
            } else if self.or_frames[fi].seen[bi] {
                self.err(
                    "L0106",
                    span,
                    format!("`{}` is bound more than once in the same pattern", self.name(name)),
                    "Rename one of the bindings.",
                );
            }
            self.or_frames[fi].seen[bi] = true;
            if mode != exp.mode || mutable_local != exp.mutable {
                self.err(
                    "L0110",
                    span,
                    format!("variable `{}` is bound inconsistently across `|` alternatives", self.name(name)),
                    "Bind it the same way in every alternative (same `ref` and `mut`).",
                );
            }
            if !self.unify(lty, exp.ty) {
                self.mismatch(span, exp.ty, lty);
            }
            self.scopes.push((key, exp.local));
            self.out.pat_res[pi] = PatRes::Binding { local: exp.local, mode };
            if let Some(log) = &mut self.or_log {
                log.push(OrBind { name, ctxt: span.ctxt, local: exp.local, mode, ty: lty, mutable: mutable_local });
            }
            return;
        }
        if !self.or_frames.is_empty() {
            // A name the first alternative never bound: the
            // alternative is rejected when it ends, but checking
            // continues with a fresh local so the body still
            // resolves names.
            self.or_frames.last_mut().unwrap().extra.push((name, span));
        } else if let Some(&mark) = self.pat_marks.last()
            && self.scopes[mark..].iter().any(|&(k, _)| k == key)
        {
            // One pattern may not bind a name twice (rustc
            // E0416): bindings an enclosing or-pattern restored
            // into scope count too.
            self.err(
                "L0106",
                span,
                format!("`{}` is bound more than once in the same pattern", self.name(name)),
                "Rename one of the bindings.",
            );
        }
        let l = self.add_local(name, lty, mutable_local, span);
        self.out.pat_res[pi] = PatRes::Binding { local: l, mode };
        if let Some(log) = &mut self.or_log {
            log.push(OrBind { name, ctxt: span.ctxt, local: l, mode, ty: lty, mutable: mutable_local });
        }
    }

    /// Checks one const pattern value against the scrutinee type:
    /// structural-match (a constant whose Adt type has no derived
    /// `PartialEq` is L0633, as in Rust; a structural value lust
    /// cannot compare yet is the non-scalar unsupported error), then
    /// type equality and refutability outside `match`. Returns true
    /// when the pattern may use the value.
    fn check_const_value(&mut self, cty: Ty, val: &crate::ty::consteval::ConstValue, t: Ty, span: Span, in_match: bool) -> bool {
        use crate::ty::consteval::ConstValue as CV;
        let ct = self.resolve(cty);
        match val {
            CV::Int(_) | CV::Bool(_) | CV::Char(_) | CV::Float(..) | CV::Str(_) => {}
            _ => {
                let nonstructural = matches!(self.tys.local_adt(ct), Some(a) if !self.p.adt(a).derives.partial_eq);
                if nonstructural {
                    let tn = self.tn(ct);
                    self.err(
                        "L0633",
                        span,
                        format!("constant of non-structural type `{tn}` cannot be used in a pattern"),
                        "Derive `PartialEq` on the type, match a field, or compare in a guard instead.",
                    );
                } else {
                    self.errs.push(unsupported(span, "non-scalar const patterns"));
                }
                return false;
            }
        }
        let eff = if matches!(val, CV::Str(_)) && self.kind(t) == TyKind::Str { t } else { ct };
        if !self.unify(eff, t) {
            self.mismatch(span, t, eff);
            return false;
        }
        if !in_match {
            self.errs.push(unsupported(span, "refutable patterns here"));
        }
        true
    }

    /// A free const item used as a pattern, by const index.
    fn const_item_pat(&mut self, pi: usize, idx: u32, t: Ty, span: Span, in_match: bool) {
        // The pattern consumes the const's value: record its `Sig`
        // read so a value edit rechecks this body (ARCH 8.2).
        if let Some(&def) = self.p.const_defs.get(idx as usize) {
            let p = self.p;
            let _ = p.sig_of(&mut self.out.reads, def);
        }
        let c = &self.p.consts[idx as usize];
        let (ct, val) = (c.ty, c.value.clone());
        if self.check_const_value(ct, &val, t, span, in_match) {
            self.out.pat_res[pi] = PatRes::ConstItem(idx);
        }
    }

    /// Tries to read a path pattern as a const pattern. Returns true
    /// when the path named a const (or a static, which errors), so
    /// the caller skips variant handling.
    fn try_const_path_pat(&mut self, pi: usize, segs: &[ast::PathSeg], t: Ty, span: Span, in_match: bool) -> bool {
        let p = self.p;
        if segs.len() == 1 {
            // Free consts and statics in one segment are handled by
            // the pattern-identifier resolution in the Path arm.
            return false;
        }
        // Primitive associated consts (`i64::MAX`, `u32::BITS`), the
        // same table `path_expr` reads for expression positions.
        if segs.len() == 2
            && let Some(it) = p.known.int_ty(segs[0].name)
        {
            let item = self.name(segs[1].name).to_string();
            let item = item.as_str();
            let bits = it.bits();
            let v = match item {
                "MAX" => Some(crate::ty::consteval::truncate_to_int(it.max128() as i128, it)),
                "MIN" => Some(if it.signed() { if bits >= 128 { i128::MIN } else { -(1i128 << (bits - 1)) } } else { 0 }),
                "BITS" => Some(bits as i128),
                _ => None,
            };
            if let Some(v) = v {
                let (ct, val) = if item == "BITS" {
                    (int(IntTy::U32), v)
                } else if it == IntTy::U128 && item == "MAX" {
                    (int(it), -1)
                } else {
                    (int(it), v)
                };
                let cv = crate::ty::consteval::ConstValue::Int(val);
                if self.check_const_value(ct, &cv, t, span, in_match) {
                    self.out.pat_res[pi] = PatRes::PrimConst(val);
                }
                return true;
            }
        }
        if let Some((adt, item)) = self.assoc_const_key(segs)
            && let Some(picked) = self.assoc_const_base(segs, Some(span)).and_then(|base| self.inherent_assoc_pick(adt, item, base, Some(span)))
        {
            if let Some(idx) = picked {
                self.check_assoc_vis(adt, item, "associated constant", span);
                self.const_item_pat(pi, idx, t, span, in_match);
            }
            return true;
        }
        // A trait associated const pattern on a concrete type
        // (`S::C`): only a confirmed impl gives the value a
        // pattern needs.
        if segs.len() == 2
            && !self.assoc_const_key(segs).is_some_and(|(adt, item)| self.inherent_value_blocks(adt, item))
            && let Some(base) = self.assoc_const_base(segs, Some(span))
            && let Some((Some(idx), _)) = self.trait_assoc_const(None, base, None, segs[1].name, span)
        {
            self.const_item_pat(pi, idx, t, span, in_match);
            return true;
        }
        false
    }

    /// A qualified path in value position: `<Type>::CONST` or
    /// `<Type as Trait>::CONST`. Calls through a qualified path
    /// resolve in the call arm instead. A named trait reads only
    /// that trait's item; with no trait, inherent items win, as
    /// on a plain path.
    fn qpath_value(&mut self, e: ExprId, self_ty: ast::TyId, trait_path: &[ast::PathSeg], segs: &[ast::PathSeg], span: Span) -> Ty {
        let p = self.p;
        if segs.len() != 1 {
            self.err("L0101", span, "cannot find the associated item", "Check the qualified path and the name.");
            return ERROR;
        }
        let name = segs[0].name;
        let base = self.resolve_written(self_ty);
        let hint = if trait_path.is_empty() {
            None
        } else {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            let tref = ast::TraitRefExpr { path: trait_path.to_vec() };
            match generics::resolve_trait_ref(p.ast, p.interner, p.known, &cx, &mut self.tys, &self.body_scope.clone(), base, &tref, span)
            {
                Ok(tr) => Some(tr),
                Err(d) => {
                    self.errs.push(d);
                    return ERROR;
                }
            }
        };
        if hint.is_none()
            && let Some(adt) = self.tys.local_adt(self.resolve(base))
            && let Some(picked) = self.inherent_assoc_pick(adt, name, base, Some(span))
        {
            return match picked {
                Some(idx) => {
                    // As on a plain `Type::C` path: the value is baked in
                    // (record its `Sig` read) and visibility applies.
                    if let Some(&def) = p.const_defs.get(idx as usize) {
                        let _ = p.sig_of(&mut self.out.reads, def);
                    }
                    self.check_assoc_vis(adt, name, "associated constant", span);
                    let c = &p.consts[idx as usize];
                    let (v, t) = (c.value.clone(), c.ty);
                    let i = self.ei(e);
                    self.out.const_exprs[i] = Some(v);
                    self.deep(t)
                }
                None => ERROR,
            };
        }
        let blocked = hint.is_none()
            && self.replay_pick(e).is_none()
            && self.tys.local_adt(self.resolve(base)).is_some_and(|adt| self.inherent_value_blocks(adt, name));
        if !blocked && let Some((idx, t)) = self.trait_assoc_const(Some(e), base, hint, name, span) {
            if let Some(idx) = idx {
                let v = p.consts[idx as usize].value.clone();
                let i = self.ei(e);
                self.out.const_exprs[i] = Some(v);
            }
            return t;
        }
        // An inherent associated function as a value
        // (`<S>::mk`), resolved as the plain two-segment path
        // is. A trait's function as a value through a qualified
        // path is not resolved yet.
        if hint.is_none()
            && let ast::TyExpr::Path(ty_segs) = p.ast.ty(self_ty)
            && ty_segs.len() == 1
        {
            let mut segs2 = ty_segs.clone();
            segs2.push(segs[0].clone());
            if let Some(r) = self.resolve_assoc(&segs2, span) {
                // Function items only: variant construction
                // through a qualified path has no lowering yet,
                // so it rejects with the error below instead.
                if let Res::Fn(f) = r {
                    self.set_res(e, r);
                    return self.inherent_qpath_fn_value(e, f, base, span);
                }
            } else {
                return ERROR;
            }
        }
        // A trait's function as a value: `<S as Tr>::mk`, also a
        // generic impl's fn or a trait default body, instantiated at
        // the selected impl's (or trait ref's) args.
        if let Some(found) = self.trait_fn_value(self.resolve(base), hint, name, true, span) {
            let Some((f, prefix)) = found else { return ERROR };
            self.set_res(e, Res::Fn(f));
            return self.fn_value_ty_prefixed(e, f, &prefix, span);
        }
        self.err(
            "L0104",
            span,
            format!("no associated const named `{}` here", self.name(name)),
            "Check the spelling against the impl or trait definition.",
        );
        ERROR
    }

    /// True when an inherent associated function or enum variant
    /// of this name shadows any trait associated const on an Adt
    /// (inherent items win in rustc's path resolution).
    fn inherent_value_blocks(&mut self, adt: AdtId, item: Sym) -> bool {
        let p = self.p;
        let template = p.defs.def_of_adt(adt).and_then(|d| p.defs.local_adt(d)).unwrap_or(adt);
        p.inherent_reads(&mut self.out.reads, p.def_of_adt(template), item);
        p.methods.contains_key(&(template, item)) || (p.adt(adt).is_enum && p.adt(adt).variants.iter().any(|v| v.name == item))
    }

    /// Resolves a trait associated const read (`Type::C`, `T::C`,
    /// `Self::C`, `<T as Tr>::C`) on self type `base`, like
    /// `assoc_call` resolves a trait method call: a written trait
    /// (`hint`), else the template pick, else the bounds on a
    /// type parameter, else every trait in scope that declares a
    /// const of this name. Returns the const's type and, when an
    /// impl is confirmed, its evaluated value as an index into
    /// `Program::consts` (the impl's own, else the trait
    /// default). Param evidence gives only the type; the
    /// instance check replays the pick for the value.
    fn trait_assoc_const(
        &mut self,
        pick_e: Option<ExprId>,
        base: Ty,
        hint: Option<TraitRef>,
        name: Sym,
        span: Span,
    ) -> Option<(Option<u32>, Ty)> {
        let p = self.p;
        // Every user trait that declares an associated const `name`.
        let mut by_name: Vec<DefId> = Vec::new();
        for &assoc in p.gx.trait_assoc_consts.keys() {
            let Some(t) = p.gx.index.trait_of_assoc(assoc) else { continue };
            let Some(rec) = p.gx.index.trait_record(t) else { continue };
            if rec.assoc_items.iter().any(|&(d, n, _)| d == assoc && n == name) && !by_name.contains(&t) {
                by_name.push(t);
            }
        }
        if by_name.is_empty() {
            return None;
        }
        let base_r = self.resolve(base);
        let bound: Vec<DefId> = if hint.is_none() && matches!(self.tys.kind(base_r), TyKind::Param(_) | TyKind::Projection(..)) {
            by_name
                .iter()
                .copied()
                .filter(|&t| {
                    self.env().iter().any(|pred| {
                        matches!(pred, Predicate::Trait(b) if b.count == 0 && b.value.def == t
                            && self.tys.args(b.value.args).first().and_then(|g| g.as_ty()) == Some(base_r))
                    })
                })
                .collect()
        } else {
            Vec::new()
        };
        let traits: Vec<DefId> = match (hint, pick_e.and_then(|e| self.replay_pick(e))) {
            (Some(tr), _) => vec![tr.def],
            (None, Some(pick)) => vec![pick.trait_def],
            (None, None) if !bound.is_empty() => bound,
            (None, None) => by_name.into_iter().filter(|&d| method::trait_in_scope_pub(self, d)).collect(),
        };
        let mut hits: Vec<(Option<u32>, Ty)> = Vec::new();
        let mut hit_traits: Vec<DefId> = Vec::new();
        for trait_def in traits {
            let Some(rec) = p.gx.index.trait_record(trait_def).cloned() else { continue };
            let Some(assoc) = rec.assoc_by_name(name).filter(|a| p.gx.trait_assoc_consts.contains_key(a)) else { continue };
            let snap = self.snapshot_vars();
            let obl_len = self.obl_len();
            let sites_len = self.generic_sites.len();
            let tr = match hint {
                Some(written) if written.def == trait_def => written,
                _ => {
                    let n_inputs = rec.generics.params.len().saturating_sub(1);
                    let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(base)];
                    for _ in 0..n_inputs {
                        tr_args.push(GenericArg::Ty(self.new_var(false)));
                    }
                    let args_id = self.tys.intern_args(&tr_args);
                    TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS }
                }
            };
            let sel = self.select_obligation_at(tr, span, 0);
            let hit = match sel {
                // An impl parameter the header could not bind means
                // the Self type is not known here (a fresh variable
                // from a missing turbofish): rustc asks for the
                // annotation, so this is no hit.
                Selection::Impl { id, ref unbound, .. } if unbound.is_empty() => {
                    let impl_def = p.gx.index.get(id).def;
                    p.impl_assoc_consts
                        .get(&(impl_def, assoc))
                        .copied()
                        .or_else(|| p.trait_assoc_const_values.get(&assoc).copied())
                        .map(|idx| (Some(idx), self.deep(p.consts[idx as usize].ty)))
                }
                Selection::ParamEvidence(_) => {
                    let (declared, _) = p.gx.trait_assoc_consts[&assoc];
                    let args: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
                    Some((None, subst(&mut self.tys, declared, &args)))
                }
                _ => None,
            };
            match hit {
                Some(h) => {
                    hits.push(h);
                    hit_traits.push(trait_def);
                }
                None => {
                    self.rollback_vars(snap);
                    self.obl_truncate(obl_len);
                    self.generic_sites.truncate(sites_len);
                }
            }
        }
        match hits.len() {
            1 => {
                let hit = hits.into_iter().next().unwrap();
                if let Some(e) = pick_e {
                    self.record_pick(e, hit_traits[0], 0, ReceiverForm::Value);
                    if hit.0.is_none() {
                        self.abstract_consts.push(e);
                    }
                }
                Some(hit)
            }
            0 => None,
            _ => {
                self.err(
                    "L0720",
                    span,
                    format!("multiple trait associated consts named `{}` apply here", self.name(name)),
                    "Name the trait with a fully qualified path, such as `<Type as Trait>::CONST`.",
                );
                Some((None, ERROR))
            }
        }
    }

    /// The self type a two-segment associated const path names:
    /// a type parameter or `Self` from the body scope, else a
    /// local Adt (written type arguments fix its parameters,
    /// fresh variables otherwise, as in `trait_assoc_base`). A
    /// `None` span (body const evaluation) reports no argument
    /// errors: the path's own check reports them.
    fn assoc_const_base(&mut self, segs: &[ast::PathSeg], span: Option<Span>) -> Option<Ty> {
        let p = self.p;
        let head = segs[0].name;
        if let Some(&(_, t)) = self.body_scope.param_tys.iter().find(|(n, _)| *n == head) {
            return Some(t);
        }
        if head == p.known.self_type
            && let Some(t) = self.body_scope.self_ty
        {
            return Some(t);
        }
        let a = match self.binding(Namespace::Type, head) {
            BindingRes::Def(def) => p.adt_by_def(def)?,
            _ => return None,
        };
        let generics = p.gx.adt_generics.get(a.0 as usize).cloned().unwrap_or_default();
        if generics.params.is_empty() {
            return Some(self.tys.adt_ty(a));
        }
        let mark = self.errs.len();
        let args = self.value_path_args(a, &segs[..1], span.unwrap_or_default());
        if span.is_none() {
            self.errs.truncate(mark);
        }
        Some(self.tys.mk_adt(p.def_of_adt(a), &args))
    }

    /// A zero const value of one type, for the template-only
    /// placeholder in `finish`. Reference and other non-const
    /// shapes have no placeholder: a trait associated const of
    /// such a type read through a type parameter still fails
    /// the template check with the unassigned-temp error.
    fn zero_const(&mut self, t: Ty) -> Option<crate::ty::consteval::ConstValue> {
        use crate::ty::consteval::ConstValue;
        let t = self.deep(t);
        match self.tys.kind(t) {
            TyKind::Adt(..) if self.tys.option_elem(t).is_some() => Some(ConstValue::Variant(0, Vec::new())),
            TyKind::Adt(..) => {
                let p = self.p;
                let a = self.tys.local_adt(t)?;
                let (is_enum, field_tys) = {
                    let adt = p.adt(a);
                    (adt.is_enum, adt.variants.first()?.fields.iter().map(|f| f.ty).collect::<Vec<Ty>>())
                };
                let args: Vec<GenericArg> = match self.tys.adt_parts(t) {
                    Some((_, args_id)) => self.tys.args(args_id).to_vec(),
                    None => Vec::new(),
                };
                let mut vals = Vec::new();
                for ft in field_tys {
                    let ft = if args.is_empty() { ft } else { subst(&mut self.tys, ft, &args) };
                    vals.push(self.zero_const(ft)?);
                }
                Some(if is_enum { ConstValue::Variant(0, vals) } else { ConstValue::Aggregate(vals) })
            }
            TyKind::Int(_) => Some(ConstValue::Int(0)),
            TyKind::Float(f) => Some(ConstValue::Float(0, f)),
            TyKind::Bool => Some(ConstValue::Bool(false)),
            TyKind::Char => Some(ConstValue::Char('\0')),
            TyKind::Unit => Some(ConstValue::Unit),
            TyKind::Tuple(ts) => {
                let elems: Vec<Ty> = self.tys.tys_of(ts).to_vec();
                let mut vals = Vec::new();
                for e in elems {
                    vals.push(self.zero_const(e)?);
                }
                Some(ConstValue::Aggregate(vals))
            }
            TyKind::Array(e, c) => {
                let ConstKind::Int(n) = self.tys.const_kind(self.resolve_const(c)) else { return None };
                Some(ConstValue::Repeat(Box::new(self.zero_const(e)?), n as u64))
            }
            _ => None,
        }
    }

    /// The (Adt, name) key an associated const path (`Self::A`,
    /// `Type::A`) names, when the owning type is a local Adt.
    fn assoc_const_key(&mut self, segs: &[ast::PathSeg]) -> Option<(AdtId, Sym)> {
        if segs.len() != 2 {
            return None;
        }
        let p = self.p;
        let (ty_name, item) = (segs[0].name, segs[1].name);
        let adt = if ty_name == p.known.self_type {
            self.self_adt()
        } else {
            match self.binding(Namespace::Type, ty_name) {
                BindingRes::Def(def) => p.adt_by_def(def),
                _ => None,
            }
        }?;
        Some((adt, item))
    }

    /// The pick among same-name inherent associated consts for
    /// a written Self type instance, exactly as written
    /// (`assoc_const_base`): an impl applies when its Self
    /// pattern unifies with the instance under fresh impl
    /// arguments, probed with rollback so a rejected candidate
    /// binds nothing. The one hit replays for real (its
    /// predicates become obligations); several hits report the
    /// ambiguity here and act as no pick.
    /// `None` when no candidate applies (the caller keeps
    /// looking), `Some(None)` when several apply (reported
    /// here; the caller must not fall through to a trait item).
    fn inherent_assoc_pick(&mut self, adt: AdtId, item: Sym, written: Ty, span: Option<Span>) -> Option<Option<u32>> {
        let p = self.p;
        let cands: Vec<u32> = p.inherent_assoc_consts(adt, item).to_vec();
        if cands.is_empty() {
            return None;
        }
        let mut hits: Vec<(u32, Option<(Ty, Generics, Span)>)> = Vec::new();
        for &idx in &cands {
            let entry = p.gx.inherent_const_self.get(&idx).cloned();
            let applies = match &entry {
                None => true,
                Some((pat, gens, _)) => {
                    let snap = self.snapshot_vars();
                    let obl = self.obl_len();
                    let args = self.fresh_args(gens);
                    let cand = subst(&mut self.tys, *pat, &args);
                    let hit = self.unify(cand, written);
                    self.rollback_vars(snap);
                    self.obl_truncate(obl);
                    hit
                }
            };
            if applies {
                hits.push((idx, entry));
            }
        }
        match hits.len() {
            0 => None,
            1 => {
                let (idx, entry) = hits.pop().unwrap();
                if let Some((pat, gens, _)) = entry {
                    let args = self.fresh_args(&gens);
                    let cand = subst(&mut self.tys, pat, &args);
                    if self.unify(cand, written)
                        && let Some(span) = span
                    {
                        let preds = gens.predicates.clone();
                        self.push_predicates(&preds, &args, span);
                    }
                }
                Some(Some(idx))
            }
            _ => {
                if let Some(span) = span {
                    self.err(
                        "L0110",
                        span,
                        format!("multiple associated constants named `{}` apply here", self.name(item)),
                        "Write the type arguments so only one impl applies, for example `Type::<Arg>::CONST`.",
                    );
                }
                Some(None)
            }
        }
    }

    fn pattern(&mut self, pat: PatId, t: Ty, in_match: bool) {
        // Names bound from here on belong to this one pattern
        // (see the duplicate-name check in `bind_pattern_local`).
        self.pat_marks.push(self.scopes.len());
        self.pattern_mode(pat, t, BindMode::Move, in_match);
        self.pat_marks.pop();
    }

    fn pattern_mode(&mut self, pat: PatId, t: Ty, mode: BindMode, in_match: bool) {
        let p = self.p;
        let pi = (pat.0 - self.out.pat_base) as usize;
        let span = p.ast.pat_span(pat);
        // Default binding modes: a non-binding pattern auto-derefs a reference scrutinee.
        let scrut_t = self.resolve(t);
        let mut t = scrut_t;
        let mut mode = mode;
        let opt = self.option_pattern(pat);
        let structural = opt.is_some()
            || matches!(
                p.ast.pat(pat),
                Pat::TupleStruct { .. }
                    | Pat::Struct { .. }
                    | Pat::Path(_)
                    | Pat::Lit(_)
                    | Pat::Range { .. }
                    | Pat::Tuple(_)
                    | Pat::Slice { .. }
            );
        if structural {
            let mut derefs = 0;
            while let TyKind::Ref(_, m, inner) = self.tys.kind(t) {
                // A string literal, byte string literal, or &str const
                // pattern has a reference type itself, so it matches
                // the scrutinee reference directly and never
                // auto-derefs (rustc rejects `&&str` against `"ab"`
                // and `&&[u8]` against `b"ab"`).
                let str_pat = matches!(p.ast.pat(pat), Pat::Lit(l) if matches!(p.ast.expr(*l), Expr::Str(_)) || self.is_byte_str_lit(*l))
                    || matches!(p.ast.pat(pat), Pat::Path(segs) if segs.len() == 1 && p.const_names.get(&segs[0].name).is_some_and(|&i| matches!(p.consts[i as usize].value, crate::ty::consteval::ConstValue::Str(_))));
                if str_pat {
                    break;
                }
                derefs += 1;
                mode = match mode {
                    BindMode::Ref(false) => BindMode::Ref(false),
                    _ => BindMode::Ref(m.is_mut()),
                };
                t = self.resolve(inner);
            }
            self.out.pat_derefs[pi] = derefs;
        }
        self.out.pat_ty[pi] = t;
        // Turbofish on the pattern's path (`Some::<u8>(x)`, `None::<u8>`)
        // fixes the scrutinee's args, as in expressions.
        let pat_path: Option<&[ast::PathSeg]> = match p.ast.pat(pat) {
            Pat::TupleStruct { path, .. } | Pat::Path(path) => Some(path.as_slice()),
            _ => None,
        };
        if let Some(is_some) = opt {
            let inner = match pat_path.and_then(|segs| self.builtin_ctor_args(segs, 1, span)) {
                Some(a) => a[0],
                None => self.new_var(false),
            };
            let ot = self.tys.mk_option(inner);
            if std::env::var_os("LUST_DEBUG_PAT").is_some() {
                eprintln!(
                    "PAT opt scrutinee ty={} kind={:?} fn={} params={:?}",
                    self.tn(t),
                    self.tys.kind(t),
                    self.name(self.f.name),
                    self.f.params.iter().map(|&x| self.tn(x)).collect::<Vec<_>>()
                );
            }
            if !self.unify(ot, t) {
                self.mismatch(span, t, ot);
                return;
            }
            self.out.pat_res[pi] = PatRes::Opt(is_some);
            if let (true, Pat::TupleStruct { elems, .. }) = (is_some, p.ast.pat(pat)) {
                self.pattern_mode(elems[0], inner, mode, in_match);
            }
            return;
        }
        if opt.is_none()
            && let Some(is_ok) = self.result_pattern(pat)
        {
            let (a, b) = match pat_path.and_then(|segs| self.builtin_ctor_args(segs, 2, span)) {
                Some(w) => (w[0], w[1]),
                None => (self.new_var(false), self.new_var(false)),
            };
            let rt = self.tys.mk_result(a, b);
            if !self.unify(rt, t) {
                self.mismatch(span, t, rt);
                return;
            }
            self.out.pat_res[pi] = PatRes::Res(is_ok);
            if let Pat::TupleStruct { elems, .. } = p.ast.pat(pat) {
                self.pattern_mode(elems[0], if is_ok { a } else { b }, mode, in_match);
            }
            return;
        }
        // A plain name that resolves to a const item, a unit struct, or
        // a unit variant is a path pattern, not a binding (unless a
        // local binding shadows the name). Imports count: resolution
        // goes through the module bindings, as in expressions. The
        // pattern consumes the const's value, so record its `Sig` read
        // (the fingerprint folds the evaluated value): a value edit
        // must recheck this body (ARCH 8.2), like a const in an
        // expression.
        if let Pat::Binding { name, mutable: false, by_ref: false } = p.ast.pat(pat)
            && self.lookup(*name, span.ctxt).is_none()
            && let Some(crate::check::collect::BodyItem::Const(ci)) = self.body_item_of(*name, span.ctxt)
        {
            let c = &p.body_consts[ci as usize];
            if !matches!(
                c.value,
                crate::ty::consteval::ConstValue::Int(_)
                    | crate::ty::consteval::ConstValue::Bool(_)
                    | crate::ty::consteval::ConstValue::Char(_)
            ) {
                self.errs.push(unsupported(span, "non-scalar const patterns"));
                return;
            }
            let ct = c.ty;
            if !self.unify(ct, t) {
                self.mismatch(span, t, ct);
                return;
            }
            self.out.pat_res[pi] = PatRes::BodyConst(ci);
            return;
        }
        if let Pat::Binding { name, mutable: false, by_ref: false } = p.ast.pat(pat)
            && self.lookup(*name, span.ctxt).is_none()
        {
            match self.pat_ident(*name) {
                PatIdent::Const(idx) => {
                    self.const_item_pat(pi, idx, t, span, in_match);
                    return;
                }
                PatIdent::Static => {
                    self.err(
                        "L0110",
                        span,
                        "statics cannot be used as patterns",
                        "Use a const item for a pattern, or compare with the static in a guard.",
                    );
                    return;
                }
                PatIdent::Variant(a, v) => {
                    let adt_ty = self.tys.adt_ty(a);
                    if !self.unify(adt_ty, t) {
                        self.mismatch(span, t, adt_ty);
                        return;
                    }
                    if p.adt(a).variants[v as usize].shape != VariantShape::Unit {
                        self.err("L0110", span, "this variant has fields", "Match its fields with `(..)` or `{ .. }`.");
                        return;
                    }
                    if self.hidden_variant(a, v, span) {
                        return;
                    }
                    self.out.pat_res[pi] = PatRes::Variant(a, v);
                    return;
                }
                PatIdent::Other => {}
            }
        }
        // A const path pattern (`MAX`, `Self::A`, `Type::A`, `m::S`)
        // is not a variant: it compares against the const's value.
        if let Pat::Path(segs) = p.ast.pat(pat) {
            let segs = segs.clone();
            if self.try_const_path_pat(pi, &segs, t, span, in_match) {
                // A const path pattern does not auto-deref (unlike a
                // literal or a variant): if peeling references above
                // was needed to reach the const's type, the pattern
                // does not match the scrutinee (rustc E0308). A const
                // whose own type is a reference (a `&str` const) needs
                // no peeling: its type already is the scrutinee type.
                let const_is_ref = match self.out.pat_res[pi] {
                    PatRes::ConstItem(idx) => matches!(self.kind(self.p.consts[idx as usize].ty), TyKind::Ref(..)),
                    PatRes::BodyConst(ci) => matches!(self.kind(self.p.body_consts[ci as usize].ty), TyKind::Ref(..)),
                    _ => false,
                };
                if self.out.pat_derefs[pi] > 0 && !const_is_ref {
                    self.mismatch(span, scrut_t, t);
                }
                return;
            }
        }
        match p.ast.pat(pat) {
            Pat::Wild => {}
            Pat::Binding { name, mutable, by_ref } => {
                // A plain binding named the same as a variant of the
                // matched enum type is an error (rustc E0170): it can
                // never mean the variant. `mut`, `ref`, and `@` forms
                // are plain bindings and stay legal.
                if !mutable && !by_ref {
                    let (_, base) = self.autoderef(t);
                    if let Some(a) = self.tys.local_adt(self.resolve(base))
                        && p.adt(a).is_enum
                        && p.adt(a).variants.iter().any(|v| v.name == *name)
                        && self.lookup(*name, span.ctxt).is_none()
                        && !matches!(self.pat_ident(*name), PatIdent::Variant(b, _) if b == a)
                    {
                        let (vn, en) = (self.name(*name).to_string(), p.display_path(p.adt(a).name));
                        self.err(
                            "L0110",
                            span,
                            format!("pattern binding `{vn}` is named the same as one of the variants of the type `{en}`"),
                            format!("Rename the binding, or match the variant with `{en}::{vn}` (or `use {en}::{vn};` first)."),
                        );
                        return;
                    }
                }
                self.bind_pattern_local(pi, *name, *mutable, *by_ref, t, mode, span);
            }
            Pat::At { name, mutable, by_ref, inner } => {
                self.bind_pattern_local(pi, *name, *mutable, *by_ref, t, mode, span);
                self.pattern_mode(*inner, t, mode, in_match);
            }
            Pat::Ref { mutable, inner } => match self.kind(t) {
                TyKind::Ref(_, m, inner_ty) => {
                    // Edition 2024: an explicit `&` dereference inside an
                    // implicitly-borrowing pattern is an error.
                    if mode != BindMode::Move {
                        self.err(
                            "L0122",
                            span,
                            "cannot explicitly dereference within an implicitly-borrowing pattern",
                            "Remove the `&`: the pattern already borrows by default, so the binding has the same type without it.",
                        );
                    }
                    if *mutable && !m.is_mut() {
                        self.err(
                            "L0110",
                            span,
                            "pattern requires `&mut`, but the matched type is a shared reference",
                            "Use `&` in the pattern, or match on a `&mut` value.",
                        );
                    }
                    if !*mutable && m.is_mut() {
                        self.err(
                            "L0110",
                            span,
                            "pattern requires `&`, but the matched type is a mutable reference",
                            "Use `&mut` in the pattern, or match on a shared reference.",
                        );
                    }
                    // An explicit `&` resets the default binding mode inside it.
                    self.pattern_mode(*inner, inner_ty, BindMode::Move, in_match);
                }
                TyKind::Error => self.pattern_mode(*inner, ERROR, mode, in_match),
                _ => {
                    let tn = self.tn(t);
                    self.err(
                        "L0110",
                        span,
                        format!("reference pattern cannot match a value of type `{tn}`"),
                        "Match on a reference, or remove the `&`.",
                    );
                    self.pattern_mode(*inner, ERROR, mode, in_match);
                }
            },
            Pat::Lit(l) => {
                // A byte string literal has type `&[u8; N]` but, as a
                // pattern, also matches a `&[u8]` scrutinee (rustc's
                // byte string pattern rule). Check it with no expected
                // type so the array keeps its own length, then apply
                // that rule by hand.
                let byte_str = self.is_byte_str_lit(*l);
                let lt = self.expr(*l, if byte_str { None } else { Some(t) });
                if !self.unify(lt, t) && !(byte_str && self.byte_str_pat_ok(lt, t)) {
                    self.mismatch(span, t, lt);
                }
                if !in_match {
                    self.errs.push(unsupported(span, "refutable patterns here"));
                }
            }
            Pat::Range { lo, hi, inclusive } => {
                // The parser only builds two-bound ranges today; a half-open
                // range checks its one bound the same way.
                let mut bound_tys = Vec::new();
                if let Some(lo) = lo {
                    bound_tys.push((*lo, self.expr(*lo, Some(t))));
                }
                if let Some(hi) = hi {
                    bound_tys.push((*hi, self.expr(*hi, Some(t))));
                }
                // A range bound that reads a trait associated const
                // through a type parameter depends on the parameter:
                // rustc rejects constant patterns that do (E0158).
                for &(b_e, _) in &bound_tys {
                    if self.abstract_consts.contains(&b_e) {
                        let b_span = self.span(b_e);
                        self.err(
                            "L0110",
                            b_span,
                            "a range pattern bound cannot depend on a generic parameter",
                            "Use a literal bound, or compare with an `if` guard.",
                        );
                    }
                }
                // An exclusive range `lo..hi` needs lo < hi (rustc E0579);
                // an inclusive one needs lo <= hi (rustc E0030). Float
                // ranges follow the same rules, and a NaN bound is an
                // error in rustc ("cannot use NaN in patterns").
                let mut empty = false;
                // An unresolved float variable falls back to `f64` at
                // body end, so its bounds read as `f64` here too.
                let float_ft = match self.kind(t) {
                    TyKind::Float(ft) => Some(ft),
                    k if k.is_float_infer() => Some(FloatTy::F64),
                    _ => None,
                };
                if let Some(ft) = float_ft {
                    let vals: Vec<Option<f64>> = bound_tys.iter().map(|&(b_e, _)| self.const_float(b_e, ft)).collect();
                    for (&(b_e, _), v) in bound_tys.iter().zip(&vals) {
                        if v.is_some_and(|v| v.is_nan()) {
                            let b_span = self.span(b_e);
                            self.err("L0110", b_span, "cannot use NaN in patterns", "Use a guard to test for NaN.");
                        }
                    }
                    if let [Some(lo_v), Some(hi_v)] = vals[..] {
                        empty = lo_v > hi_v || (!inclusive && lo_v == hi_v);
                    }
                }
                if let [(lo_e, _), (hi_e, _)] = bound_tys[..]
                    && let (Some(lo_v), Some(hi_v)) = (self.const_scalar(lo_e), self.const_scalar(hi_e))
                    && match (self.scalar_key(lo_v, t), self.scalar_key(hi_v, t)) {
                        (Some(a), Some(b)) => a > b || (!inclusive && a == b),
                        _ => lo_v > hi_v || (!inclusive && lo_v == hi_v),
                    }
                {
                    empty = true;
                }
                // `..MIN` is empty too: the exclusive upper bound is the
                // type's minimum, whose order key is 0 (rustc E0579).
                if lo.is_none()
                    && !inclusive
                    && let [(hi_e, _)] = bound_tys[..]
                    && self.const_scalar(hi_e).is_some_and(|hi_v| self.scalar_key(hi_v, t) == Some(0))
                {
                    empty = true;
                }
                if empty {
                    self.err(
                        "L0119",
                        span,
                        "lower range bound is greater than the upper bound",
                        "Swap the bounds, or fix the values. An empty range pattern never matches.",
                    );
                }
                if bound_tys.iter().any(|&(_, bt)| !self.unify(bt, t))
                    || !(matches!(self.kind(t), TyKind::Int(_) | TyKind::Float(_) | TyKind::Char)
                        || self.kind(t).is_int_infer()
                        || self.kind(t).is_float_infer())
                {
                    self.err(
                        "L0110",
                        span,
                        "range patterns need integer, float, or char bounds of the matched type",
                        "Use bounds of the scrutinee's type.",
                    );
                }
            }
            Pat::Path(segs) | Pat::TupleStruct { path: segs, .. } | Pat::Struct { path: segs, .. } => {
                // A path may also name a const item (`m::K`, rewritten
                // to its flat name) or a primitive associated const
                // (`u8::MAX`): both compare like literal patterns.
                if matches!(p.ast.pat(pat), Pat::Path(_)) {
                    if segs.len() == 1 {
                        match self.pat_ident(segs[0].name) {
                            PatIdent::Const(idx) => {
                                // As above: a const pattern does not
                                // auto-deref, unless its own type is a
                                // reference.
                                if self.out.pat_derefs[pi] > 0 && !matches!(self.kind(p.consts[idx as usize].ty), TyKind::Ref(..)) {
                                    self.mismatch(span, scrut_t, t);
                                    return;
                                }
                                self.const_item_pat(pi, idx, t, span, in_match);
                                return;
                            }
                            PatIdent::Static => {
                                self.err(
                                    "L0110",
                                    span,
                                    "statics cannot be used as patterns",
                                    "Use a const item for a pattern, or compare with the static in a guard.",
                                );
                                return;
                            }
                            PatIdent::Variant(a, v) if p.adt(a).is_enum => {
                                let adt_ty = self.tys.adt_ty(a);
                                if !self.unify(adt_ty, t) {
                                    self.mismatch(span, t, adt_ty);
                                    return;
                                }
                                if p.adt(a).variants[v as usize].shape != VariantShape::Unit {
                                    self.err("L0110", span, "this variant has fields", "Match its fields with `(..)` or `{ .. }`.");
                                    return;
                                }
                                if self.hidden_variant(a, v, span) {
                                    return;
                                }
                                self.out.pat_res[pi] = PatRes::Variant(a, v);
                                return;
                            }
                            _ => {}
                        }
                    } else if let Some((cv, ct)) = self.primitive_const_pattern(segs) {
                        // As above: a const pattern does not auto-deref.
                        if self.out.pat_derefs[pi] > 0 {
                            self.mismatch(span, scrut_t, ct);
                            return;
                        }
                        if !self.unify(ct, t) {
                            self.mismatch(span, t, ct);
                            return;
                        }
                        self.out.pat_const[pi] = Some(cv);
                        return;
                    }
                }
                let target = if segs.len() == 1 {
                    let n = segs[0].name;
                    // The flat type table answers below; the binding query
                    // is the recorded read of that answer (ARCH 8.2).
                    if n != p.known.self_type {
                        self.binding(Namespace::Type, n);
                    }
                    let a = if n == p.known.self_type { self.self_adt() } else { p.type_names.get(&n).copied() };
                    // A struct pattern through a type alias (`SA { a }`);
                    // tuple-struct and unit patterns need the value
                    // namespace, which an alias does not fill (rustc E0532).
                    let a = match p.ast.pat(pat) {
                        Pat::Struct { .. } => a.or_else(|| self.alias_adt(n).map(|(a, _)| a)),
                        _ => a,
                    };
                    match a.filter(|&a| !p.adt(a).is_enum).map(|a| (a, 0)) {
                        Some(v) => Some(v),
                        // An imported variant in a tuple or struct pattern
                        // (`use E::*; B(n)`): resolve through the bindings.
                        None => match self.pat_ident(n) {
                            PatIdent::Variant(a, v) => Some((a, v)),
                            _ => None,
                        },
                    }
                } else {
                    match self.resolve_assoc(segs, span) {
                        Some(Res::Variant(a, v)) => Some((a, v)),
                        Some(_) => {
                            self.err("L0110", span, "expected a variant or struct in this pattern", "Use `Type::Variant`.");
                            None
                        }
                        None => return,
                    }
                };
                let Some((a, v)) = target else {
                    self.err("L0102", span, "unknown struct or variant in pattern", "Check the name.");
                    return;
                };
                // Written args on the pattern's path (`E::<u8>::A(x)`), and
                // a path through `Self` (the impl's own args), must name
                // the scrutinee's own type.
                let ty_seg = segs[segs.len().saturating_sub(2)].name;
                let via_self = ty_seg == p.known.self_type;
                let via_alias = self.alias_adt(ty_seg).is_some_and(|(_, args)| !args.is_empty());
                if (via_self || via_alias || segs[segs.len().saturating_sub(2)..].iter().any(|s| s.has_args()))
                    && !p.gx.adt_generics[a.0 as usize].params.is_empty()
                {
                    let written = self.value_path_args(a, segs, span);
                    let wt = self.tys.mk_adt(p.def_of_adt(a), &written);
                    if !self.unify(wt, t) {
                        self.mismatch(span, t, wt);
                        return;
                    }
                }
                // A generic Adt pattern matches the scrutinee's
                // own instance when mono has made it; before that
                // (and in templates) it matches the template with
                // the scrutinee's args substituted into its fields.
                let dt = self.deep(t);
                let scrut_args: Vec<GenericArg> = match self.tys.adt_parts(dt) {
                    Some((d, aa)) if d == p.def_of_adt(a) => self.tys.args(aa).to_vec(),
                    _ => Vec::new(),
                };
                let (a, adt_ty) = match self.tys.local_adt(dt) {
                    Some(inst) if inst != a && p.def_of_adt(inst) == p.def_of_adt(a) => (inst, dt),
                    _ if !scrut_args.is_empty() => (a, dt),
                    _ => (a, self.tys.adt_ty(a)),
                };
                if !self.unify(adt_ty, t) {
                    self.mismatch(span, t, adt_ty);
                    return;
                }
                self.out.pat_res[pi] = PatRes::Variant(a, v);
                let variant = &p.adt(a).variants[v as usize];
                match p.ast.pat(pat) {
                    Pat::Path(_) => {
                        if variant.shape != VariantShape::Unit {
                            self.err("L0110", span, "this variant has fields", "Match its fields with `(..)` or `{ .. }`.");
                        }
                    }
                    Pat::TupleStruct { elems, .. } => {
                        if variant.shape != VariantShape::Tuple {
                            self.err(
                                "L0110",
                                span,
                                format!("this variant has {} field(s)", variant.fields.len()),
                                "Match every field, or use `_` for the ones you do not need.",
                            );
                            return;
                        }
                        if !p.adt(a).is_enum {
                            self.check_ctor_vis(a, span);
                        }
                        let Some(mapped) = map_tuple_elems(p.ast, elems, variant.fields.len()) else {
                            self.err(
                                "L0110",
                                span,
                                format!("this variant has {} field(s)", variant.fields.len()),
                                "Match every field, use `_`, or skip the middle with `..`.",
                            );
                            return;
                        };
                        for (i, sub) in mapped {
                            let ft = variant.fields[i].ty;
                            let ft = if scrut_args.is_empty() { ft } else { self.subst_norm(ft, &scrut_args, span) };
                            self.pattern_mode(sub, ft, mode, in_match);
                        }
                    }
                    Pat::Struct { fields, rest, .. } => {
                        // Braces fit every shape, as in rustc: `U {}` for a
                        // unit struct, `P { 0: x, .. }` for a tuple struct.
                        if variant.shape == VariantShape::Unit && !fields.is_empty() {
                            self.err("L0110", span, "this variant does not have named fields", "Use the tuple form.");
                            return;
                        }
                        for &(fname, sub) in fields {
                            match variant.fields.iter().position(|f| f.name == fname) {
                                Some(i) => {
                                    self.check_field_vis(a, fname, p.ast.pat_span(sub));
                                    let ft = variant.fields[i].ty;
                                    let ft = if scrut_args.is_empty() { ft } else { self.subst_norm(ft, &scrut_args, span) };
                                    self.pattern_mode(sub, ft, mode, in_match);
                                }
                                None => {
                                    let s = p.ast.pat_span(sub);
                                    self.err(
                                        "L0103",
                                        s,
                                        format!("no field `{}` in this variant", self.name(fname)),
                                        "Check the field name.",
                                    );
                                }
                            }
                        }
                        if !rest && fields.len() < variant.fields.len() {
                            self.err(
                                "L0107",
                                span,
                                "pattern does not mention all fields",
                                "Add the missing fields, or end the pattern with `..`.",
                            );
                        }
                    }
                    _ => unreachable!(),
                }
            }
            Pat::Or(alts) => {
                // Every alternative binds the same names into the
                // same locals: the first alternative records its
                // bindings, later ones reuse them (see
                // `bind_pattern_local`). The scopes this pattern
                // leaves behind are the first alternative's.
                let alts: Vec<PatId> = alts.clone();
                if alts.is_empty() {
                    return;
                }
                let scope0 = self.scopes.len();
                let parent_log = self.or_log.take();
                self.or_log = Some(Vec::new());
                self.pattern_mode(alts[0], t, mode, in_match);
                let first_log = self.or_log.take().unwrap_or_default();
                self.or_log = parent_log;
                if let Some(log) = &mut self.or_log {
                    log.extend(first_log.iter().cloned());
                }
                let first_scope: Vec<((Sym, CtxtId), u32)> = self.scopes[scope0..].to_vec();
                for &alt in &alts[1..] {
                    self.scopes.truncate(scope0);
                    self.or_frames.push(OrFrame { seen: vec![false; first_log.len()], expected: first_log.clone(), extra: Vec::new() });
                    self.pattern_mode(alt, t, mode, in_match);
                    let frame = self.or_frames.pop().unwrap();
                    let alt_span = p.ast.pat_span(alt);
                    for (b, &seen) in frame.expected.iter().zip(&frame.seen) {
                        if !seen {
                            self.err(
                                "L0110",
                                alt_span,
                                format!("variable `{}` is not bound in all `|` alternatives", self.name(b.name)),
                                "Bind it in every alternative, or in none of them.",
                            );
                        }
                    }
                    for (name, s) in &frame.extra {
                        self.err(
                            "L0110",
                            *s,
                            format!("variable `{}` is not bound in all `|` alternatives", self.name(*name)),
                            "Bind it in every alternative, or in none of them.",
                        );
                    }
                }
                self.scopes.truncate(scope0);
                self.scopes.extend(first_scope);
            }
            Pat::Tuple(elems) => {
                if elems.is_empty() {
                    if !self.unify(t, UNIT) {
                        self.mismatch(span, t, UNIT);
                    }
                    return;
                }
                let elem_tys: Vec<Ty> = (0..elems.len()).map(|_| self.new_var(false)).collect();
                // A rest element means the arity is not the written count; take
                // element types from the scrutinee tuple when it is known.
                let known: Option<Vec<Ty>> = match self.kind(t) {
                    TyKind::Tuple(ts) => Some(self.tys.tys_of(ts).to_vec()),
                    _ => None,
                };
                match known {
                    Some(kt) => {
                        let Some(mapped) = map_tuple_elems(p.ast, elems, kt.len()) else {
                            self.err(
                                "L0110",
                                span,
                                format!("this tuple has {} element(s)", kt.len()),
                                "Match every element, use `_`, or skip the middle with `..`.",
                            );
                            return;
                        };
                        for (i, sub) in mapped {
                            self.pattern_mode(sub, kt[i], mode, in_match);
                        }
                    }
                    None => {
                        if elems.iter().any(|&s| matches!(p.ast.pat(s), Pat::Rest)) {
                            self.err(
                                "L0110",
                                span,
                                "cannot use `..` when the tuple type is not known",
                                "Add a type annotation, or match every element.",
                            );
                            return;
                        }
                        for (i, &sub) in elems.iter().enumerate() {
                            self.pattern_mode(sub, elem_tys[i], mode, in_match);
                        }
                        let ts = self.tys.intern_tys(&elem_tys);
                        let tt = self.tys.intern(TyKind::Tuple(ts));
                        if !self.unify(tt, t) {
                            self.mismatch(span, t, tt);
                        }
                    }
                }
            }
            // A bare `..` only appears inside tuple and slice forms, which map
            // it away before recursing; anywhere else it is a syntax error.
            Pat::Rest => {
                self.err("L0110", span, "`..` can only be used in tuple and slice patterns", "Remove the `..`.");
            }
            Pat::Slice { prefix, middle, suffix } => {
                let (elem, arr_len) = match self.kind(t) {
                    TyKind::Array(elem, c) => {
                        let n = match self.tys.const_kind(c) {
                            ConstKind::Int(n) => Some(n as u64),
                            _ => None,
                        };
                        (elem, n)
                    }
                    TyKind::Slice(elem) => (elem, None),
                    TyKind::Error => {
                        for &sub in prefix.iter().chain(suffix.iter()) {
                            self.pattern_mode(sub, ERROR, mode, in_match);
                        }
                        if let Some(mid) = middle {
                            if !matches!(p.ast.pat(*mid), Pat::Rest) {
                                self.pattern_mode(*mid, ERROR, mode, in_match);
                            }
                        }
                        return;
                    }
                    _ => {
                        let tn = self.tn(t);
                        self.err(
                            "L0110",
                            span,
                            format!("slice pattern cannot match a value of type `{tn}`"),
                            "Match on an array or a slice, for example `&value[..]`.",
                        );
                        for &sub in prefix.iter().chain(suffix.iter()) {
                            self.pattern_mode(sub, ERROR, mode, in_match);
                        }
                        return;
                    }
                };
                let fixed = (prefix.len() + suffix.len()) as u64;
                if let Some(n) = arr_len {
                    let bad = if middle.is_some() { fixed > n } else { fixed != n };
                    if bad {
                        self.err(
                            "L0110",
                            span,
                            format!("pattern requires {fixed} element(s) but the array has {n}"),
                            "Change the pattern length, or skip the middle with `..`.",
                        );
                        return;
                    }
                }
                for &sub in prefix.iter().chain(suffix.iter()) {
                    self.pattern_mode(sub, elem, mode, in_match);
                }
                if let Some(mid) = middle {
                    match p.ast.pat(*mid) {
                        Pat::Rest | Pat::Wild => {}
                        Pat::Binding { by_ref: true, .. } => {
                            let st = self.tys.intern(TyKind::Slice(elem));
                            self.pattern_mode(*mid, st, mode, in_match);
                        }
                        Pat::Binding { .. } => match (mode, arr_len) {
                            (BindMode::Move, Some(n)) => {
                                let c = self.tys.intern_const(ConstKind::Int((n - fixed) as u128));
                                let at = self.tys.intern(TyKind::Array(elem, c));
                                self.pattern_mode(*mid, at, BindMode::Move, in_match);
                            }
                            (BindMode::Move, None) => {
                                self.err(
                                    "L0110",
                                    span,
                                    "cannot bind the middle of a slice pattern by value",
                                    "Match on a reference, or use `ref` for the binding.",
                                );
                            }
                            (BindMode::Ref(_), _) => {
                                let st = self.tys.intern(TyKind::Slice(elem));
                                self.pattern_mode(*mid, st, mode, in_match);
                            }
                        },
                        _ => {
                            let st = self.tys.intern(TyKind::Slice(elem));
                            self.pattern_mode(*mid, st, mode, in_match);
                        }
                    }
                }
            }
            Pat::Paren(inner) => self.pattern_mode(*inner, t, mode, in_match),
            // AST v2 pattern forms the parser still rejects.
            Pat::QPath { .. } | Pat::MacroCall(_) => {}
        }
    }

    /// `Some(p)` is Some(true), `None` is Some(false), anything else is None.
    /// True when `path` is `<parent>::<last>` with the parent in a
    /// plain or canonical std spelling (`Option::Some`,
    /// `std::option::Option::Some`).
    fn std_parent_path(&self, path: &[ast::PathSeg], parent: Sym, last: Sym) -> bool {
        if path.len() < 2 || path[path.len() - 1].name != last {
            return false;
        }
        let head = &path[..path.len() - 1];
        if head.len() == 1 {
            return head[0].name == parent;
        }
        if head[head.len() - 1].name != parent {
            return false;
        }
        let names: Vec<&str> = head.iter().map(|s| self.p.interner.get(s.name)).collect();
        crate::ty::lang::std_path_kind(&names) == Some(crate::ty::lang::StdPathKind::Type)
    }

    fn option_pattern(&self, pat: PatId) -> Option<bool> {
        let k = self.p.known;
        match self.p.ast.pat(pat) {
            Pat::Binding { name, mutable: false, by_ref: false } if *name == k.None => Some(false),
            Pat::Path(segs) if self.std_parent_path(segs, k.Option, k.None) => Some(false),
            Pat::TupleStruct { path, elems }
                if elems.len() == 1 && ((path.len() == 1 && path[0].name == k.Some) || self.std_parent_path(path, k.Option, k.Some)) =>
            {
                Some(true)
            }
            _ => None,
        }
    }

    /// `Ok(..)` as `Some(true)`, `Err(..)` as `Some(false)`, in the
    /// prelude spelling and the qualified `Result::Ok(..)` spelling.
    fn result_pattern(&self, pat: PatId) -> Option<bool> {
        let k = self.p.known;
        match self.p.ast.pat(pat) {
            Pat::TupleStruct { path, elems } if elems.len() == 1 => {
                let last = path.last().map(|s| s.name)?;
                if (path.len() == 1 && last == k.Ok) || self.std_parent_path(path, k.Result, k.Ok) {
                    Some(true)
                } else if (path.len() == 1 && last == k.Err) || self.std_parent_path(path, k.Result, k.Err) {
                    Some(false)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Exhaustiveness for `match`, by the usefulness check in
    /// `usefulness.rs`. Patterns it cannot read still make it
    /// reject a match that Rust accepts (lust is a subset).
    fn exhaustive(&mut self, scrut_ty: Ty, arms: &[ast::Arm], span: Span) {
        let p = self.p;
        let pats: Vec<PatId> = arms.iter().filter(|a| a.guard.is_none()).map(|a| a.pat).collect();
        if self.covers(&pats) {
            return;
        }
        let (_, base) = self.autoderef(scrut_ty);
        let msg = match self.tys.local_adt(base) {
            Some(a) if p.adt(a).is_enum => {
                let mut flat = Vec::new();
                pats.iter().for_each(|&x| self.flatten_or(x, &mut flat));
                let missing: Vec<String> = (0..p.adt(a).variants.len())
                    .filter(|&v| !flat.iter().any(|&x| matches!(self.pres(x), PatRes::Variant(_, w) if w as usize == v)))
                    .map(|v| format!("{}::{}", p.display_path(p.adt(a).name), self.name(p.adt(a).variants[v].name)))
                    .collect();
                if missing.is_empty() {
                    "non-exhaustive match: some nested cases are missing".to_string()
                } else {
                    format!("non-exhaustive match: missing {}", missing.join(", "))
                }
            }
            _ if self.kind(base) == TyKind::Error => return,
            _ => "non-exhaustive match".to_string(),
        };
        self.err("L0115", span, msg, "Add arms for the missing cases, or add a `_ => ...` arm.");
    }

    /// Follows `@`, parenthesized, and reference wrappers to the pattern they
    /// wrap. For exhaustiveness only: a reference wrapper adds no condition.
    fn pat_unwrap(&self, mut pat: PatId) -> PatId {
        loop {
            match self.p.ast.pat(pat) {
                Pat::At { inner, .. } | Pat::Paren(inner) | Pat::Ref { inner, .. } => pat = *inner,
                _ => return pat,
            }
        }
    }

    fn pres(&self, pat: PatId) -> PatRes {
        // An `@` or parenthesized wrapper takes the resolution of what it wraps
        // for exhaustiveness, when the wrapped pattern has a variant or
        // Option resolution of its own.
        let own = self.out.pat_res[(pat.0 - self.out.pat_base) as usize];
        match self.p.ast.pat(pat) {
            Pat::At { inner, .. } | Pat::Paren(inner) | Pat::Ref { inner, .. } => match self.pres(*inner) {
                r @ (PatRes::Variant(..) | PatRes::Opt(_) | PatRes::Res(_)) => r,
                _ => own,
            },
            _ => own,
        }
    }

    fn flatten_or(&self, pat: PatId, out: &mut Vec<PatId>) {
        match self.p.ast.pat(pat) {
            Pat::Or(alts) => alts.iter().for_each(|&a| self.flatten_or(a, out)),
            _ => out.push(pat),
        }
    }

    /// An order-preserving key for an integer or char scalar at type
    /// `t`: raw bits, with the sign bit flipped for signed types.
    fn scalar_key(&self, v: i128, t: Ty) -> Option<u128> {
        match self.kind(t) {
            TyKind::Int(it) => {
                let bits = if it.bits() >= 128 { v as u128 } else { (v as u128) & ((1u128 << it.bits()) - 1) };
                Some(if it.signed() { bits ^ (1u128 << (it.bits() - 1)) } else { bits })
            }
            TyKind::Char => Some(v as u32 as u128),
            _ => None,
        }
    }

    /// The scalar value a pattern matches as a single point, if it is one.
    fn pat_scalar(&self, pat: PatId) -> Option<i128> {
        let pi = (pat.0 - self.out.pat_base) as usize;
        if let Some(cv) = &self.out.pat_const[pi] {
            return match cv {
                crate::ty::consteval::ConstValue::Int(v) => Some(*v),
                crate::ty::consteval::ConstValue::Char(c) => Some(*c as i128),
                _ => None,
            };
        }
        if let PatRes::ConstItem(idx) = self.out.pat_res[pi] {
            return match &self.p.consts[idx as usize].value {
                crate::ty::consteval::ConstValue::Int(v) => Some(*v),
                crate::ty::consteval::ConstValue::Char(c) => Some(*c as i128),
                _ => None,
            };
        }
        match self.p.ast.pat(self.pat_unwrap(pat)) {
            Pat::Lit(l) => self.const_scalar(*l),
            _ => None,
        }
    }

    /// True when a checked pattern matches every value of its
    /// type: the syntactic `irrefutable` test, or, for a pattern
    /// that contains an or-pattern, the exhaustiveness test
    /// (`A(x) | B(x)` over a two-variant enum always matches, as
    /// in Rust).
    fn pat_always_matches(&self, pat: PatId) -> bool {
        if self.irrefutable(pat) {
            return true;
        }
        fn has_or(p: &Program, pat: PatId) -> bool {
            match p.ast.pat(pat) {
                Pat::Or(_) => true,
                Pat::TupleStruct { elems, .. } | Pat::Tuple(elems) => elems.iter().any(|&e| has_or(p, e)),
                Pat::Struct { fields, .. } => fields.iter().any(|&(_, s)| has_or(p, s)),
                Pat::Slice { prefix, middle, suffix } => prefix.iter().chain(suffix.iter()).chain(middle.iter()).any(|&s| has_or(p, s)),
                Pat::At { inner, .. } | Pat::Paren(inner) | Pat::Ref { inner, .. } => has_or(p, *inner),
                _ => false,
            }
        }
        has_or(self.p, pat) && self.covers(&[pat])
    }

    /// True when a guarded arm's pattern binds a slice
    /// middle by value (an owned array) whose elements are not
    /// `Copy`, or also binds through an or-pattern: those arms
    /// bind before the guard runs, so drop order (and guard
    /// retry) would differ from Rust. See the call in the
    /// `match` check.
    fn slice_middle_move_blocks_guard(&self, root: PatId) -> bool {
        fn has_binding(cx: &Ctx, pat: PatId) -> bool {
            matches!(cx.out.pat_res[(pat.0 - cx.out.pat_base) as usize], PatRes::Binding { .. })
                || children(cx, pat).into_iter().any(|s| has_binding(cx, s))
        }
        fn has_or_binding(cx: &Ctx, pat: PatId) -> bool {
            (matches!(cx.p.ast.pat(pat), Pat::Or(_)) && has_binding(cx, pat))
                || children(cx, pat).into_iter().any(|s| has_or_binding(cx, s))
        }
        fn children(cx: &Ctx, pat: PatId) -> Vec<PatId> {
            match cx.p.ast.pat(pat) {
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
        fn walk(cx: &Ctx, root: PatId, pat: PatId) -> bool {
            if let Pat::Slice { middle, .. } = cx.p.ast.pat(pat)
                && let Some(mid) = middle
                && has_binding(cx, *mid)
                && let TyKind::Array(elem, _) = cx.kind(cx.out.pat_ty[(mid.0 - cx.out.pat_base) as usize])
                && (!is_copy(cx.p, &cx.tys, elem) || has_or_binding(cx, root))
            {
                return true;
            }
            children(cx, pat).into_iter().any(|s| walk(cx, root, s))
        }
        walk(self, root, root)
    }

    fn irrefutable(&self, pat: PatId) -> bool {
        let p = self.p;
        // A struct, or an enum with one variant (rustc: exhaustive).
        let one_variant = |a: AdtId| !p.adt(a).is_enum || p.adt(a).variants.len() == 1;
        if matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Opt(_) | PatRes::Res(_)) {
            return false;
        }
        match p.ast.pat(pat) {
            Pat::Wild => true,
            // A binding that resolved to a const item can fail; one
            // that resolved to a unit struct cannot.
            Pat::Binding { .. } => match self.out.pat_res[(pat.0 - self.out.pat_base) as usize] {
                PatRes::Variant(a, _) => one_variant(a),
                PatRes::Binding { .. } | PatRes::None => self.out.pat_const[(pat.0 - self.out.pat_base) as usize].is_none(),
                _ => false,
            },
            Pat::Or(alts) => alts.iter().any(|&a| self.irrefutable(a)),
            Pat::Struct { fields, .. } => {
                matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Variant(a, _) if one_variant(a))
                    && fields.iter().all(|&(_, s)| self.irrefutable(s))
            }
            Pat::TupleStruct { elems, .. } => {
                matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Variant(a, _) if one_variant(a))
                    && elems.iter().all(|&s| self.irrefutable(s))
            }
            Pat::Path(_) => {
                self.out.pat_const[(pat.0 - self.out.pat_base) as usize].is_none()
                    && !matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::ConstItem(_))
                    && matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Variant(a, _) if one_variant(a))
            }
            Pat::Tuple(elems) => elems.iter().all(|&s| matches!(p.ast.pat(s), Pat::Rest) || self.irrefutable(s)),
            Pat::Ref { inner, .. } => self.irrefutable(*inner),
            Pat::At { inner, .. } => self.irrefutable(*inner),
            Pat::Slice { prefix, middle, suffix } => {
                // The pattern matches every value only if it matches every
                // length: an array needs an exact-length pattern, or a `..`
                // with at most the array's length fixed; a slice needs a
                // lone `..` (`[]` matches only the empty slice, and
                // `[.., a]` misses it too).
                let t = self.out.pat_ty[(pat.0 - self.out.pat_base) as usize];
                let fixed = (prefix.len() + suffix.len()) as u128;
                let len_ok = match self.kind(t) {
                    TyKind::Array(_, c) => match self.tys.const_kind(c) {
                        ConstKind::Int(n) => {
                            if middle.is_some() {
                                fixed <= n
                            } else {
                                fixed == n
                            }
                        }
                        _ => false,
                    },
                    _ => middle.is_some() && fixed == 0,
                };
                len_ok
                    && middle.is_none_or(|m| matches!(p.ast.pat(m), Pat::Rest) || self.irrefutable(m))
                    && prefix.iter().chain(suffix.iter()).all(|&s| self.irrefutable(s))
            }
            Pat::Paren(inner) => self.irrefutable(*inner),
            Pat::Rest => true,
            _ => false,
        }
    }

    // ---------- Known-value overflow lint (rustc `arithmetic_overflow`) ----------

    /// The deny-level lints rustc runs over known values, mirrored from
    /// its MIR const-prop behavior (probed against rustc): an arithmetic
    /// operation on operands known at compile time that would overflow
    /// is an error (`arithmetic_overflow`, L0540), and so is an
    /// operation that always panics: division or remainder by a known
    /// zero, `MIN / -1`, and an index known to be out of bounds for an
    /// array type (`unconditional_panic`, L0541). The pass walks the
    /// checked body once, tracking scalar locals whose value is known.
    /// The tracked set follows the probed rules: a local whose address
    /// is taken anywhere is never tracked, knowledge does not survive a
    /// control-flow join for locals assigned on either side, a write
    /// through a field or index place drops the whole aggregate, reads
    /// through references and enum payloads are unknown, and an
    /// operation that stores back into the local it reads
    /// (`a = a + 1`, `a += 1`) does not fire.
    fn overflow_lint(&mut self) {
        let p = self.p;
        let allow_arith = self.f.def.attrs.iter().any(|a| crate::check::allow_attr(a, p.interner, "arithmetic_overflow"));
        let allow_panic = self.f.def.attrs.iter().any(|a| crate::check::allow_attr(a, p.interner, "unconditional_panic"));
        if allow_arith && allow_panic {
            return;
        }
        let Some(body) = self.f.def.body else { return };
        let mut lint = KLint {
            addressed: vec![false; self.out.locals.len()],
            frames: Vec::new(),
            suppress: None,
            dead: false,
            allow_arith,
            allow_panic,
            stmt_allow_arith: 0,
            stmt_allow_panic: 0,
        };
        // A local whose address is taken anywhere in the body is not tracked.
        for i in 0..self.out.expr_ty.len() {
            let e = ExprId(self.out.expr_base + i as u32);
            match p.ast.expr(e) {
                Expr::Ref { expr, .. } => {
                    if let Some(root) = self.k_place_root(*expr) {
                        lint.addressed[root as usize] = true;
                    }
                }
                Expr::MethodCall { recv, .. } => {
                    let res = self.out.expr_res[i];
                    let ar = match res {
                        Res::Method { autoref, .. } | Res::BuiltinMethod { autoref, .. } => autoref,
                        _ => Autoref::None,
                    };
                    if ar != Autoref::None
                        && let Some(root) = self.k_place_root(*recv)
                    {
                        lint.addressed[root as usize] = true;
                    }
                }
                Expr::Macro { kind, args, .. } => {
                    // Format arguments are borrowed (as in `macro_expr`).
                    let borrowed: &[ExprId] = match kind {
                        ast::MacroKind::AssertEq | ast::MacroKind::AssertNe => &args[..args.len().min(2)],
                        ast::MacroKind::Vec | ast::MacroKind::Assert => &[],
                        _ => args,
                    };
                    for &a in borrowed {
                        if matches!(p.ast.expr(a), Expr::Path(_) | Expr::Field { .. } | Expr::TupleField { .. } | Expr::Index { .. })
                            && let Some(root) = self.k_place_root(a)
                        {
                            lint.addressed[root as usize] = true;
                        }
                    }
                }
                _ => {}
            }
        }
        // A captured variable can change behind the closure: do not track it.
        for c in &self.out.closures {
            for cap in &c.captures {
                lint.addressed[cap.root as usize] = true;
            }
        }
        let mut env: KEnv = vec![None; self.out.locals.len()];
        self.k_block(body, &mut env, &mut lint);
        // Each closure body is its own MIR body in rustc: lint it with
        // nothing known on entry.
        let bodies: Vec<ExprId> = self
            .out
            .closures
            .iter()
            .filter_map(|c| match p.ast.expr(c.expr) {
                Expr::Closure { body, .. } => Some(*body),
                _ => None,
            })
            .collect();
        for b in bodies {
            let mut env: KEnv = vec![None; self.out.locals.len()];
            lint.frames.clear();
            lint.dead = false;
            lint.suppress = None;
            self.k_expr(b, &mut env, &mut lint);
        }
    }

    /// Zonks the closure records into `Checked`. A closure stored inside
    /// an Adt (a struct field, `Option`, `Vec`) holds its captures' loans
    /// through the Adt's type args, which the borrow checker tracks
    /// (W-BORROW closure contract), as it does a closure that returns a
    /// reference.
    fn finish_closures(&mut self) {
        for mut c in std::mem::take(&mut self.closures) {
            // A signature nothing fixed is an annotation error (rustc
            // E0282), never a silent default.
            if c.inputs.iter().chain([&c.output]).any(|&t| self.has_unbound_var(t) && !self.has_error_kind(t)) {
                let span = self.span(c.expr);
                self.err(
                    "L0610",
                    span,
                    "type annotations needed: cannot infer the closure's signature",
                    "Annotate the closure parameters, or use the closure where an Fn bound fixes them.",
                );
            }
            c.output = self.zonk(c.output);
            for t in c.inputs.iter_mut() {
                *t = self.zonk(*t);
            }
            for cap in c.captures.iter_mut() {
                cap.place_ty = self.zonk(cap.place_ty);
            }
            c.ty = self.zonk(c.ty);
            self.out.closures.push(c);
        }
    }

    /// The root local of a place expression, if the place is one.
    fn k_place_root(&self, e: ExprId) -> Option<u32> {
        match self.out.expr_res[self.ei(e)] {
            Res::Local(l) => return Some(l),
            _ => {}
        }
        match self.p.ast.expr(e) {
            Expr::Field { base, .. } | Expr::TupleField { base, .. } | Expr::Index { base, .. } => self.k_place_root(*base),
            _ => None,
        }
    }

    /// True when `t` is the `u128` type, whose known values are bit
    /// patterns rather than mathematical i128 values.
    fn k_is_u128(&self, t: Ty) -> bool {
        matches!(self.tys.kind(t), TyKind::Int(it) if !it.signed() && it.bits() >= 128)
    }

    /// The bit width of an integer type, when `t` is one.
    fn k_bits(&self, t: Ty) -> Option<u32> {
        match self.tys.kind(t) {
            TyKind::Int(it) => Some(it.bits()),
            _ => None,
        }
    }

    /// Orders two known values at integer type `t` (in the u128 domain
    /// for `u128`, where the stored i128 is only the bit pattern).
    fn k_cmp(&self, a: i128, b: i128, t: Ty) -> std::cmp::Ordering {
        if self.k_is_u128(t) { (a as u128).cmp(&(b as u128)) } else { a.cmp(&b) }
    }

    /// The mathematical value of an i128 seen at integer type `t`. For
    /// `u128` the bits pass through unchanged (see `KVal`).
    fn k_math(&self, v: i128, t: Ty) -> Option<i128> {
        match self.tys.kind(t) {
            TyKind::Int(it) => {
                let bits = it.bits();
                if it.signed() {
                    Some(crate::ty::consteval::truncate_to_int(v, it))
                } else if bits >= 128 {
                    Some(v)
                } else {
                    Some(v & ((1i128 << bits) - 1))
                }
            }
            _ => Some(v),
        }
    }

    /// Wraps an i128 to the range of its integer type (loss is intended:
    /// the value continues as the wrapped result, as in a wrapping op).
    fn k_wrap(&self, v: i128, t: Ty) -> Option<i128> {
        self.k_math(v, t)
    }

    /// The value range of an integer type, when it fits in i128 values.
    fn k_range(&self, t: Ty) -> Option<(IntTy, i128, i128)> {
        match self.tys.kind(t) {
            TyKind::Int(it) => {
                let bits = it.bits();
                if bits >= 128 {
                    if it.signed() { Some((it, i128::MIN, i128::MAX)) } else { None }
                } else if it.signed() {
                    Some((it, -(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1))
                } else {
                    Some((it, 0, (1i128 << bits) - 1))
                }
            }
            _ => None,
        }
    }

    fn k_fire(&mut self, span: Span, lint: &KLint) {
        if lint.allow_arith || lint.stmt_allow_arith > 0 {
            return;
        }
        self.err(
            "L0540",
            span,
            "this arithmetic operation will overflow",
            "Change the values or the type. If the wrap is intended, use a `wrapping_*` operation.",
        );
    }

    /// The `unconditional_panic` fire: an operation on known values
    /// that always panics when it runs.
    fn k_fire_panic(&mut self, span: Span, lint: &KLint, what: &str, fix: &'static str) {
        if lint.allow_panic || lint.stmt_allow_panic > 0 {
            return;
        }
        self.err("L0541", span, format!("{what}: this operation will panic at runtime"), fix);
    }

    /// Reports an out-of-bounds index when the base expression has an
    /// array type (through any number of references) and the index
    /// value is known. Slice and `Vec` bases keep a runtime length
    /// rustc does not const-propagate, so they never fire here.
    fn k_check_index(&mut self, base: ExprId, iv: &Option<KVal>, span: Span, lint: &KLint) {
        let Some(KVal::Int(i)) = iv else { return };
        let mut t = self.out.expr_ty[self.ei(base)];
        loop {
            match self.tys.kind(t) {
                TyKind::Ref(_, _, e) => t = e,
                _ => break,
            }
        }
        let TyKind::Array(_, c) = self.tys.kind(t) else { return };
        let crate::ty::ConstKind::Int(len) = self.tys.const_kind(c) else { return };
        if *i < 0 || *i as u128 >= len {
            self.k_fire_panic(span, lint, "index out of bounds", "Change the index or the array length.");
        }
    }

    /// Places whose writes change a tracked local, found by span within
    /// the given regions (a loop body and its condition).
    fn k_assigned_in(&self, regions: &[Span]) -> Vec<u32> {
        let mut out = Vec::new();
        for i in 0..self.out.expr_ty.len() {
            let e = ExprId(self.out.expr_base + i as u32);
            let lhs = match self.p.ast.expr(e) {
                Expr::Assign { lhs, .. } | Expr::AssignOp { lhs, .. } => *lhs,
                _ => continue,
            };
            let sp = self.p.ast.expr_span(e);
            if regions.iter().any(|r| r.file == sp.file && r.lo <= sp.lo && sp.hi <= r.hi)
                && let Some(root) = self.k_place_root(lhs)
                && !out.contains(&root)
            {
                out.push(root);
            }
        }
        out
    }

    /// Records a value for a local, unless its address is taken.
    fn k_set(env: &mut KEnv, lint: &KLint, local: u32, v: Option<KVal>) {
        if !lint.addressed.get(local as usize).copied().unwrap_or(false) {
            env[local as usize] = v;
        }
    }

    /// Drops the knowledge of every local assigned in the given regions:
    /// after a control-flow join, a local assigned on any side is no
    /// longer known, even if all sides assign the same value.
    fn k_poison(&self, env: &mut KEnv, regions: &[Span]) {
        for r in self.k_assigned_in(regions) {
            env[r as usize] = None;
        }
    }

    /// True when a block cannot complete: a statement or its tail has
    /// type `!` (a return, a panic, a diverging call, a break).
    fn k_block_diverges(&self, b: ast::BlockId) -> bool {
        let block = self.p.ast.block(b);
        let never = |e: ExprId| self.tys.kind(self.out.expr_ty[self.ei(e)]) == TyKind::Never;
        block.stmts.iter().any(|s| match s {
            Stmt::Expr { expr, .. } => never(*expr),
            Stmt::Let { init, .. } => init.is_some_and(|i| never(i)),
            _ => false,
        }) || block.tail.is_some_and(never)
    }

    /// Binds the known value of a scrutinee into a pattern's locals.
    /// Tuple and struct projections keep their component values; enum
    /// payload bindings are unknown (the probed rustc behavior).
    fn k_bind_pat(&mut self, pat: PatId, v: &Option<KVal>, env: &mut KEnv, lint: &KLint) {
        let p = self.p;
        let pres = self.out.pat_res[(pat.0 - self.out.pat_base) as usize];
        match p.ast.pat(pat) {
            Pat::Binding { .. } => {
                if let PatRes::Binding { local, mode } = pres {
                    let val = if mode == BindMode::Move { v.clone() } else { None };
                    Self::k_set(env, lint, local, val);
                }
            }
            Pat::At { inner, .. } => {
                if let PatRes::Binding { local, mode } = pres {
                    let val = if mode == BindMode::Move { v.clone() } else { None };
                    Self::k_set(env, lint, local, val);
                }
                self.k_bind_pat(*inner, v, env, lint);
            }
            Pat::Tuple(elems) => {
                if let Some(KVal::Agg(items)) = v
                    && let Some(map) = map_tuple_elems(p.ast, elems, items.len())
                {
                    for (idx, sub) in map {
                        self.k_bind_pat(sub, &items[idx].clone(), env, lint);
                    }
                } else {
                    for &sub in elems {
                        self.k_bind_pat(sub, &None, env, lint);
                    }
                }
            }
            Pat::TupleStruct { elems, .. } => {
                let struct_val = match pres {
                    PatRes::Variant(a, _) if !p.adt(a).is_enum => v.clone(),
                    _ => None,
                };
                match &struct_val {
                    Some(KVal::Agg(items)) => match map_tuple_elems(p.ast, elems, items.len()) {
                        Some(map) => {
                            for (idx, sub) in map {
                                self.k_bind_pat(sub, &items[idx].clone(), env, lint);
                            }
                        }
                        None => {
                            for &sub in elems {
                                self.k_bind_pat(sub, &None, env, lint);
                            }
                        }
                    },
                    _ => {
                        for &sub in elems {
                            self.k_bind_pat(sub, &None, env, lint);
                        }
                    }
                }
            }
            Pat::Struct { fields, .. } => {
                let struct_fields = match pres {
                    PatRes::Variant(a, var) if !p.adt(a).is_enum => {
                        Some(p.adt(a).variants[var as usize].fields.iter().map(|f| f.name).collect::<Vec<_>>())
                    }
                    _ => None,
                };
                for &(fname, sub) in fields {
                    let slot = match (v, &struct_fields) {
                        (Some(KVal::Agg(items)), Some(names)) => {
                            names.iter().position(|&n| n == fname).and_then(|i| items.get(i)).cloned().unwrap_or(None)
                        }
                        _ => None,
                    };
                    self.k_bind_pat(sub, &slot, env, lint);
                }
            }
            Pat::Slice { prefix, suffix, .. } => match v {
                Some(KVal::Agg(items)) if items.len() >= prefix.len() + suffix.len() => {
                    for (i, &sub) in prefix.iter().enumerate() {
                        self.k_bind_pat(sub, &items[i].clone(), env, lint);
                    }
                    for (j, &sub) in suffix.iter().enumerate() {
                        self.k_bind_pat(sub, &items[items.len() - suffix.len() + j].clone(), env, lint);
                    }
                }
                _ => {
                    for &sub in prefix.iter().chain(suffix.iter()) {
                        self.k_bind_pat(sub, &None, env, lint);
                    }
                }
            },
            Pat::Or(alts) => {
                // A binding is known after an or-pattern only
                // when every alternative binds it to the same
                // known value; the matched alternative is the
                // only one that runs.
                let mut merged: Option<KEnv> = None;
                for &a in alts {
                    let mut alt_env = env.clone();
                    self.k_bind_pat(a, v, &mut alt_env, lint);
                    match &mut merged {
                        None => merged = Some(alt_env),
                        Some(m) => {
                            for (slot, other) in m.iter_mut().zip(alt_env) {
                                if *slot != other {
                                    *slot = None;
                                }
                            }
                        }
                    }
                }
                if let Some(m) = merged {
                    *env = m;
                }
            }
            Pat::Ref { inner, .. } | Pat::Paren(inner) => self.k_bind_pat(*inner, &None, env, lint),
            _ => {}
        }
    }

    /// Pushes statement-level `#[allow(..)]` counters for `attrs`;
    /// returns which counters rose, for `k_allow_pop`.
    fn k_allow_push(&self, attrs: &[ast::Attr], lint: &mut KLint) -> (bool, bool) {
        let arith = attrs.iter().any(|a| crate::check::allow_attr(a, self.p.interner, "arithmetic_overflow"));
        let panic_ = attrs.iter().any(|a| crate::check::allow_attr(a, self.p.interner, "unconditional_panic"));
        lint.stmt_allow_arith += u32::from(arith);
        lint.stmt_allow_panic += u32::from(panic_);
        (arith, panic_)
    }

    fn k_allow_pop(&self, pushed: (bool, bool), lint: &mut KLint) {
        lint.stmt_allow_arith -= u32::from(pushed.0);
        lint.stmt_allow_panic -= u32::from(pushed.1);
    }

    fn k_block(&mut self, b: ast::BlockId, env: &mut KEnv, lint: &mut KLint) -> Option<KVal> {
        // A block-level `#![allow(..)]` covers the whole block.
        let pushed = self.k_allow_push(&self.p.ast.block(b).inner_attrs.clone(), lint);
        let v = self.k_block_body(b, env, lint);
        self.k_allow_pop(pushed, lint);
        v
    }

    fn k_block_body(&mut self, b: ast::BlockId, env: &mut KEnv, lint: &mut KLint) -> Option<KVal> {
        let p = self.p;
        if lint.dead {
            return None;
        }
        let block = p.ast.block(b);
        for stmt in &block.stmts {
            if lint.dead {
                return None;
            }
            let diverges = match stmt {
                Stmt::Let { pat, init, els, attrs, .. } => {
                    // A statement-level `#[allow(..)]` covers this let.
                    let pushed = self.k_allow_push(attrs, lint);
                    let v = init.map(|i| self.k_expr(i, env, lint)).unwrap_or(None);
                    self.k_bind_pat(*pat, &v, env, lint);
                    if let Some(els) = els {
                        let mut eenv = env.clone();
                        self.k_block(*els, &mut eenv, lint);
                    }
                    self.k_allow_pop(pushed, lint);
                    init.is_some_and(|i| self.tys.kind(self.out.expr_ty[self.ei(i)]) == TyKind::Never)
                }
                Stmt::Expr { expr, attrs, .. } => {
                    // A statement-level `#[allow(..)]` covers this expr.
                    let pushed = self.k_allow_push(attrs, lint);
                    self.k_expr(*expr, env, lint);
                    self.k_allow_pop(pushed, lint);
                    self.tys.kind(self.out.expr_ty[self.ei(*expr)]) == TyKind::Never
                }
                Stmt::Item(_) | Stmt::Macro { .. } => false,
            };
            if diverges {
                return None;
            }
        }
        if lint.dead {
            return None;
        }
        match block.tail {
            Some(tail) => {
                // An outer `#[allow(..)]` on the tail covers it.
                let pushed = self.k_allow_push(&block.tail_attrs.clone(), lint);
                let v = self.k_expr(tail, env, lint);
                self.k_allow_pop(pushed, lint);
                v
            }
            None => None,
        }
    }

    /// A recorded const value as a known value, if it is scalar or an
    /// aggregate of knowns.
    fn k_const(&self, cv: &crate::ty::consteval::ConstValue, t: Ty) -> Option<KVal> {
        use crate::ty::consteval::ConstValue as CV;
        match cv {
            CV::Int(v) => self.k_math(*v, t).map(KVal::Int),
            CV::Bool(b) => Some(KVal::Bool(*b)),
            CV::Char(c) => Some(KVal::Int(*c as i128)),
            CV::Variant(v, _) => match self.tys.kind(t) {
                TyKind::Adt(def, _) => match self.p.adt_by_def(def) {
                    Some(a) if self.p.adt(a).is_enum => Some(KVal::Enum(a, *v)),
                    _ => None,
                },
                _ => None,
            },
            CV::Aggregate(vals) => Some(KVal::Agg(vals.iter().map(|v| self.k_const(v, ERROR)).collect())),
            _ => None,
        }
    }

    /// Walks one expression, lints overflowing operations with known
    /// operands, applies assignment effects to `env`, and returns the
    /// expression's known value when there is one.
    fn k_expr(&mut self, e: ExprId, env: &mut KEnv, lint: &mut KLint) -> Option<KVal> {
        let p = self.p;
        let span = self.span(e);
        let ety = self.out.expr_ty[self.ei(e)];
        if let Some(cv) = &self.out.const_exprs[self.ei(e)] {
            return self.k_const(cv, ety);
        }
        match p.ast.expr(e) {
            Expr::Int(v, _) => Some(KVal::Int(*v as u128 as i128)),
            Expr::Bool(b) => Some(KVal::Bool(*b)),
            Expr::Char(c) => Some(KVal::Int(*c as i128)),
            Expr::Path(_) | Expr::SelfValue => match self.out.expr_res[self.ei(e)] {
                Res::Local(l) => env.get(l as usize).cloned().unwrap_or(None),
                Res::Variant(a, v) if p.adt(a).is_enum => Some(KVal::Enum(a, v)),
                _ => None,
            },
            Expr::Block(b) | Expr::UnsafeBlock(b) => self.k_block(*b, env, lint),
            Expr::ConstBlock(_) => None,
            Expr::LabeledBlock { label, body } => {
                lint.frames.push((Some(label.name), Vec::new()));
                let v = self.k_block(*body, env, lint);
                let (_, breaks) = lint.frames.pop().unwrap();
                match (breaks.len(), v) {
                    (0, v) => v,
                    (1, None) => breaks.into_iter().next().unwrap(),
                    _ => None,
                }
            }
            Expr::If { cond, then, els } => {
                let cv = self.k_expr(*cond, env, lint);
                let then_span = p.ast.block(*then).span;
                let els_span = els.map(|x| self.span(x));
                if let Some(KVal::Bool(b)) = cv {
                    // Only the taken side runs (dead-side operations do not
                    // fire); locals it assigns are still lost at the join,
                    // and if it diverges, what follows is unreachable.
                    let saved = lint.dead;
                    lint.dead = false;
                    let side_span = if b {
                        self.k_block(*then, env, lint);
                        then_span
                    } else {
                        match els {
                            Some(els) => {
                                self.k_expr(*els, env, lint);
                                self.span(*els)
                            }
                            None => span,
                        }
                    };
                    let side_diverges = lint.dead
                        || if b {
                            self.k_block_diverges(*then)
                        } else {
                            els.is_some_and(|x| self.tys.kind(self.out.expr_ty[self.ei(x)]) == TyKind::Never)
                        };
                    lint.dead = saved || side_diverges;
                    if els.is_some() || b {
                        self.k_poison(env, &[side_span]);
                    }
                    return None;
                }
                let saved = lint.dead;
                lint.dead = false;
                let mut tenv = env.clone();
                self.k_block(*then, &mut tenv, lint);
                lint.dead = false;
                if let Some(els) = els {
                    let mut eenv = env.clone();
                    self.k_expr(*els, &mut eenv, lint);
                }
                lint.dead = saved;
                match els_span {
                    Some(es) => self.k_poison(env, &[then_span, es]),
                    None => self.k_poison(env, &[then_span]),
                }
                None
            }
            Expr::While { label, cond, body } => {
                let regions = [self.span(*cond), p.ast.block(*body).span];
                let poison = self.k_assigned_in(&regions);
                let mut lenv = env.clone();
                for &r in &poison {
                    lenv[r as usize] = None;
                }
                let saved = lint.dead;
                lint.dead = false;
                let cv = self.k_expr(*cond, &mut lenv, lint);
                if cv != Some(KVal::Bool(false)) {
                    lint.dead = false;
                    lint.frames.push((label.map(|l| l.name), Vec::new()));
                    self.k_block(*body, &mut lenv, lint);
                    lint.frames.pop();
                }
                lint.dead = saved;
                for &r in &poison {
                    env[r as usize] = None;
                }
                None
            }
            Expr::Loop { label, body } => {
                let poison = self.k_assigned_in(&[p.ast.block(*body).span]);
                let mut lenv = env.clone();
                for &r in &poison {
                    lenv[r as usize] = None;
                }
                let saved = lint.dead;
                lint.dead = false;
                lint.frames.push((label.map(|l| l.name), Vec::new()));
                self.k_block(*body, &mut lenv, lint);
                let (_, breaks) = lint.frames.pop().unwrap();
                lint.dead = saved;
                for &r in &poison {
                    env[r as usize] = None;
                }
                if breaks.len() == 1 { breaks.into_iter().next().unwrap() } else { None }
            }
            Expr::For { label, pat, iter, body } => {
                self.k_expr(*iter, env, lint);
                let regions = [self.span(*iter), p.ast.block(*body).span];
                let poison = self.k_assigned_in(&regions);
                let mut lenv = env.clone();
                for &r in &poison {
                    lenv[r as usize] = None;
                }
                let saved = lint.dead;
                lint.dead = false;
                let none = None;
                self.k_bind_pat(*pat, &none, &mut lenv, lint);
                lint.frames.push((label.map(|l| l.name), Vec::new()));
                self.k_block(*body, &mut lenv, lint);
                lint.frames.pop();
                lint.dead = saved;
                for &r in &poison {
                    env[r as usize] = None;
                }
                None
            }
            Expr::Match { scrut, arms } => {
                let sv = self.k_expr(*scrut, env, lint);
                let sty = self.out.expr_ty[self.ei(*scrut)];
                let saved = lint.dead;
                if let Some(arm) = sv.as_ref().and_then(|v| self.k_select_arm(arms, v, sty)) {
                    // Only this arm runs. With several arms its assignments
                    // and its value are still lost at the join; a single
                    // arm is straight-line code.
                    lint.dead = false;
                    let pushed = self.k_allow_push(&arm.attrs.clone(), lint);
                    self.k_bind_pat(arm.pat, &sv, env, lint);
                    let v = self.k_expr(arm.body, env, lint);
                    self.k_allow_pop(pushed, lint);
                    let body_dead = lint.dead || self.tys.kind(self.out.expr_ty[self.ei(arm.body)]) == TyKind::Never;
                    lint.dead = saved || body_dead;
                    if arms.len() == 1 {
                        return v;
                    }
                    self.k_poison(env, &[self.span(arm.body)]);
                    return None;
                }
                let mut regions: Vec<Span> = Vec::new();
                let mut single = None;
                for arm in arms {
                    lint.dead = false;
                    let mut aenv = env.clone();
                    let pushed = self.k_allow_push(&arm.attrs.clone(), lint);
                    self.k_bind_pat(arm.pat, &sv, &mut aenv, lint);
                    if let Some(g) = arm.guard {
                        self.k_expr(g, &mut aenv, lint);
                    }
                    let v = self.k_expr(arm.body, &mut aenv, lint);
                    self.k_allow_pop(pushed, lint);
                    regions.push(self.span(arm.body));
                    single = Some((aenv, v));
                }
                lint.dead = saved;
                if arms.len() == 1
                    && let Some((aenv, v)) = single
                {
                    *env = aenv;
                    return v;
                }
                self.k_poison(env, &regions);
                None
            }
            Expr::Break { label, value } => {
                let v = value.map(|x| self.k_expr(x, env, lint)).unwrap_or(None);
                let want = label.map(|l| l.name);
                if let Some(frame) = lint.frames.iter_mut().rev().find(|(n, _)| want.is_none() || *n == want) {
                    frame.1.push(v);
                }
                None
            }
            Expr::Continue(_) => None,
            Expr::Return(v) => {
                if let Some(v) = v {
                    self.k_expr(*v, env, lint);
                }
                None
            }
            Expr::Let { pat, scrut } => {
                let v = self.k_expr(*scrut, env, lint);
                self.k_bind_pat(*pat, &v, env, lint);
                None
            }
            Expr::Call { callee, args } => {
                self.k_expr(*callee, env, lint);
                let mut vals = Vec::new();
                for &a in args {
                    vals.push(self.k_expr(a, env, lint));
                }
                match self.out.expr_res[self.ei(e)] {
                    Res::DefaultVal => match self.tys.kind(ety) {
                        TyKind::Int(_) | TyKind::Char => Some(KVal::Int(0)),
                        TyKind::Bool => Some(KVal::Bool(false)),
                        _ => None,
                    },
                    Res::FromCast => match vals.into_iter().next().flatten() {
                        Some(KVal::Int(v)) => self.k_wrap(v, ety).map(KVal::Int),
                        other => other,
                    },
                    _ => match self.out.expr_res[self.ei(*callee)] {
                        Res::ConstUsize(u) => Some(KVal::Int(u as i128)),
                        Res::Variant(a, v) if p.adt(a).is_enum => Some(KVal::Enum(a, v)),
                        Res::Variant(a, _) if !p.adt(a).is_enum => Some(KVal::Agg(vals)),
                        Res::OptSome => Some(KVal::Agg(vals)),
                        _ => None,
                    },
                }
            }
            Expr::MethodCall { recv, args, .. } => {
                self.k_expr(*recv, env, lint);
                for &a in args {
                    self.k_expr(a, env, lint);
                }
                None
            }
            Expr::Field { base, .. } | Expr::TupleField { base, .. } => {
                let bv = self.k_expr(*base, env, lint);
                match (bv, self.out.expr_res[self.ei(e)]) {
                    (Some(KVal::Agg(items)), Res::Field { derefs: 0, index }) => items.get(index as usize).cloned().unwrap_or(None),
                    _ => None,
                }
            }
            Expr::Index { base, index } => {
                let bv = self.k_expr(*base, env, lint);
                let iv = self.k_expr(*index, env, lint);
                self.k_check_index(*base, &iv, span, lint);
                match (bv, iv) {
                    (Some(KVal::Agg(items)), Some(KVal::Int(i))) if i >= 0 => items.get(i as usize).cloned().unwrap_or(None),
                    _ => None,
                }
            }
            Expr::StructLit { fields, update, .. } => {
                let base = update.and_then(|u| self.k_expr(u, env, lint));
                match self.out.expr_res[self.ei(e)] {
                    Res::Variant(a, v) if !p.adt(a).is_enum => {
                        let variant = &p.adt(a).variants[v as usize];
                        let mut items: Vec<Option<KVal>> = match base {
                            Some(KVal::Agg(items)) if items.len() == variant.fields.len() => items,
                            _ => vec![None; variant.fields.len()],
                        };
                        for &(fname, _, fe) in fields {
                            let fv = self.k_expr(fe, env, lint);
                            if let Some(i) = variant.fields.iter().position(|f| f.name == fname) {
                                items[i] = fv;
                            }
                        }
                        Some(KVal::Agg(items))
                    }
                    Res::Variant(a, v) if p.adt(a).is_enum => {
                        for &(_, _, fe) in fields {
                            self.k_expr(fe, env, lint);
                        }
                        Some(KVal::Enum(a, v))
                    }
                    _ => {
                        for &(_, _, fe) in fields {
                            self.k_expr(fe, env, lint);
                        }
                        None
                    }
                }
            }
            Expr::Tuple(elems) => {
                let items = elems.iter().map(|&el| self.k_expr(el, env, lint)).collect();
                Some(KVal::Agg(items))
            }
            Expr::Array(elems) => {
                let items = elems.iter().map(|&el| self.k_expr(el, env, lint)).collect();
                Some(KVal::Agg(items))
            }
            Expr::ArrayRepeat { value, len } => {
                self.k_expr(*value, env, lint);
                self.k_expr(*len, env, lint);
                None
            }
            Expr::Range { lo, hi, .. } => {
                for b in [lo, hi].into_iter().flatten() {
                    self.k_expr(*b, env, lint);
                }
                None
            }
            Expr::Ref { expr, .. } => {
                self.k_expr(*expr, env, lint);
                None
            }
            Expr::Deref(inner) => {
                self.k_expr(*inner, env, lint);
                None
            }
            Expr::Cast { expr, .. } => {
                let v = self.k_expr(*expr, env, lint);
                match (v, self.tys.kind(ety)) {
                    (Some(KVal::Int(x)), TyKind::Int(_) | TyKind::Char) => self.k_wrap(x, ety).map(KVal::Int),
                    (Some(KVal::Bool(b)), TyKind::Int(_)) => Some(KVal::Int(b as i128)),
                    (Some(KVal::Bool(b)), TyKind::Bool) => Some(KVal::Bool(b)),
                    _ => None,
                }
            }
            Expr::OffsetOf { .. } => match self.out.expr_res[self.ei(e)] {
                Res::ConstUsize(u) => Some(KVal::Int(u as i128)),
                _ => None,
            },
            Expr::Macro { args, .. } => {
                for &a in args {
                    self.k_expr(a, env, lint);
                }
                None
            }
            Expr::Binary { op, lhs, rhs } => self.k_binary(e, *op, *lhs, *rhs, span, env, lint),
            Expr::Unary { op, expr } => self.k_unary(e, *op, *expr, span, env, lint),
            Expr::Assign { lhs, rhs } => {
                self.k_place_parts(*lhs, env, lint);
                let whole = if matches!(p.ast.expr(*lhs), Expr::Path(_)) { self.k_place_root(*lhs) } else { None };
                if let Some(root) = whole
                    && matches!(p.ast.expr(*rhs), Expr::Binary { .. } | Expr::Unary { .. })
                {
                    lint.suppress = Some((*rhs, root));
                }
                let v = self.k_expr(*rhs, env, lint);
                lint.suppress = None;
                match whole {
                    Some(root) => Self::k_set(env, lint, root, v),
                    None => {
                        if let Some(root) = self.k_place_root(*lhs) {
                            env[root as usize] = None;
                        }
                    }
                }
                None
            }
            Expr::AssignOp { op, lhs, rhs } => {
                let root = self.k_place_root(*lhs);
                let old = if matches!(p.ast.expr(*lhs), Expr::Path(_)) {
                    root.and_then(|r| env.get(r as usize).cloned().unwrap_or(None))
                } else {
                    self.k_place_parts(*lhs, env, lint);
                    None
                };
                let rv = self.k_expr(*rhs, env, lint);
                // A compound assignment does not fire for its own overflow
                // (probed), but a bad shift amount still does, and a
                // division or remainder that always panics does too.
                if matches!(op, BinOp::Shl | BinOp::Shr)
                    && let Some(KVal::Int(s)) = rv
                {
                    let lt = self.out.expr_ty[self.ei(*lhs)];
                    if let Some(bits) = self.k_bits(lt) {
                        if s < 0 || s >= bits as i128 {
                            self.k_fire(span, lint);
                        }
                    }
                }
                if matches!(op, BinOp::Div | BinOp::Rem)
                    && let Some(KVal::Int(b)) = rv
                {
                    let lt = self.out.expr_ty[self.ei(*lhs)];
                    if let Some(b) = self.k_math(b, lt) {
                        if b == 0 {
                            self.k_fire_panic(span, lint, "attempt to divide by zero", "Change the divisor so it cannot be zero.");
                        } else if b == -1
                            && let Some((_, lo, _)) = self.k_range(lt)
                            && matches!(&old, Some(KVal::Int(a)) if self.k_math(*a, lt) == Some(lo))
                        {
                            self.k_fire_panic(span, lint, "attempt to divide with overflow", "Change the values or the type.");
                        }
                    }
                }
                match root {
                    Some(r) if matches!(p.ast.expr(*lhs), Expr::Path(_)) => {
                        let lt = self.out.expr_ty[self.ei(*lhs)];
                        let nv = match (old, rv) {
                            (Some(KVal::Int(a)), Some(KVal::Int(b))) => self.k_arith(*op, a, b, lt).map(KVal::Int),
                            _ => None,
                        };
                        Self::k_set(env, lint, r, nv);
                    }
                    Some(r) => env[r as usize] = None,
                    None => {}
                }
                None
            }
            Expr::Try(inner) | Expr::Await(inner) => self.k_expr(*inner, env, lint),
            Expr::Closure { params, body, .. } => {
                // A closure body is its own body for the lints: its
                // parameters are unknown, captures keep the knowledge
                // they have here, and nothing it assigns leaks out.
                let mut cenv = env.clone();
                let none = None;
                for param in params {
                    self.k_bind_pat(param.pat, &none, &mut cenv, lint);
                }
                let saved = lint.dead;
                lint.dead = false;
                self.k_expr(*body, &mut cenv, lint);
                lint.dead = saved;
                None
            }
            _ => None,
        }
    }

    /// Walks the sub-expressions of an assignment place (indexes and the
    /// like) so operations inside them are linted.
    fn k_place_parts(&mut self, e: ExprId, env: &mut KEnv, lint: &mut KLint) {
        match self.p.ast.expr(e) {
            Expr::Index { base, index } => {
                self.k_place_parts(*base, env, lint);
                let iv = self.k_expr(*index, env, lint);
                let span = self.span(e);
                self.k_check_index(*base, &iv, span, lint);
            }
            Expr::Field { base, .. } | Expr::TupleField { base, .. } => self.k_place_parts(*base, env, lint),
            Expr::Deref(inner) => {
                self.k_expr(*inner, env, lint);
            }
            // A destructuring target holds a place per element.
            Expr::Tuple(elems) | Expr::Array(elems) => {
                for &el in elems {
                    self.k_place_parts(el, env, lint);
                }
            }
            Expr::StructLit { fields, .. } => {
                for &(_, _, fe) in fields {
                    self.k_place_parts(fe, env, lint);
                }
            }
            Expr::Call { args, .. } => {
                for &arg in args {
                    self.k_place_parts(arg, env, lint);
                }
            }
            _ => {}
        }
    }

    /// The arm a known scrutinee value selects. Arms are read in
    /// order: an arm is selected only when its pattern certainly
    /// matches, it has no guard, and no earlier arm could have
    /// matched. A pattern this pass cannot decide (a guarded arm that
    /// covers, a payload subpattern, a const it cannot read) stops
    /// the selection, so the caller walks every arm instead.
    fn k_select_arm<'x>(&self, arms: &'x [ast::Arm], v: &KVal, sty: Ty) -> Option<&'x ast::Arm> {
        for arm in arms {
            match self.k_covers(arm.pat, v, sty) {
                KCov::Yes if arm.guard.is_none() => return Some(arm),
                KCov::Yes | KCov::Unknown => return None,
                KCov::No => {}
            }
        }
        None
    }

    /// Whether a pattern certainly matches, certainly misses, or may
    /// match the known scrutinee value.
    fn k_covers(&self, pat: PatId, v: &KVal, sty: Ty) -> KCov {
        match v {
            KVal::Int(i) => self.k_scalar_covers(pat, *i, sty),
            KVal::Bool(b) => self.k_scalar_covers(pat, *b as i128, sty),
            KVal::Enum(a, var) => self.k_enum_covers(pat, *a, *var),
            KVal::Agg(_) => KCov::Unknown,
        }
    }

    fn k_scalar_covers(&self, pat: PatId, val: i128, sty: Ty) -> KCov {
        let p = self.p;
        match p.ast.pat(pat) {
            Pat::Wild => KCov::Yes,
            Pat::Binding { .. } => match self.out.pat_res[(pat.0 - self.out.pat_base) as usize] {
                // A const item used as a pattern matches only its value.
                PatRes::ConstItem(_) => match self.pat_scalar(pat) {
                    Some(x) if self.k_cmp(val, x, sty) == std::cmp::Ordering::Equal => KCov::Yes,
                    Some(_) => KCov::No,
                    None => KCov::Unknown,
                },
                PatRes::Binding { .. } => KCov::Yes,
                _ => KCov::Unknown,
            },
            Pat::Path(_) => match self.pat_scalar(pat) {
                Some(x) if self.k_cmp(val, x, sty) == std::cmp::Ordering::Equal => KCov::Yes,
                Some(_) => KCov::No,
                None => KCov::Unknown,
            },
            Pat::Lit(l) => match p.ast.expr(*l) {
                Expr::Bool(b) => {
                    if val == *b as i128 {
                        KCov::Yes
                    } else {
                        KCov::No
                    }
                }
                _ => match self.const_scalar(*l) {
                    Some(x) if self.k_cmp(val, x, sty) == std::cmp::Ordering::Equal => KCov::Yes,
                    Some(_) => KCov::No,
                    None => KCov::Unknown,
                },
            },
            Pat::Range { lo, hi, inclusive } => {
                use std::cmp::Ordering::{Greater, Less};
                let lo_v = match lo {
                    Some(e) => match self.const_scalar(*e) {
                        Some(x) => Some(x),
                        None => return KCov::Unknown,
                    },
                    None => None,
                };
                let hi_v = match hi {
                    Some(e) => match self.const_scalar(*e) {
                        Some(x) => Some(x),
                        None => return KCov::Unknown,
                    },
                    None => None,
                };
                let lo_ok = lo_v.is_none_or(|x| self.k_cmp(val, x, sty) != Less);
                let hi_ok = hi_v.is_none_or(|x| {
                    let c = self.k_cmp(val, x, sty);
                    if *inclusive { c != Greater } else { c == Less }
                });
                if lo_ok && hi_ok { KCov::Yes } else { KCov::No }
            }
            Pat::Or(alts) => {
                let mut any_unknown = false;
                for &a in alts {
                    match self.k_scalar_covers(a, val, sty) {
                        KCov::Yes => return KCov::Yes,
                        KCov::Unknown => any_unknown = true,
                        KCov::No => {}
                    }
                }
                if any_unknown { KCov::Unknown } else { KCov::No }
            }
            Pat::At { inner, .. } | Pat::Paren(inner) => self.k_scalar_covers(*inner, val, sty),
            _ => KCov::Unknown,
        }
    }

    fn k_enum_covers(&self, pat: PatId, adt: AdtId, var: u32) -> KCov {
        let p = self.p;
        match self.out.pat_res[(pat.0 - self.out.pat_base) as usize] {
            PatRes::Variant(a, v) if a == adt => {
                if v != var {
                    return KCov::No;
                }
                // The variant matches; payload subpatterns that are
                // plain bindings cannot refuse it.
                let subs_catch = match p.ast.pat(pat) {
                    Pat::TupleStruct { elems, .. } => elems.iter().all(|&s| self.k_pat_catches(s)),
                    Pat::Struct { fields, .. } => fields.iter().all(|&(_, s)| self.k_pat_catches(s)),
                    _ => true,
                };
                if subs_catch { KCov::Yes } else { KCov::Unknown }
            }
            PatRes::Variant(..) => KCov::Unknown,
            _ => match p.ast.pat(pat) {
                Pat::Wild => KCov::Yes,
                Pat::Binding { .. } => match self.out.pat_res[(pat.0 - self.out.pat_base) as usize] {
                    PatRes::Binding { .. } => KCov::Yes,
                    _ => KCov::Unknown,
                },
                Pat::Or(alts) => {
                    let mut any_unknown = false;
                    for &a in alts {
                        match self.k_enum_covers(a, adt, var) {
                            KCov::Yes => return KCov::Yes,
                            KCov::Unknown => any_unknown = true,
                            KCov::No => {}
                        }
                    }
                    if any_unknown { KCov::Unknown } else { KCov::No }
                }
                Pat::At { inner, .. } | Pat::Paren(inner) => self.k_enum_covers(*inner, adt, var),
                _ => KCov::Unknown,
            },
        }
    }

    /// True when a subpattern accepts any payload (a binding, a
    /// wildcard, or the same nested under `@`, parens, or borrows).
    fn k_pat_catches(&self, pat: PatId) -> bool {
        match self.p.ast.pat(pat) {
            Pat::Wild | Pat::Rest => true,
            Pat::Binding { .. } => matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Binding { .. }),
            Pat::At { inner, .. } | Pat::Paren(inner) | Pat::Ref { inner, .. } => self.k_pat_catches(*inner),
            Pat::Or(alts) => alts.iter().any(|&a| self.k_pat_catches(a)),
            _ => false,
        }
    }

    /// Wrapped arithmetic for continuing a known value (no lint here).
    fn k_arith(&self, op: BinOp, a: i128, b: i128, t: Ty) -> Option<i128> {
        if self.k_is_u128(t) {
            // The stored values are u128 bit patterns; `b` of a shift is
            // the amount in its own type, already range-checked by the
            // caller, so a negative or huge amount just stops tracking.
            let (au, bu) = (a as u128, b as u128);
            let r = match op {
                BinOp::Add => au.wrapping_add(bu),
                BinOp::Sub => au.wrapping_sub(bu),
                BinOp::Mul => au.wrapping_mul(bu),
                BinOp::Div => {
                    if bu == 0 {
                        return None;
                    }
                    au / bu
                }
                BinOp::Rem => {
                    if bu == 0 {
                        return None;
                    }
                    au % bu
                }
                BinOp::BitAnd => au & bu,
                BinOp::BitOr => au | bu,
                BinOp::BitXor => au ^ bu,
                BinOp::Shl => au.checked_shl(u32::try_from(b).ok()?)?,
                BinOp::Shr => au.checked_shr(u32::try_from(b).ok()?)?,
                _ => return None,
            };
            return Some(r as i128);
        }
        let (a, b) = (self.k_math(a, t)?, self.k_math(b, t)?);
        let r = match op {
            BinOp::Add => a.checked_add(b)?,
            BinOp::Sub => a.checked_sub(b)?,
            BinOp::Mul => a.checked_mul(b)?,
            BinOp::Div => {
                if b == 0 {
                    return None;
                }
                a.checked_div(b)?
            }
            BinOp::Rem => {
                if b == 0 {
                    return None;
                }
                a.checked_rem(b)?
            }
            BinOp::BitAnd => a & b,
            BinOp::BitOr => a | b,
            BinOp::BitXor => a ^ b,
            BinOp::Shl => a.checked_shl(u32::try_from(b).ok()?)?,
            BinOp::Shr => a.checked_shr(u32::try_from(b).ok()?)?,
            _ => return None,
        };
        self.k_wrap(r, t)
    }

    fn k_binary(&mut self, e: ExprId, op: BinOp, lhs: ExprId, rhs: ExprId, span: Span, env: &mut KEnv, lint: &mut KLint) -> Option<KVal> {
        let lv = self.k_expr(lhs, env, lint);
        // A known short-circuit skips the right side entirely.
        match (op, &lv) {
            (BinOp::And, Some(KVal::Bool(false))) => return Some(KVal::Bool(false)),
            (BinOp::Or, Some(KVal::Bool(true))) => return Some(KVal::Bool(true)),
            _ => {}
        }
        let rv = self.k_expr(rhs, env, lint);
        if matches!(self.out.expr_res[self.ei(e)], Res::TraitBin { .. }) {
            return None;
        }
        match op {
            BinOp::And => match (lv, rv) {
                (Some(KVal::Bool(a)), Some(KVal::Bool(b))) => Some(KVal::Bool(a && b)),
                _ => None,
            },
            BinOp::Or => match (lv, rv) {
                (Some(KVal::Bool(a)), Some(KVal::Bool(b))) => Some(KVal::Bool(a || b)),
                _ => None,
            },
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let ord = match (&lv, &rv) {
                    (Some(KVal::Int(a)), Some(KVal::Int(b))) => {
                        let lt = self.out.expr_ty[self.ei(lhs)];
                        match (self.k_math(*a, lt), self.k_math(*b, lt)) {
                            (Some(a), Some(b)) => Some(self.k_cmp(a, b, lt)),
                            _ => None,
                        }
                    }
                    (Some(KVal::Bool(a)), Some(KVal::Bool(b))) => Some(a.cmp(b)),
                    _ => None,
                };
                ord.map(|o| {
                    KVal::Bool(match op {
                        BinOp::Eq => o == std::cmp::Ordering::Equal,
                        BinOp::Ne => o != std::cmp::Ordering::Equal,
                        BinOp::Lt => o == std::cmp::Ordering::Less,
                        BinOp::Le => o != std::cmp::Ordering::Greater,
                        BinOp::Gt => o == std::cmp::Ordering::Greater,
                        _ => o != std::cmp::Ordering::Less,
                    })
                })
            }
            BinOp::Shl | BinOp::Shr => {
                let lt = self.out.expr_ty[self.ei(lhs)];
                if let (Some(bits), Some(KVal::Int(s))) = (self.k_bits(lt), &rv)
                    && (*s < 0 || *s >= bits as i128)
                {
                    self.k_fire(span, lint);
                    return None;
                }
                match (lv, rv) {
                    (Some(KVal::Int(a)), Some(KVal::Int(b))) => self.k_arith(op, a, b, lt).map(KVal::Int),
                    _ => None,
                }
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                let lt = self.out.expr_ty[self.ei(lhs)];
                let (Some(KVal::Int(a)), Some(KVal::Int(b))) = (lv, rv) else { return None };
                if self.k_is_u128(lt) {
                    let (au, bu) = (a as u128, b as u128);
                    let r = match op {
                        BinOp::Add => au.checked_add(bu),
                        BinOp::Sub => au.checked_sub(bu),
                        _ => au.checked_mul(bu),
                    };
                    let suppressed = lint.suppress == Some((e, u32::MAX))
                        || matches!(lint.suppress, Some((se, root)) if se == e && (self.k_place_root(lhs) == Some(root) || self.k_place_root(rhs) == Some(root)));
                    return match r {
                        Some(r) => Some(KVal::Int(r as i128)),
                        None => {
                            if !suppressed {
                                self.k_fire(span, lint);
                            }
                            None
                        }
                    };
                }
                let Some((_, lo, hi)) = self.k_range(lt) else { return None };
                let (Some(a), Some(b)) = (self.k_math(a, lt), self.k_math(b, lt)) else { return None };
                let r = match op {
                    BinOp::Add => a.checked_add(b),
                    BinOp::Sub => a.checked_sub(b),
                    _ => a.checked_mul(b),
                };
                let suppressed = lint.suppress == Some((e, u32::MAX))
                    || matches!(lint.suppress, Some((se, root)) if se == e && (self.k_place_root(lhs) == Some(root) || self.k_place_root(rhs) == Some(root)));
                match r {
                    Some(r) if (lo..=hi).contains(&r) => Some(KVal::Int(r)),
                    _ => {
                        if !suppressed {
                            self.k_fire(span, lint);
                        }
                        None
                    }
                }
            }
            BinOp::Div | BinOp::Rem => {
                let lt = self.out.expr_ty[self.ei(lhs)];
                // A known zero divisor panics whatever the dividend is;
                // `MIN / -1` needs both sides known.
                if let Some(KVal::Int(b)) = &rv
                    && self.k_bits(lt).is_some()
                    && let Some(b) = self.k_math(*b, lt)
                {
                    if b == 0 {
                        self.k_fire_panic(span, lint, "attempt to divide by zero", "Change the divisor so it cannot be zero.");
                        return None;
                    }
                    if b == -1
                        && let Some(KVal::Int(a)) = &lv
                        && let Some((_, lo, _)) = self.k_range(lt)
                        && self.k_math(*a, lt) == Some(lo)
                    {
                        self.k_fire_panic(span, lint, "attempt to divide with overflow", "Change the values or the type.");
                        return None;
                    }
                }
                match (lv, rv) {
                    (Some(KVal::Int(a)), Some(KVal::Int(b))) => self.k_arith(op, a, b, lt).map(KVal::Int),
                    _ => None,
                }
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
                let lt = self.out.expr_ty[self.ei(lhs)];
                match (lv, rv) {
                    (Some(KVal::Int(a)), Some(KVal::Int(b))) => self.k_arith(op, a, b, lt).map(KVal::Int),
                    _ => None,
                }
            }
        }
    }

    fn k_unary(&mut self, e: ExprId, op: UnOp, inner: ExprId, span: Span, env: &mut KEnv, lint: &mut KLint) -> Option<KVal> {
        let v = self.k_expr(inner, env, lint);
        match op {
            UnOp::Neg => {
                let Some(KVal::Int(x)) = v else { return None };
                let t = self.out.expr_ty[self.ei(e)];
                // A literal under the minus is a magnitude, not a
                // negation of a value: `-128i8` and the `i128::MIN`
                // literal (magnitude 2^127, stored as the MIN bit
                // pattern) wrap to their own value and never fire.
                if matches!(self.p.ast.expr(inner), Expr::Int(..)) {
                    return self.k_wrap(x.wrapping_neg(), t).map(KVal::Int);
                }
                let Some((_, lo, hi)) = self.k_range(t) else { return None };
                let r = x.checked_neg();
                match r {
                    Some(r) if (lo..=hi).contains(&r) => Some(KVal::Int(r)),
                    _ => {
                        let suppressed = matches!(lint.suppress, Some((se, root)) if se == e && self.k_place_root(inner) == Some(root));
                        if !suppressed {
                            self.k_fire(span, lint);
                        }
                        None
                    }
                }
            }
            UnOp::Not => match v {
                Some(KVal::Int(x)) => {
                    let t = self.out.expr_ty[self.ei(e)];
                    let x = self.k_math(x, t)?;
                    self.k_wrap(!x, t).map(KVal::Int)
                }
                Some(KVal::Bool(b)) => Some(KVal::Bool(!b)),
                _ => None,
            },
        }
    }

    // ---------- Finish ----------

    /// True when the type still holds an unbound non-integer inference
    /// variable (an integer variable defaults to i32, as in rustc; any other
    /// one is the E0282 "type annotations needed" case).
    /// True for a type variable that is not an integer or float literal variable.
    fn unbound_general(&self, t: Ty) -> bool {
        matches!(self.kind(t), TyKind::Infer(v) if !v.is_int() && !v.is_float())
    }

    /// Also true for a const argument nothing fixed (`S<?N>` from a
    /// unit struct value, rustc E0284).
    fn has_unbound_var(&self, t: Ty) -> bool {
        if !self.tys.flags(t).contains_infer() {
            return false;
        }
        match self.tys.kind(self.resolve(t)) {
            TyKind::Infer(v) => !v.is_int() && !v.is_float(),
            TyKind::Ref(_, _, e) | TyKind::Slice(e) => self.has_unbound_var(e),
            TyKind::Array(e, n) => self.has_unbound_var(e) || self.unbound_const(n),
            TyKind::Tuple(ts) => self.tys.tys_of(ts).iter().any(|&e| self.has_unbound_var(e)),
            TyKind::Adt(_, a) => self.tys.args(a).iter().any(|g| match *g {
                GenericArg::Ty(e) => self.has_unbound_var(e),
                GenericArg::Const(c) => self.unbound_const(c),
                GenericArg::Lifetime(_) => false,
            }),
            _ => false,
        }
    }

    fn unbound_const(&self, c: ConstId) -> bool {
        matches!(self.tys.const_kind(self.resolve_const(c)), ConstKind::Infer(_))
    }

    /// True when the type holds a const variable nothing fixed.
    fn has_unbound_const(&self, t: Ty) -> bool {
        if !self.tys.flags(t).contains_infer() {
            return false;
        }
        match self.tys.kind(self.resolve(t)) {
            TyKind::Ref(_, _, e) | TyKind::Slice(e) => self.has_unbound_const(e),
            TyKind::Array(e, n) => self.unbound_const(n) || self.has_unbound_const(e),
            TyKind::Tuple(ts) => self.tys.tys_of(ts).iter().any(|&e| self.has_unbound_const(e)),
            TyKind::Adt(_, a) | TyKind::FnDef(_, a) => self.tys.args(a).iter().any(|g| match *g {
                GenericArg::Ty(e) => self.has_unbound_const(e),
                GenericArg::Const(c) => self.unbound_const(c),
                GenericArg::Lifetime(_) => false,
            }),
            _ => false,
        }
    }

    /// A generic call whose type argument nothing fixed is an
    /// annotation error (rustc E0282 and E0283), never a dropped
    /// instance request. Runs after inference, before the hard
    /// obligation run, which then skips the obligations on the
    /// reported variables (one error per root). Closure sites
    /// have their own check below; a body with an error already
    /// reports nothing here, since its variables may be unbound
    /// only because of that error.
    fn uninferred_site_args(&mut self) {
        self.run_obligations(false);
        if !self.errs.is_empty() {
            return;
        }
        let p = self.p;
        let mut reported: Vec<u32> = Vec::new();
        for i in 0..self.generic_sites.len() {
            let (ei, template, args) = self.generic_sites[i].clone();
            let Some(gi) = args.iter().position(|g| g.as_ty().is_some_and(|t| self.has_unbound_var(t) && !self.has_error_kind(t))) else {
                // A const argument nothing fixed (rustc E0282).
                if let Some(ci) = args.iter().position(|g| match *g {
                    GenericArg::Const(c) => matches!(self.tys.const_kind(self.resolve_const(c)), ConstKind::Infer(_)),
                    _ => false,
                }) {
                    let param = p.gx.fn_templates.get(template.0 as usize).and_then(|t| t.as_ref()).and_then(|t| t.generics.params.get(ci));
                    let pname = param.map_or("_".to_string(), |d| self.name(d.name).to_string());
                    let fname = p.display_path(p.fn_info(template).name);
                    let span = self.span(ExprId(self.out.expr_base + ei as u32));
                    self.err(
                        "L0610",
                        span,
                        format!("type annotations needed: cannot infer the value of the const parameter `{pname}` of `{fname}`"),
                        "Name the value with a turbofish such as `::<3>`, or annotate the value the call returns.",
                    );
                }
                continue;
            };
            let t = args[gi].as_ty().unwrap_or(ERROR);
            let t = self.deep(t);
            self.unbound_vars(t, &mut reported);
            let param = p.gx.fn_templates.get(template.0 as usize).and_then(|t| t.as_ref()).and_then(|t| t.generics.params.get(gi));
            let pname = param.map_or("_".to_string(), |d| self.name(d.name).to_string());
            let fname = p.display_path(p.fn_info(template).name);
            let span = self.span(ExprId(self.out.expr_base + ei as u32));
            self.err(
                "L0610",
                span,
                format!("type annotations needed: cannot infer the type of the generic parameter `{pname}` of `{fname}`"),
                "Name the type with a turbofish such as `::<i32>`, or annotate the value the call returns.",
            );
        }
        if reported.is_empty() {
            return;
        }
        let pending = self.obl.take();
        for ob in pending {
            let mentions = match ob {
                obligations::Obligation::Trait { trait_ref, .. } => self.args_mention(trait_ref.args, &reported),
                obligations::Obligation::AssocEq { eq, .. } => {
                    self.args_mention(eq.trait_args, &reported) || reported.iter().any(|&v| self.occurs(v, eq.ty))
                }
                obligations::Obligation::DynStatic { .. } => false,
                obligations::Obligation::TypeStatic { ty, .. } => reported.iter().any(|&v| self.occurs(v, ty)),
            };
            if !mentions {
                self.obl.push(ob);
            }
        }
    }

    /// The unbound general variables in one deep-resolved type.
    fn unbound_vars(&self, t: Ty, out: &mut Vec<u32>) {
        if !self.tys.flags(t).contains_infer() {
            return;
        }
        match self.tys.kind(self.resolve(t)) {
            TyKind::Infer(v) if !v.is_int() && !v.is_float() => out.push(v.index()),
            TyKind::Ref(_, _, e) | TyKind::Slice(e) | TyKind::Array(e, _) | TyKind::RawPtr(_, e) => self.unbound_vars(e, out),
            TyKind::Tuple(ts) => {
                for &e in self.tys.tys_of(ts) {
                    self.unbound_vars(e, out);
                }
            }
            TyKind::Adt(_, a) | TyKind::Projection(_, a) | TyKind::Closure(_, a) | TyKind::FnDef(_, a) => {
                for g in self.tys.args(a) {
                    if let Some(e) = g.as_ty() {
                        self.unbound_vars(e, out);
                    }
                }
            }
            _ => {}
        }
    }

    /// True when a type argument list mentions one of `vars`.
    fn args_mention(&self, a: ArgsId, vars: &[u32]) -> bool {
        self.tys.args(a).iter().any(|g| g.as_ty().is_some_and(|t| vars.iter().any(|&v| self.occurs(v, t))))
    }

    /// Resolves every recorded type, defaults integer variables, and checks literal ranges.
    fn finish(&mut self) {
        // rustc's literal fallback runs between the last soft run and
        // the hard one: an obligation that is only ambiguous over a
        // literal's type (`{float}: Tr` with impls for f32 and f64)
        // selects with i32 or f64, the types body end defaults to.
        self.run_obligations(false);
        self.literal_fallback_in_obligations();
        self.uninferred_site_args();
        // ARCH 2.4 run point: the obligation queue runs at body end to a fixpoint.
        // Anything left there is an annotation error, never a silent default.
        self.run_obligations(true);
        method::finish_deferred_methods(self);
        for (e, op, t) in std::mem::take(&mut self.open_binops) {
            use BinOp::*;
            let t = self.deep(t);
            let k = self.kind(t);
            let int = matches!(k, TyKind::Int(_)) || k.is_int_infer();
            let float = matches!(k, TyKind::Float(_)) || k.is_float_infer();
            let ok = match op {
                Add | Sub | Mul | Div | Rem => int || float,
                BitAnd | BitOr | BitXor => int || k == TyKind::Bool,
                Shl | Shr => int,
                Eq | Ne | Lt | Le | Gt | Ge => int || float || matches!(k, TyKind::Bool | TyKind::Char),
                And | Or => true,
            };
            if !ok && k != TyKind::Error {
                let span = self.span(e);
                self.err(
                    "L0610",
                    span,
                    "type annotations needed: the operand types of this operator must be known here",
                    "Annotate the closure parameters.",
                );
            }
        }
        // A local whose element or item type was never decided (`let a = [];`,
        // `let v = Vec::new();`) is an annotation error (rustc E0282). This
        // scan runs before the zonk below defaults those variables away.
        for i in 0..self.out.locals.len() {
            let t = self.out.locals[i].ty;
            if self.has_unbound_var(t) && !self.has_error_kind(t) {
                let span = self.out.locals[i].span;
                let name = self.name(self.out.locals[i].name).to_string();
                self.err(
                    "L0111",
                    span,
                    format!("cannot infer the type of `{name}`"),
                    "Add a type annotation, such as `let v: Vec<i64> = Vec::new();`.",
                );
            }
        }
        // The same for a const argument in an expression that is no
        // local (`S;` for a unit struct with a const param, rustc E0284):
        // codegen has no value for it.
        // Only a body that made a const variable can keep one.
        if self.errs.is_empty()
            && self.next_const_id > generics::INFER_MARKER_BASE
            && let Some(i) = (0..self.out.expr_ty.len()).find(|&i| self.has_unbound_const(self.out.expr_ty[i]))
        {
            let span = self.span(ExprId(self.out.expr_base + i as u32));
            self.err(
                "L0610",
                span,
                "type annotations needed: cannot infer the value of a const parameter here",
                "Name the value with a turbofish such as `S::<3>`, or annotate the type.",
            );
        }
        // Deferred format tests, with types as bound by now.
        for (t, spec, span) in std::mem::take(&mut self.deferred_fmt) {
            let t = self.deep(t);
            self.check_fmt_arg(t, spec, span);
        }
        // Deferred Clone and PartialEq needs of builtin Vec and
        // slice methods, with types as bound by now.
        for (t, span) in std::mem::take(&mut self.deferred_clone) {
            let t = self.deep(t);
            let t = self.normalize_here(t);
            if !has_clone(self.p, &self.tys, t) && !matches!(self.kind(t), TyKind::Error | TyKind::Infer(_)) {
                let tn = self.tn(t);
                self.err("L0112", span, format!("`{tn}` does not implement Clone"), "Add #[derive(Clone)] to the type.");
            }
        }
        for (t, span) in std::mem::take(&mut self.deferred_item_args) {
            let t = self.deep(t);
            let TyKind::FnDef(_, args) = self.kind(t) else { continue };
            if self.tys.args(args).iter().any(|g| g.as_ty().is_some_and(|e| object::may_borrow(self.p, &self.tys, e))) {
                self.errs.push(not_yet(
                    "L0702",
                    span,
                    "a builtin constructor or `Box::new`/`Rc::new` with a borrowing input as a call argument",
                ));
            }
        }
        for (t, span) in std::mem::take(&mut self.deferred_string_from) {
            let t = self.deep(t);
            let tn = self.tn(t);
            match self.kind(t) {
                TyKind::Error => {}
                _ if t == CHAR || t == STRING => {}
                TyKind::Ref(_, Mut::Shared, s) if self.kind(s) == TyKind::Str => {}
                TyKind::Infer(_) => self.err("L0610", span, "type annotations needed: the input of `String::from` is not known", "Annotate the input's type."),
                // No std impl, and no user one can exist (orphan rules).
                TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Unit => self.err(
                    "L0612",
                    span,
                    format!("the trait bound `String: From<{tn}>` is not satisfied"),
                    "Convert with `to_string()` or `format!`.",
                ),
                // std's `&mut str`, `&String`, and `Box<str>` impls, a
                // user impl, or a param's bound.
                _ => {
                    let what = format!("`String::from` as a value with input `{tn}` (lust takes `&str`, `char`, or `String` there)");
                    self.errs.push(unsupported(span, &what));
                }
            }
        }
        for (t, span) in std::mem::take(&mut self.deferred_eq) {
            let t = self.deep(t);
            let t = self.normalize_here(t);
            if !has_eq(self.p, &self.tys, t) && !matches!(self.kind(t), TyKind::Error | TyKind::Infer(_)) {
                let tn = self.tn(t);
                self.err("L0112", span, format!("type `{tn}` cannot be compared with `==`"), "Add #[derive(PartialEq)] to the type.");
            }
        }
        for (t, span) in std::mem::take(&mut self.deferred_copy) {
            let t = self.deep(t);
            if !is_copy(self.p, &self.tys, t) && !matches!(self.kind(t), TyKind::Error | TyKind::Infer(_)) {
                let tn = self.tn(t);
                self.err("L0612", span, format!("`{tn}` is not Copy"), "Use `.cloned()` instead of `.copied()`.");
            }
        }
        for (t, span) in std::mem::take(&mut self.deferred_default) {
            let t = self.deep(t);
            if !has_default(self.p, &self.tys, t) && !matches!(self.kind(t), TyKind::Error) {
                let tn = self.tn(t);
                self.err("L0612", span, format!("`{tn}` does not implement Default, or lust cannot build its default yet"), "Use `replace` with a value.");
            }
        }
        for (t, span) in std::mem::take(&mut self.deferred_sized) {
            let t = self.deep(t);
            if matches!(self.kind(t), TyKind::Dyn(..) | TyKind::Slice(_) | TyKind::Str) {
                self.errs.push(not_yet("L0641", span, "this `Rc` function on an unsized type"));
            }
        }
        for (t, span) in std::mem::take(&mut self.deferred_debug) {
            let t = self.deep(t);
            if !has_debug(self.p, &self.tys, t) && !matches!(self.kind(t), TyKind::Error) {
                let tn = self.tn(t);
                self.err("L0612", span, format!("`{tn}` does not implement Debug"), "Add #[derive(Debug)] to the type.");
            }
        }
        for (t, span) in std::mem::take(&mut self.deferred_ord) {
            let t = self.deep(t);
            if !has_total_ord(self.p, &self.tys, t) && !matches!(self.kind(t), TyKind::Error) {
                let tn = self.tn(t);
                self.err("L0612", span, format!("`{tn}` does not implement Ord, or lust cannot compare it yet"), "Derive Ord on the type, or compare integers, chars, strings, or tuples of them.");
            }
        }
        for i in 0..self.out.expr_ty.len() {
            let t = self.out.expr_ty[i];
            self.out.expr_ty[i] = self.zonk(t);
        }
        self.settle_projections();
        for i in 0..self.out.pat_ty.len() {
            let t = self.out.pat_ty[i];
            self.out.pat_ty[i] = self.zonk(t);
        }
        self.finish_closures();
        for i in 0..self.out.locals.len() {
            let t = self.out.locals[i].ty;
            let z = self.zonk(t);
            if z == ERROR && !self.has_error_kind(t) {
                let span = self.out.locals[i].span;
                let name = self.name(self.out.locals[i].name).to_string();
                self.err(
                    "L0111",
                    span,
                    format!("cannot infer the type of `{name}`"),
                    "Add a type annotation, such as `let v: Vec<i64> = Vec::new();`.",
                );
            }
            self.out.locals[i].ty = z;
        }
        for i in 0..self.out.coerce.len() {
            if let Coerce::Unsize(t) = self.out.coerce[i] {
                let z = self.zonk(t);
                self.out.coerce[i] = Coerce::Unsize(z);
            }
        }
        for (x, y, span) in std::mem::take(&mut self.vtable_sites) {
            let (x, y) = (self.zonk(x), self.zonk(y));
            // After mono, a concrete body's every coercion has its
            // vtable; a miss is a compiler gap, reported, never emitted.
            if self.p.gx.mono_done && generics::vtable_for(self.p, &self.tys, x, y).is_none() {
                let tn = self.tn(x);
                self.err(
                    "L0702",
                    span,
                    format!("internal: no vtable was built for `{tn}` here, so this `dyn` coercion is not supported yet"),
                    "Report this; meanwhile, use generics instead of `dyn` here.",
                );
            }
            self.out.vtable_requests.push((x, y));
        }
        // Every local has a statically known size (rustc E0277): `let x
        // = *b;` for `b: Box<dyn Tr>` is a move out of the box that the
        // borrow checker allows for a sized pointee.
        for i in 0..self.out.locals.len() {
            let t = self.deep(self.out.locals[i].ty);
            if matches!(self.kind(t), TyKind::Dyn(..) | TyKind::Str | TyKind::Slice(_)) {
                let (tn, span) = (self.tn(t), self.out.locals[i].span);
                self.err(
                    "L0110",
                    span,
                    format!("the size for values of type `{tn}` cannot be known, so it cannot be a local variable"),
                    "Bind a reference instead: `let x = &*b;`.",
                );
            }
        }
        self.overflow_lint();
        // Abstract associated const reads (see `abstract_consts`)
        // get their zero placeholder now: every value-reading
        // analysis above has run, only lowering is left.
        for e in std::mem::take(&mut self.abstract_consts) {
            let i = self.ei(e);
            if self.out.const_exprs[i].is_none()
                && let Some(v) = self.zero_const(self.out.expr_ty[i])
            {
                self.out.const_exprs[i] = Some(v);
            }
        }
        // Generic user `deref` fns of method receivers, as call sites.
        for (table, idx, is_mut, template, args) in std::mem::take(&mut self.deref_sites) {
            let zargs: Vec<GenericArg> = args
                .iter()
                .map(|&g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(self.zonk(t)),
                    GenericArg::Const(c) => GenericArg::Const(self.resolve_const(c)),
                    other => other,
                })
                .collect();
            let entries = match table {
                DerefTable::Recv => &mut self.out.deref_recv,
                DerefTable::Coerce => &mut self.out.deref_coerce,
            };
            if let Some(entry) = entries.get_mut(idx) {
                if is_mut {
                    entry.1.args_mut = zargs.clone();
                } else {
                    entry.1.args = zargs.clone();
                }
            }
            self.out.inst_requests.push((template, zargs));
        }
        // Generic call sites become instance requests for mono,
        // with their args zonked into place for lowering.
        for (ei, template, args) in std::mem::take(&mut self.generic_sites) {
            let zargs: Vec<GenericArg> = args
                .iter()
                .map(|&g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(self.zonk(t)),
                    GenericArg::Const(c) => GenericArg::Const(self.resolve_const(c)),
                    other => other,
                })
                .collect();
            if ei < self.out.generic_args.len() {
                self.out.generic_args[ei] = zargs.clone();
            }
            self.out.inst_requests.push((template, zargs));
        }
        // A generic Adt constructor names the template Adt; the
        // value's type names the instance mono made. Point the
        // resolution at the instance so lowering lays it out.
        for i in 0..self.out.expr_res.len() {
            if let Res::Variant(a, v) = self.out.expr_res[i]
                && let Some(inst) = self.tys.local_adt(self.out.expr_ty[i])
                && inst != a
            {
                self.out.expr_res[i] = Res::Variant(inst, v);
            }
        }
        for i in 0..self.out.pat_res.len() {
            if let PatRes::Variant(a, v) = self.out.pat_res[i]
                && let Some(inst) = self.tys.local_adt(self.out.pat_ty[i])
                && inst != a
            {
                self.out.pat_res[i] = PatRes::Variant(inst, v);
            }
        }
        // Literal range checks (the deny-level overflowing_literals
        // lint, for ints and floats alike).
        let base = self.out.expr_base;
        for i in 0..self.out.expr_ty.len() {
            let e = ExprId(base + i as u32);
            if let Expr::Float(s) = self.p.ast.expr(e)
                && let TyKind::Float(f) = self.tys.kind(self.out.expr_ty[i])
            {
                let text = self.p.ast.strings[*s as usize].as_str();
                if crate::check::collect::float_literal_overflows(text, f) {
                    let sp = self.span(e);
                    self.err(
                        "L0118",
                        sp,
                        format!("literal out of range for `{}`", f.name()),
                        format!("Use a value that fits in `{}`, or a wider type.", f.name()),
                    );
                }
            }
            if let Expr::Int(v, _) = self.p.ast.expr(e)
                && let TyKind::Int(it) = self.tys.kind(self.out.expr_ty[i])
            {
                let neg = self.negated_lits.contains(&e);
                let max = if neg && it.signed() { it.max128() + 1 } else { it.max128() };
                if *v > max {
                    let s = self.span(e);
                    self.err(
                        "L0118",
                        s,
                        format!("literal out of range for `{}`", it.name()),
                        format!("Use a value that fits in `{}`, or a wider type.", it.name()),
                    );
                }
            }
        }
    }

    fn has_error_kind(&self, t: Ty) -> bool {
        match self.kind(t) {
            TyKind::Error => true,
            TyKind::Ref(_, _, e) | TyKind::Slice(e) | TyKind::Array(e, _) => self.has_error_kind(e),
            TyKind::Adt(_, a) => (0..self.tys.args(a).len()).any(|i| match self.tys.args(a)[i].as_ty() {
                Some(e) => self.has_error_kind(e),
                None => false,
            }),
            TyKind::Tuple(ts) => {
                let n = self.tys.tys_of(ts).len();
                (0..n).any(|i| {
                    let e = self.tys.tys_of(ts)[i];
                    self.has_error_kind(e)
                })
            }
            _ => false,
        }
    }
}

/// The const evaluator's context over a body being checked: names resolve
/// through the program tables and the Binding query, as in body checking.
struct CheckCx<'x, 'p, 'a> {
    cx: &'x mut Ctx<'p, 'a>,
}

impl<'a, 'p> crate::ty::consteval::ConstCx<'a> for CheckCx<'_, 'p, 'a> {
    type Tys = Tys<'p>;

    fn enter_const_fn(&mut self, owner: Option<Sym>) {
        let cx = &mut *self.cx;
        let a = owner.and_then(|n| cx.p.type_names.get(&n).copied());
        cx.const_fn_saved.push((cx.const_fn_self, cx.body_scope.self_ty));
        cx.const_fn_self = Some(a);
        cx.body_scope.self_ty = a.map(|a| cx.tys.adt_ty(a));
    }
    fn exit_const_fn(&mut self) {
        if let Some((o, t)) = self.cx.const_fn_saved.pop() {
            self.cx.const_fn_self = o;
            self.cx.body_scope.self_ty = t;
        }
    }

    fn tys(&mut self) -> &mut Tys<'p> {
        &mut self.cx.tys
    }
    fn tys_ref(&self) -> &Tys<'p> {
        &self.cx.tys
    }
    fn ast(&self) -> &'a ast::Ast {
        self.cx.p.ast
    }
    fn sym_text(&self, s: Sym) -> &str {
        self.cx.name(s)
    }
    fn const_item(&mut self, name: Sym) -> Option<crate::ty::consteval::TypedValue> {
        // A const read inside body const evaluation consumes the value:
        // record the const's `Sig` read (its fingerprint folds the
        // value), as `path_expr` does for a plain expression use.
        let p = self.cx.p;
        let &i = p.const_names.get(&name)?;
        let out = {
            let c = &p.consts[i as usize];
            (c.value.clone(), c.ty)
        };
        if let Some(&def) = p.const_defs.get(i as usize) {
            let _ = p.sig_of(&mut self.cx.out.reads, def);
        }
        Some(out)
    }
    fn assoc_const_item(&mut self, segs: &[ast::PathSeg]) -> Option<crate::ty::consteval::TypedValue> {
        // An inherent associated const read inside body const
        // evaluation, through the same pick as `path_expr`.
        let p = self.cx.p;
        let (adt, item) = self.cx.assoc_const_key(segs)?;
        let idx = self.cx.assoc_const_base(segs, None).and_then(|base| self.cx.inherent_assoc_pick(adt, item, base, None))??;
        let out = {
            let c = &p.consts[idx as usize];
            (c.value.clone(), c.ty)
        };
        if let Some(&def) = p.const_defs.get(idx as usize) {
            let _ = p.sig_of(&mut self.cx.out.reads, def);
        }
        Some(out)
    }
    fn static_item(&mut self, name: Sym) -> Option<(u32, Ty)> {
        let p = self.cx.p;
        let &i = p.static_names.get(&name)?;
        let ty = p.statics[i as usize].ty;
        if let Some(&def) = p.static_defs.get(i as usize) {
            let _ = p.sig_of(&mut self.cx.out.reads, def);
        }
        Some((i, ty))
    }
    fn call_target(&mut self, callee: ExprId) -> crate::ty::consteval::CallTarget {
        use crate::ty::consteval::{CallTarget, ConstFnBody};
        let p = self.cx.p;
        let ast::Expr::Path(segs) = p.ast.expr(callee) else { return CallTarget::Unknown };
        let last = segs[segs.len() - 1].name;
        let ltext = self.cx.name(last).to_string();
        if matches!(ltext.as_str(), "size_of" | "align_of") {
            let args = segs[segs.len() - 1].type_args();
            if args.len() == 1 {
                let t = self.cx.resolve_written(args[0]);
                return if ltext == "size_of" { CallTarget::SizeOf(t) } else { CallTarget::AlignOf(t) };
            }
            return CallTarget::Unknown;
        }
        if segs.len() == 1 && last == p.known.Some {
            return CallTarget::VariantCtor { adt: AdtId(u32::MAX), variant: 1, ty: ERROR };
        }
        // The Result shim sits one below the Option shim (u32::MAX):
        // Ok is variant 0, Err is variant 1.
        if segs.len() == 1 && last == p.known.Ok {
            return CallTarget::VariantCtor { adt: AdtId(u32::MAX - 1), variant: 0, ty: ERROR };
        }
        if segs.len() == 1 && last == p.known.Err {
            return CallTarget::VariantCtor { adt: AdtId(u32::MAX - 1), variant: 1, ty: ERROR };
        }
        let span = self.cx.span(callee);
        let fid = if segs.len() == 1 {
            if self.cx.lookup(last, span.ctxt).is_some() {
                return CallTarget::Unknown;
            }
            self.cx.binding_fn(last)
        } else {
            match self.cx.resolve_assoc(segs, span) {
                Some(Res::Fn(f)) => Some(f),
                Some(Res::Variant(a, v)) => {
                    return CallTarget::VariantCtor { adt: a, variant: v, ty: self.cx.tys.adt_ty(a) };
                }
                Some(Res::Builtin(_)) => return CallTarget::NonConst,
                _ => None,
            }
        };
        if let Some(f) = fid {
            let info = p.fn_info(f);
            if !info.is_const {
                return CallTarget::NonConst;
            }
            let Some(body) = info.def.body else { return CallTarget::NonConst };
            // The evaluator is about to run this const fn's body and bake
            // the result into the body being checked: that body depends
            // on the const fn's body, not only its signature. A `Checked`
            // read records the edge; its replay never matches, so the
            // reader rechecks whenever it is a walk candidate. Nested
            // const calls inside the evaluated body come back here and
            // record their own edges, so the dependency is transitive.
            self.cx.out.reads.record_checked(p.def_id(f), Fingerprint(0));
            if info.self_kind.is_some() {
                return CallTarget::Unknown;
            }
            let params: Vec<(Sym, bool, Option<ast::PatId>)> = info.def.params.iter().map(|pp| (pp.name, pp.mutable, pp.pat)).collect();
            let owner = info.owner.map(|a| p.adt(a).name);
            return CallTarget::ConstFn(ConstFnBody { params, param_tys: info.params.clone(), ret: info.ret, body, owner });
        }
        if let Some(a) = self.cx.tuple_struct_ctor(last)
            && segs.len() == 1
        {
            return CallTarget::VariantCtor { adt: a, variant: 0, ty: self.cx.tys.adt_ty(a) };
        }
        if segs.len() == 2 && matches!(self.cx.name(segs[0].name), "String" | "Vec") {
            return CallTarget::NonConst;
        }
        CallTarget::Unknown
    }
    fn unit_variant(&mut self, segs: &[ast::PathSeg], expected: Option<Ty>) -> Option<(AdtId, u32, Ty)> {
        let p = self.cx.p;
        if segs.len() == 1 && segs[0].name == p.known.None {
            let elem = expected.and_then(|t| self.cx.tys.option_elem(t)).unwrap_or(ERROR);
            let ty = self.cx.tys.mk_option(elem);
            return Some((AdtId(u32::MAX), 0, ty));
        }
        let (adt, variant) = variant_of(p, segs)?;
        if p.adt(adt).variants[variant as usize].shape != VariantShape::Unit {
            return None;
        }
        Some((adt, variant, self.cx.tys.adt_ty(adt)))
    }
    fn struct_target(&mut self, path: &[ast::PathSeg]) -> Option<(AdtId, u32, Ty)> {
        let (adt, variant) = variant_of(self.cx.p, path)?;
        Some((adt, variant, self.cx.tys.adt_ty(adt)))
    }
    fn pattern_variant(&mut self, segs: &[ast::PathSeg]) -> Option<(AdtId, u32)> {
        variant_of(self.cx.p, segs)
    }
    fn variant_fields(&self, adt: AdtId, variant: u32) -> Vec<(Sym, Ty)> {
        if adt.0 >= u32::MAX - 1 {
            return Vec::new();
        }
        self.cx.p.adt(adt).variants[variant as usize].fields.iter().map(|f| (f.name, f.ty)).collect()
    }
    fn resolve_ty(&mut self, t: ast::TyId) -> Ty {
        self.cx.resolve_written(t)
    }
    fn layout(&mut self, t: Ty) -> Option<crate::ty::layout::Layout> {
        let p: &Program<'_> = self.cx.p;
        let t = self.cx.deep(t);
        // A layout answer inside body const evaluation (`size_of` in a
        // const block or array length) is baked into the body: record
        // the layout reads, as `layout_query` does.
        p.record_layout_reads(&mut self.cx.out.reads, &self.cx.tys, t);
        crate::ty::layout::layout_of_ty(&self.cx.tys, &UserLayout(p), t).ok()
    }
    fn adt_repr(&self, adt: AdtId) -> crate::ty::layout::Repr {
        self.cx.p.adt(adt).repr
    }
    fn discriminant(&self, adt: AdtId, variant: u32) -> i128 {
        self.cx.p.adt(adt).variants[variant as usize].disc
    }
    fn is_enum(&self, adt: AdtId) -> bool {
        adt.0 < u32::MAX - 1 && self.cx.p.adt(adt).is_enum
    }
    fn named_field_private(&mut self, adt: AdtId, field: Sym) -> bool {
        // A privacy answer inside body const evaluation (a `const`
        // block the checker does not walk) depends on the Adt's
        // member visibility: record the same `Sig(adt)` read as
        // `check_field_vis`, so a visibility edit rechecks it.
        let p = self.cx.p;
        if p.resolved.is_some()
            && let Some(def) = p.defs.def_of_adt(adt)
        {
            let _ = p.sig_of(&mut self.cx.out.reads, def);
        }
        crate::check::collect::named_field_is_private(p, adt, field, self.cx.module)
    }
    fn tuple_field_private(&mut self, adt: AdtId, index: u32) -> bool {
        let p = self.cx.p;
        if p.resolved.is_some()
            && let Some(def) = p.defs.def_of_adt(adt)
        {
            let _ = p.sig_of(&mut self.cx.out.reads, def);
        }
        crate::check::collect::tuple_field_is_private(p, adt, index, self.cx.module)
    }
}

/// The (Adt, variant) a path denotes in the compat tables.
fn variant_of(p: &Program<'_>, segs: &[ast::PathSeg]) -> Option<(AdtId, u32)> {
    // `std::cmp::Ordering::Less`: the same std variant paths
    // `resolve_assoc` answers, for const contexts.
    if segs.len() >= 4 {
        let path: Vec<&str> = segs.iter().map(|s| p.interner.get(s.name)).collect();
        return generics::std_variant_of(p, &path);
    }
    if segs.len() == 1 {
        let &a = p.type_names.get(&segs[0].name)?;
        if p.adt(a).is_enum {
            return None;
        }
        return Some((a, 0));
    }
    if segs.len() == 2 {
        let &a = p.type_names.get(&segs[0].name)?;
        let v = p.adt(a).variants.iter().position(|v| v.name == segs[1].name)?;
        return Some((a, v as u32));
    }
    None
}
/// The solver over one body's inference state (see
/// `traits::solve::SolveCx`): probes bind body variables and roll
/// back through the trail `bind_var` records.
impl<'p> SolveCx for Ctx<'p, '_> {
    type Snapshot = usize;
    type Store = Tys<'p>;

    fn tys(&mut self) -> &mut Tys<'p> {
        &mut self.tys
    }
    fn deep_resolve(&mut self, t: Ty) -> Ty {
        self.deep(t)
    }
    fn unify(&mut self, a: Ty, b: Ty) -> bool {
        self.unify(a, b)
    }
    fn fresh_var(&mut self) -> Ty {
        self.new_var(false)
    }
    fn fresh_const_var(&mut self) -> ConstId {
        Ctx::fresh_const_var(self)
    }
    fn unify_const(&mut self, a: ConstId, b: ConstId) -> bool {
        Ctx::unify_const(self, a, b)
    }
    fn resolve_const(&self, c: ConstId) -> ConstId {
        Ctx::resolve_const(self, c)
    }
    fn snapshot(&mut self) -> usize {
        self.trail.len()
    }
    /// Pops the trail: type variables, and const variables (ids at or
    /// above `INFER_MARKER_BASE`, see `unify_const`).
    fn rollback(&mut self, snap: usize) {
        while self.trail.len() > snap {
            let var = self.trail.pop().unwrap();
            if var >= generics::INFER_MARKER_BASE {
                self.const_bindings.remove(&var);
            } else {
                self.vars[var as usize].bound = None;
            }
        }
    }
    fn closure_select(&mut self, obl: TraitRef) -> Option<bool> {
        self.closure_select_impl(obl)
    }
    fn closure_output(&mut self, assoc: DefId, self_ty: Ty) -> Option<Ty> {
        self.closure_output_impl(assoc, self_ty)
    }
    fn structural(&mut self, tr: TraitRef) -> Option<bool> {
        let p = self.p;
        let lang = &p.gx.lang;
        let self_ty = self.tys.args(tr.args).first().and_then(|g| g.as_ty())?;
        let self_ty = self.deep(self_ty);
        if matches!(self.kind(self_ty), TyKind::Infer(_)) {
            return None;
        }
        if tr.def == lang.sized {
            return Some(self.sized_ok(self_ty));
        }
        if lang.is_auto(tr.def) {
            return self.auto_holds(tr.def, self_ty);
        }
        if p.gx.index.derive_family.contains(&tr.def)
            && matches!(self.kind(self_ty), TyKind::Tuple(_) | TyKind::Array(..) | TyKind::Slice(_) | TyKind::Ref(..) | TyKind::RawPtr(..) | TyKind::Closure(..))
        {
            return Some(self.derive_query_holds(tr.def, self_ty));
        }
        None
    }
    fn record_impl_set(&mut self, trait_def: DefId, self_ty: Ty, _failed: bool) {
        let p = self.p;
        let resolved = self.resolve(self_ty);
        let head = Head::of(&self.tys, resolved);
        p.impl_set(&mut self.out.reads, trait_def, head);
    }
}

/// W-BORROW (`note_closure_bounds`): true when a bound's type has a region
/// position of its own (a reference, an Adt with lifetime params, a
/// borrowing builtin, `dyn`, a closure or fn pointer), not counting type
/// params and projections.
fn bound_type_has_regions(p: &Program, t: Ty) -> bool {
    use crate::ty::iter::IterKind;
    match p.tys.kind(t) {
        TyKind::Ref(..) | TyKind::Dyn(..) | TyKind::Closure(..) | TyKind::FnPtr(_) | TyKind::FnDef(..) | TyKind::Opaque(..) => true,
        TyKind::Adt(def, args) => {
            matches!(p.tys.builtin_of(t), Some(BuiltinTy::Chars | BuiltinTy::Iter(IterKind::SliceIter | IterKind::SliceIterMut)))
                || p.gx.adt_lifetimes.get(&def).is_some_and(|v| !v.is_empty())
                || p.tys.args(args).iter().any(|g| g.as_ty().is_some_and(|e| bound_type_has_regions(p, e)))
        }
        TyKind::Tuple(ts) => p.tys.tys_of(ts).iter().any(|&e| bound_type_has_regions(p, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => bound_type_has_regions(p, e),
        _ => false,
    }
}
