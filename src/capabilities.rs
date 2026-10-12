// `lust capabilities [--json]`: what the supported Rust subset contains, and what it rejects.
//
// Where the compiler has a table, this output is generated from that table so it cannot drift:
// integer types from `IntTy::ALL`, std methods from the `Builtin` enum (an exhaustive match maps
// each builtin to its type and name), std free functions from `Builtin` plus the source std
// registry (`ty::lang::STD_FNS`, S5), macros from `MacroKind`, operators from `BinOp::symbol`,
// and error codes from the explain docs. The rejected list names the same feature strings as the
// `unsupported(...)` call sites; scripts/agentkit-test.sh greps those call sites and checks that
// every one appears here.
use crate::ast::{BinOp, ItemKind, MacroKind, Pat, UnOp};
use crate::check::Builtin;
use crate::diag;
use crate::explain;
use crate::intern::{Interner, Known, Sym};
use crate::ty::lang;
use crate::ty::{IntTy, TyKind};

/// Every `Builtin` variant. `builtin_info` matches exhaustively, so a new builtin cannot be
/// given a type and name by accident; the agentkit test counts the variants in check/mod.rs and
/// compares with the length of this list.
const ALL_BUILTINS: &[Builtin] = &[
    Builtin::StringNew,
    Builtin::StringFrom,
    Builtin::StringWithCapacity,
    Builtin::VecNew,
    Builtin::VecWithCapacity,
    Builtin::EnvArgs,
    Builtin::ArgsCount,
    Builtin::StrLen,
    Builtin::StrIsEmpty,
    Builtin::StrToString,
    Builtin::StringLen,
    Builtin::StringIsEmpty,
    Builtin::StringPushStr,
    Builtin::StringPush,
    Builtin::StringAsStr,
    Builtin::VecLen,
    Builtin::VecIsEmpty,
    Builtin::VecPush,
    Builtin::Clone,
    Builtin::ToString,
    Builtin::WrappingAdd,
    Builtin::WrappingSub,
    Builtin::WrappingMul,
    Builtin::Abs,
    Builtin::Pow,
    Builtin::Min,
    Builtin::Max,
    Builtin::OptIsSome,
    Builtin::OptIsNone,
    Builtin::OptUnwrap,
    Builtin::OptExpect,
    Builtin::OptUnwrapOr,
    Builtin::VecPop,
    Builtin::VecGet,
    Builtin::VecFirst,
    Builtin::VecLast,
    Builtin::VecContains,
    Builtin::VecSwap,
    Builtin::VecClear,
    Builtin::VecInsert,
    Builtin::VecRemove,
    Builtin::VecTruncate,
    Builtin::StrContains,
    Builtin::StrStartsWith,
    Builtin::StrEndsWith,
    Builtin::StrTrim,
    Builtin::StrToUppercase,
    Builtin::StrToLowercase,
    Builtin::StrChars,
    Builtin::CharsNext,
    Builtin::CharsCount,
    Builtin::CharIsDigit,
    Builtin::CharIsAlphabetic,
    Builtin::CharIsAlphanumeric,
    Builtin::CharIsWhitespace,
    Builtin::CharIsUppercase,
    Builtin::CharIsLowercase,
    Builtin::CharToUppercase,
    Builtin::CharToLowercase,
    Builtin::CharToDigit,
    Builtin::SliceLen,
    Builtin::SliceIsEmpty,
];

/// How a builtin is called.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Call {
    Method,
    Associated,
    Function,
}

/// The receiver or owner types of a builtin, the names it answers to, and how it is called.
/// Exhaustive on purpose: adding a `Builtin` variant fails to compile until it is listed here.
fn builtin_info(b: Builtin, k: &Known) -> (&'static [&'static str], Vec<Sym>, Call) {
    use Builtin as B;
    match b {
        B::StringNew => (&["String"], vec![k.new], Call::Associated),
        B::StringFrom => (&["String"], vec![k.from], Call::Associated),
        B::StringWithCapacity => (&["String"], vec![k.with_capacity], Call::Associated),
        B::VecNew => (&["Vec<T>"], vec![k.new], Call::Associated),
        B::VecWithCapacity => (&["Vec<T>"], vec![k.with_capacity], Call::Associated),
        B::EnvArgs => (&["std::env"], vec![k.args], Call::Function),
        B::ArgsCount => (&["std::env::Args"], vec![k.count], Call::Method),
        B::StrLen => (&["str"], vec![k.len], Call::Method),
        B::StrIsEmpty => (&["str"], vec![k.is_empty], Call::Method),
        B::StrToString => (&["str"], vec![k.to_string, k.to_owned], Call::Method),
        B::StringLen => (&["String"], vec![k.len], Call::Method),
        B::StringIsEmpty => (&["String"], vec![k.is_empty], Call::Method),
        B::StringPushStr => (&["String"], vec![k.push_str], Call::Method),
        B::StringPush => (&["String"], vec![k.push], Call::Method),
        B::StringAsStr => (&["String"], vec![k.as_str], Call::Method),
        B::VecLen => (&["Vec<T>"], vec![k.len], Call::Method),
        B::VecIsEmpty => (&["Vec<T>"], vec![k.is_empty], Call::Method),
        B::VecPush => (&["Vec<T>"], vec![k.push], Call::Method),
        B::Clone => (&["any Clone type"], vec![k.clone], Call::Method),
        B::ToString => (&["bool", "char", "integers", "String"], vec![k.to_string], Call::Method),
        B::WrappingAdd => (&["integers"], vec![k.wrapping_add], Call::Method),
        B::WrappingSub => (&["integers"], vec![k.wrapping_sub], Call::Method),
        B::WrappingMul => (&["integers"], vec![k.wrapping_mul], Call::Method),
        B::Abs => (&["signed integers"], vec![k.abs], Call::Method),
        B::Pow => (&["integers"], vec![k.pow], Call::Method),
        B::Min => (&["integers"], vec![k.min], Call::Method),
        B::Max => (&["integers"], vec![k.max], Call::Method),
        B::OptIsSome => (&["Option<T>"], vec![k.is_some], Call::Method),
        B::OptIsNone => (&["Option<T>"], vec![k.is_none], Call::Method),
        B::OptUnwrap => (&["Option<T>"], vec![k.unwrap], Call::Method),
        B::OptExpect => (&["Option<T>"], vec![k.expect], Call::Method),
        B::OptUnwrapOr => (&["Option<T>"], vec![k.unwrap_or], Call::Method),
        B::VecPop => (&["Vec<T>"], vec![k.pop], Call::Method),
        B::VecGet => (&["Vec<T>"], vec![k.get], Call::Method),
        B::VecFirst => (&["Vec<T>"], vec![k.first], Call::Method),
        B::VecLast => (&["Vec<T>"], vec![k.last], Call::Method),
        B::VecContains => (&["Vec<T>"], vec![k.contains], Call::Method),
        B::VecSwap => (&["Vec<T>"], vec![k.swap], Call::Method),
        B::VecClear => (&["Vec<T>"], vec![k.clear], Call::Method),
        B::VecInsert => (&["Vec<T>"], vec![k.insert], Call::Method),
        B::VecRemove => (&["Vec<T>"], vec![k.remove], Call::Method),
        B::VecTruncate => (&["Vec<T>"], vec![k.truncate], Call::Method),
        B::StrContains => (&["str", "String"], vec![k.contains], Call::Method),
        B::StrStartsWith => (&["str", "String"], vec![k.starts_with], Call::Method),
        B::StrEndsWith => (&["str", "String"], vec![k.ends_with], Call::Method),
        B::StrTrim => (&["str", "String"], vec![k.trim], Call::Method),
        B::StrToUppercase => (&["str", "String"], vec![k.to_uppercase], Call::Method),
        B::StrToLowercase => (&["str", "String"], vec![k.to_lowercase], Call::Method),
        B::StrChars => (&["str", "String"], vec![k.chars], Call::Method),
        B::CharsNext => (&["str::Chars"], vec![k.next], Call::Method),
        B::CharsCount => (&["str::Chars"], vec![k.count], Call::Method),
        B::CharIsDigit => (&["char"], vec![k.is_ascii_digit], Call::Method),
        B::CharIsAlphabetic => (&["char"], vec![k.is_ascii_alphabetic], Call::Method),
        B::CharIsAlphanumeric => (&["char"], vec![k.is_ascii_alphanumeric], Call::Method),
        B::CharIsWhitespace => (&["char"], vec![k.is_ascii_whitespace], Call::Method),
        B::CharIsUppercase => (&["char"], vec![k.is_ascii_uppercase], Call::Method),
        B::CharIsLowercase => (&["char"], vec![k.is_ascii_lowercase], Call::Method),
        B::CharToUppercase => (&["char"], vec![k.to_ascii_uppercase], Call::Method),
        B::CharToLowercase => (&["char"], vec![k.to_ascii_lowercase], Call::Method),
        B::CharToDigit => (&["char"], vec![k.to_digit], Call::Method),
        B::SliceLen => (&["[T]", "[T; n]"], vec![k.len], Call::Method),
        B::SliceIsEmpty => (&["[T]", "[T; n]"], vec![k.is_empty], Call::Method),
    }
}

/// Every macro kind, in `MacroKind` order. `macro_name` matches exhaustively.
const ALL_MACROS: &[MacroKind] = &[
    MacroKind::Println,
    MacroKind::Print,
    MacroKind::Eprintln,
    MacroKind::Eprint,
    MacroKind::Format,
    MacroKind::Panic,
    MacroKind::Vec,
    MacroKind::Assert,
    MacroKind::AssertEq,
    MacroKind::AssertNe,
    MacroKind::Todo,
    MacroKind::Unreachable,
];

fn macro_name(m: MacroKind, k: &Known) -> Sym {
    match m {
        MacroKind::Println => k.println,
        MacroKind::Print => k.print,
        MacroKind::Eprintln => k.eprintln,
        MacroKind::Eprint => k.eprint,
        MacroKind::Format => k.format,
        MacroKind::Panic => k.panic,
        MacroKind::Vec => k.vec,
        MacroKind::Assert => k.assert,
        MacroKind::AssertEq => k.assert_eq,
        MacroKind::AssertNe => k.assert_ne,
        MacroKind::Todo => k.todo,
        MacroKind::Unreachable => k.unreachable,
    }
}

// Exhaustive matches kept only so that adding an enum variant fails to compile until the
// lists below are reviewed. They are never called.
#[allow(dead_code)]
fn item_kind_label(k: &ItemKind) -> &'static str {
    match k {
        ItemKind::Fn(_) => "fn",
        ItemKind::Struct(_) => "struct",
        ItemKind::Enum(_) => "enum",
        ItemKind::Impl(_) => "impl",
        ItemKind::Use(_) => "use",
        ItemKind::Mod(_) => "mod (shape only)",
        ItemKind::Trait(_) => "trait (shape only)",
        ItemKind::Type(_) => "type alias (shape only)",
        ItemKind::Const(_) => "const (shape only)",
        ItemKind::Static(_) => "static (shape only)",
        ItemKind::MacroRules(_) => "macro_rules (shape only)",
        ItemKind::ExternCrate(_) => "extern crate (shape only)",
        ItemKind::ExternBlock(_) => "extern block (shape only)",
        ItemKind::Union(_) => "union (shape only)",
        ItemKind::MacroCall(_) => "item macro call (shape only)",
    }
}

#[allow(dead_code)]
fn ty_kind_label(k: &TyKind) -> &'static str {
    // String, Vec<T>, Option<T>, std::env::Args, and str::Chars are Adt types with
    // builtin defs since S3a; the capability lists below still name them on their own.
    match k {
        TyKind::Error => "error placeholder",
        TyKind::Unit => "()",
        TyKind::Bool => "bool",
        TyKind::Char => "char",
        TyKind::Str => "str",
        TyKind::Never => "!",
        TyKind::Int(_) => "integers",
        TyKind::Float(_) => "floats (representation only)",
        TyKind::Ref(..) => "&T and &mut T",
        TyKind::RawPtr(..) => "raw pointers (representation only)",
        TyKind::Slice(_) => "slices (representation only)",
        TyKind::Array(..) => "arrays",
        TyKind::Tuple(_) => "tuples",
        TyKind::Adt(..) => "String, Vec<T>, Option<T>, std::env::Args, str::Chars, user structs and enums",
        TyKind::FnPtr(_) => "fn pointers (representation only)",
        TyKind::FnDef(..) => "fn items (representation only)",
        TyKind::Closure(..) => "closures (representation only)",
        TyKind::Dyn(..) => "dyn Trait (representation only)",
        TyKind::Opaque(..) => "impl Trait (representation only)",
        TyKind::Param(_) => "generic parameters (representation only)",
        TyKind::Projection(..) => "associated types (representation only)",
        TyKind::Infer(_) => "inference variable",
    }
}

#[allow(dead_code)]
fn pat_label(p: &Pat) -> &'static str {
    match p {
        Pat::Wild => "_",
        Pat::Binding { .. } => "bindings",
        Pat::Lit(_) => "literals",
        Pat::Path(_) => "paths and unit variants",
        Pat::TupleStruct { .. } => "tuple-struct patterns",
        Pat::Struct { .. } => "struct patterns",
        Pat::Or(_) => "or patterns",
        Pat::Range { .. } => "range patterns",
        Pat::Tuple(_) => "tuple patterns",
        Pat::Slice { .. } => "slice patterns",
        Pat::Ref { .. } => "reference patterns",
        Pat::At { .. } => "@ patterns",
        Pat::Rest => "rest patterns",
        Pat::Paren(_) => "parenthesized patterns (shape only)",
        Pat::QPath { .. } => "qualified path patterns (shape only)",
        Pat::MacroCall(_) => "macro patterns (shape only)",
    }
}

/// Features lust rejects, with the code it reports. The strings mirror the messages at the
/// `unsupported(...)` and `not_yet(...)` call sites; the agentkit test greps the former.
const REJECTED: &[(&str, &str)] = &[
    ("references in struct and enum fields", "L0201"),
    ("lifetime names such as 'a", "L0203"),
    ("user macros (macro_rules! definitions and calls)", "L0401"),
    ("attributes lust does not know by name (named in the message)", "L0402"),
    ("known attributes such as cfg, repr, path, and inline (named in the message)", "L0522"),
    ("deriving traits other than Debug, Clone, Copy, PartialEq, Eq, Hash (named in the message)", "L0403"),
    ("`unsafe` blocks and functions", "L0404"),
    ("`async` functions and blocks", "L0405"),
    ("moving a field out of a struct or enum", "L9001"),
    ("destructuring in `let` without an initializer", "L9001"),
    ("turbofish on method calls", "L0721"),
    ("ranges outside `for` loops", "L9001"),
    ("module paths", "L0505"),
    ("module paths in types", "L0505"),
    ("open ranges", "L9001"),
    ("iterating a Vec by value", "L9001"),
    ("refutable patterns here (in `let` and parameters)", "L9001"),
    ("bindings inside `|` patterns", "L9001"),
    ("#[derive(PartialOrd)]", "L9001"),
    ("#[derive(Ord)]", "L9001"),
    ("#[derive(Default)]", "L9001"),
    ("the `HashMap` type", "L0641"),
    ("the `HashSet` type", "L0641"),
    ("the `BTreeMap` type", "L0641"),
    ("the `Result` type", "L0641"),
    ("the `Box` type", "L0641"),
    ("the `Rc` type", "L0641"),
    ("the `Arc` type", "L0641"),
    ("the `RefCell` type", "L0641"),
    ("the `Cell` type", "L0641"),
    ("the `f32` type", "L0641"),
    ("the `f64` type", "L0641"),
    ("the `i128` type", "L0641"),
    ("the `u128` type", "L0641"),
    ("trait definitions", "L0614"),
    ("modules", "L0505"),
    ("const and static items", "L0632"),
    ("type aliases", "L0602"),
    ("generic functions", "L0614"),
    ("generic structs", "L0614"),
    ("generic enums", "L0614"),
    ("generic impls", "L0614"),
    ("typed `self` parameters", "L0721"),
    ("patterns in parameters", "L0820"),
    ("where clauses", "L0614"),
    ("explicit enum discriminants", "L0632"),
    ("trait impls", "L0614"),
    ("associated consts and types", "L0621"),
    ("`impl Trait` types", "L0602"),
    ("`dyn Trait` types", "L0602"),
    ("function pointer types", "L0602"),
    ("items inside function bodies", "L0820"),
    ("let-else", "L0820"),
    ("closures", "L0820"),
    ("the `?` operator", "L0820"),
    ("floating point numbers", "L0641"),
    ("named format arguments", "L0641"),
    ("format spec forms other than {} and {:?} (named in the message)", "L0641"),
    ("#[test] functions inside impl blocks", "L9001"),
    ("absolute paths (`::a::b`)", "L0505"),
    ("`extern crate` items", "L0505"),
    ("module paths (`crate::` and `super::`)", "L0505"),
    ("module paths (`self::`)", "L0505"),
    ("associated bindings in generic arguments", "L0621"),
    ("qualified paths", "L0621"),
    ("const functions", "L0632"),
    ("const generic arguments", "L0632"),
    ("inline const blocks", "L0632"),
    ("inferred expressions (`_`)", "L0820"),
    ("let chains", "L0820"),
    ("raw references (`&raw`)", "L0820"),
    ("tuple struct patterns with field numbers", "L0820"),
    ("variadic parameters", "L0820"),
    ("extern blocks", "L0810"),
    ("extern functions", "L0810"),
    ("byte string and byte char literals", "L0641"),
    ("float and byte literals in patterns", "L0641"),
    ("higher-ranked (`for<..>`) types and bounds", "L0614"),
    ("unions", "L0602"),
    ("extern function types", "L0602"),
    ("raw pointer types", "L0602"),
    ("inferred types (`_`)", "L0602"),
    ("this type form", "L0602"),
];

const ITEMS: &[&str] = &[
    "fn",
    "struct (named fields, tuple fields, or unit)",
    "enum (unit, tuple, and struct variants)",
    "impl (inherent only)",
    "use (parsed, no effect yet)",
];

const TYPES: &[&str] = &[
    "bool",
    "char",
    "() unit",
    "! never",
    "String",
    "&str",
    "Vec<T>",
    "Option<T>",
    "&T",
    "&mut T",
    "user structs and enums",
    "tuples",
    "arrays [T; n]",
    "slices &[T] and &mut [T]",
    "std::env::Args (from std::env::args())",
    "str::Chars (from s.chars())",
];

const CONTROL_FLOW: &[&str] = &[
    "if / else",
    "if let",
    "match (guards, or patterns, ranges, nested patterns)",
    "loop (break with a value)",
    "while",
    "while let",
    "for over ranges, &Vec, &mut Vec, and s.chars()",
    "break and continue, with labels",
    "labeled blocks with break values",
    "early return",
    "blocks as expressions",
];

const PATTERNS: &[&str] = &[
    "_ wildcard",
    "bindings (mut, ref, default binding modes)",
    "literals",
    "paths and unit variants",
    "tuple-struct patterns",
    "tuple patterns with ..",
    "struct patterns with ..",
    "or patterns a | b",
    "range patterns",
    "reference patterns &p and &mut p",
    "@ bindings",
    "slice patterns [a, rest @ .., b]",
    "half-open range patterns",
];

const EXPRESSIONS: &[&str] = &[
    "struct literals, with ..base update",
    "method calls with autoderef and autoref",
    "field access",
    "indexing v[i] and a[i]",
    "tuple values and tuple field access .0",
    "array literals and [value; count] repeat",
    "ranges a..b and a..=b (in for)",
    "casts with as (between integers, from bool and char, u8 to char)",
    "format strings with {}, {:?}, positions, and captured names",
    "vec! literals with [value; count]",
    "assignment and compound assignment",
];

const DERIVES: &[&str] = &["Debug", "Clone", "Copy", "PartialEq", "Eq (accepted, no effect yet)", "Hash (accepted, no effect yet)"];

/// Grouped std surface: type name to sorted method or associated-function names.
fn grouped(want: Call) -> Vec<(String, Vec<String>)> {
    let interner = Interner::default();
    let known = Known::new(&interner);
    let mut groups: Vec<(String, Vec<String>)> = Vec::new();
    for &b in ALL_BUILTINS {
        let (types, names, call) = builtin_info(b, &known);
        if call != want {
            continue;
        }
        for t in types {
            let entry = match groups.iter_mut().find(|(g, _)| g == t) {
                Some(e) => e,
                None => {
                    groups.push((t.to_string(), Vec::new()));
                    groups.last_mut().expect("just pushed")
                }
            };
            for &n in &names {
                let name = interner.get(n).to_string();
                if !entry.1.contains(&name) {
                    entry.1.push(name);
                }
            }
        }
    }
    for (_, names) in &mut groups {
        names.sort();
    }
    groups
}

fn json_arr(items: &[String]) -> String {
    let parts: Vec<String> = items.iter().map(|s| diag::json_str(s)).collect();
    format!("[{}]", parts.join(","))
}

fn json_str_arr(items: &[&str]) -> String {
    json_arr(&items.iter().map(|s| s.to_string()).collect::<Vec<_>>())
}

fn json_groups(groups: &[(String, Vec<String>)]) -> String {
    let parts: Vec<String> = groups.iter().map(|(t, names)| format!("{}:{}", diag::json_str(t), json_arr(names))).collect();
    format!("{{{}}}", parts.join(","))
}

/// Entry point for `lust capabilities`. Returns the process exit code.
pub fn run(args: &[String]) -> i32 {
    let json = match args {
        [] => false,
        [a] if a == "--json" => true,
        _ => {
            eprintln!("usage: lust capabilities [--json]");
            return 2;
        }
    };
    let interner = Interner::default();
    let known = Known::new(&interner);
    // Supported types only: `IntTy::ALL` also carries the representation-only 128-bit forms.
    let int_types: Vec<String> = IntTy::ALL_SUPPORTED.iter().map(|t| t.name().to_string()).collect();
    let macros: Vec<String> = ALL_MACROS.iter().map(|&m| format!("{}!", interner.get(macro_name(m, &known)))).collect();
    let attributes: Vec<String> =
        [known.derive, known.test, known.allow, known.warn, known.deny].iter().map(|&s| interner.get(s).to_string()).collect();
    let binops: Vec<String> = [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::Div,
        BinOp::Rem,
        BinOp::BitAnd,
        BinOp::BitOr,
        BinOp::BitXor,
        BinOp::Shl,
        BinOp::Shr,
        BinOp::Eq,
        BinOp::Ne,
        BinOp::Lt,
        BinOp::Le,
        BinOp::Gt,
        BinOp::Ge,
        BinOp::And,
        BinOp::Or,
    ]
    .iter()
    .map(|o| o.symbol().to_string())
    .collect();
    let unops: Vec<String> = [UnOp::Neg, UnOp::Not]
        .iter()
        .map(|o| match o {
            UnOp::Neg => "-".to_string(),
            UnOp::Not => "!".to_string(),
        })
        .collect();
    let methods = grouped(Call::Method);
    let associated = grouped(Call::Associated);
    let mut functions = grouped(Call::Function);
    // Source std fns join the free-function list from their registry
    // rows, so the output cannot drift from the loader (S5).
    for def in lang::STD_FNS.iter().filter(|d| d.implemented) {
        let key = def.path[..def.path.len() - 1].join("::");
        let name = def.path[def.path.len() - 1].to_string();
        match functions.iter_mut().find(|(g, _)| *g == key) {
            Some(e) => {
                if !e.1.contains(&name) {
                    e.1.push(name);
                    e.1.sort();
                }
            }
            None => functions.push((key, vec![name])),
        }
    }
    let codes = explain::codes();

    if json {
        let rejected: Vec<String> =
            REJECTED.iter().map(|(f, c)| format!("{{\"feature\":{},\"code\":\"{}\"}}", diag::json_str(f), c)).collect();
        let code_objs: Vec<String> = codes.iter().map(|(c, t)| format!("{{\"code\":\"{}\",\"title\":{}}}", c, diag::json_str(t))).collect();
        println!(
            "{{\"schema\":1,\"kind\":\"capabilities\",\"commands\":{},\"items\":{},\"types\":{},\"integer_types\":{},\"methods\":{},\"associated_functions\":{},\"functions\":{},\"macros\":{},\"attributes\":{},\"derives\":{},\"operators\":{{\"binary\":{},\"unary\":{}}},\"control_flow\":{},\"patterns\":{},\"expressions\":{},\"rejected\":[{}],\"diagnostics\":{{\"schema\":{},\"codes\":[{}]}}}}",
            json_str_arr(&["check", "build", "run", "test", "explain", "capabilities", "daemon"]),
            json_str_arr(ITEMS),
            json_str_arr(TYPES),
            json_arr(&int_types),
            json_groups(&methods),
            json_groups(&associated),
            json_groups(&functions),
            json_arr(&macros),
            json_arr(&attributes),
            json_str_arr(DERIVES),
            json_arr(&binops),
            json_arr(&unops),
            json_str_arr(CONTROL_FLOW),
            json_str_arr(PATTERNS),
            json_str_arr(EXPRESSIONS),
            rejected.join(","),
            diag::SCHEMA,
            code_objs.join(",")
        );
    } else {
        let list = |name: &str, items: &[String]| println!("{name}: {}", items.join(", "));
        println!("lust capabilities (schema 1)");
        list(
            "commands",
            &["check".into(), "build".into(), "run".into(), "test".into(), "explain".into(), "capabilities".into(), "daemon".into()],
        );
        list("items", &ITEMS.iter().map(|s| s.to_string()).collect::<Vec<_>>());
        list("types", &TYPES.iter().map(|s| s.to_string()).collect::<Vec<_>>());
        list("integer types", &int_types);
        for (t, names) in &methods {
            println!("methods on {t}: {}", names.join(", "));
        }
        for (t, names) in &associated {
            println!("associated functions on {t}: {}", names.join(", "));
        }
        for (t, names) in &functions {
            println!("functions in {t}: {}", names.join(", "));
        }
        list("macros", &macros);
        list("attributes", &attributes);
        list("derives", &DERIVES.iter().map(|s| s.to_string()).collect::<Vec<_>>());
        list("binary operators", &binops);
        list("unary operators", &unops);
        list("control flow", &CONTROL_FLOW.iter().map(|s| s.to_string()).collect::<Vec<_>>());
        list("patterns", &PATTERNS.iter().map(|s| s.to_string()).collect::<Vec<_>>());
        println!("rejected features ({}):", REJECTED.len());
        for (f, c) in REJECTED {
            println!("  {f} [{c}]");
        }
        println!("diagnostic codes ({}): run `lust explain <code>`", codes.len());
    }
    0
}
