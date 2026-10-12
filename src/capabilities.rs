// `lust capabilities [--json]`: what the supported Rust subset contains, and what it rejects.
//
// Where the compiler has a table, this output is generated from that table so it cannot drift:
// integer types from `IntTy::ALL`, std methods from the `Builtin` enum (an exhaustive match maps
// each builtin to its type and name), macros from `MacroKind`, operators from `BinOp::symbol`,
// and error codes from the explain docs. The rejected list names the same feature strings as the
// `unsupported(...)` call sites; scripts/agentkit-test.sh greps those call sites and checks that
// every one appears here.
use crate::ast::{BinOp, ItemKind, MacroKind, Pat, UnOp};
use crate::check::Builtin;
use crate::diag;
use crate::explain;
use crate::intern::{Interner, Known, Sym};
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
        ItemKind::Use => "use",
    }
}

#[allow(dead_code)]
fn ty_kind_label(k: &TyKind) -> &'static str {
    match k {
        TyKind::Error => "error placeholder",
        TyKind::Unit => "()",
        TyKind::Bool => "bool",
        TyKind::Char => "char",
        TyKind::Str => "str",
        TyKind::String => "String",
        TyKind::Never => "!",
        TyKind::Int(_) => "integers",
        TyKind::Vec(_) => "Vec<T>",
        TyKind::Option(_) => "Option<T>",
        TyKind::Ref(..) => "&T and &mut T",
        TyKind::Adt(_) => "user structs and enums",
        TyKind::Args => "std::env::Args",
        TyKind::Chars => "str::Chars",
        TyKind::Var(..) => "inference variable",
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
    }
}

/// Features lust rejects, with the code it reports. The strings mirror the messages at the
/// `unsupported(...)` call sites, which the agentkit test greps for.
const REJECTED: &[(&str, &str)] = &[
    ("references in struct and enum fields", "L0201"),
    ("lifetime names such as 'a", "L0203"),
    ("user macros (macro_rules! definitions and calls)", "L0401"),
    ("attributes other than derive, test, allow, warn, deny (named in the message)", "L0402"),
    ("deriving traits other than Debug, Clone, Copy, PartialEq, Eq, Hash (named in the message)", "L0403"),
    ("`unsafe` blocks and functions", "L0404"),
    ("`async` functions and blocks", "L0405"),
    ("moving a field out of a struct or enum", "L9001"),
    ("destructuring in `let`", "L9001"),
    ("turbofish on method calls", "L9001"),
    ("ranges outside `for` loops", "L9001"),
    ("module paths", "L9001"),
    ("module paths in types", "L9001"),
    ("open ranges", "L9001"),
    ("iterating a Vec by value", "L9001"),
    ("refutable patterns here (in `let` and parameters)", "L9001"),
    ("bindings inside `|` patterns", "L9001"),
    ("#[derive(PartialOrd)]", "L9001"),
    ("#[derive(Ord)]", "L9001"),
    ("#[derive(Default)]", "L9001"),
    ("`HashMap` type", "L9001"),
    ("`HashSet` type", "L9001"),
    ("`BTreeMap` type", "L9001"),
    ("`Result` type", "L9001"),
    ("`Box` type", "L9001"),
    ("`Rc` type", "L9001"),
    ("`Arc` type", "L9001"),
    ("`RefCell` type", "L9001"),
    ("`Cell` type", "L9001"),
    ("`f32` type", "L9001"),
    ("`f64` type", "L9001"),
    ("`i128` type", "L9001"),
    ("`u128` type", "L9001"),
    ("trait definitions", "L9001"),
    ("modules", "L9001"),
    ("const and static items", "L9001"),
    ("type aliases", "L9001"),
    ("generic functions", "L9001"),
    ("generic structs", "L9001"),
    ("generic enums", "L9001"),
    ("generic impls", "L9001"),
    ("typed `self` parameters", "L9001"),
    ("patterns in parameters", "L9001"),
    ("where clauses", "L9001"),
    ("tuple structs", "L9001"),
    ("explicit enum discriminants", "L9001"),
    ("trait impls", "L9001"),
    ("associated consts and types", "L9001"),
    ("tuple types", "L9001"),
    ("array and slice types", "L9001"),
    ("`impl Trait` and `dyn Trait` types", "L9001"),
    ("function pointer types", "L9001"),
    ("items inside function bodies", "L9001"),
    ("let-else", "L9001"),
    ("`..` in tuple patterns", "L9001"),
    ("tuple patterns", "L9001"),
    ("slice patterns", "L9001"),
    ("reference patterns", "L9001"),
    ("closures", "L9001"),
    ("tuple fields", "L9001"),
    ("the `?` operator", "L9001"),
    ("floating point numbers", "L9001"),
    ("tuples", "L9001"),
    ("array literals", "L9001"),
    ("loop labels", "L9001"),
    ("struct update syntax", "L9001"),
    ("named format arguments", "L9001"),
    ("format spec `{:...}` forms other than {} and {:?} (named in the message)", "L9001"),
    ("#[test] functions inside impl blocks", "L9001"),
];

const ITEMS: &[&str] = &[
    "fn",
    "struct (named fields or unit)",
    "enum (unit, tuple, and struct variants)",
    "impl (inherent only)",
    "use (parsed, no effect yet)",
];

const TYPES: &[&str] = &[
    "bool",
    "char",
    "() unit",
    "String",
    "&str",
    "Vec<T>",
    "Option<T>",
    "&T",
    "&mut T",
    "user structs and enums",
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
    "break and continue",
    "early return",
    "blocks as expressions",
];

const PATTERNS: &[&str] = &[
    "_ wildcard",
    "bindings (mut, ref, default binding modes)",
    "literals",
    "paths and unit variants",
    "tuple-struct patterns",
    "struct patterns with ..",
    "or patterns a | b",
    "range patterns",
];

const EXPRESSIONS: &[&str] = &[
    "struct literals",
    "method calls with autoderef and autoref",
    "field access",
    "indexing v[i]",
    "ranges a..b and a..=b (in for)",
    "casts with as (between integers, from bool and char, u8 to char)",
    "format strings with {}, {:?}, positions, and captured names",
    "vec! literals with [value; count]",
    "assignment and compound assignment",
];

const DERIVES: &[&str] = &["Debug", "Clone", "Copy", "PartialEq", "Eq (accepted, no effect yet)", "Hash (accepted, no effect yet)"];

/// Grouped std surface: type name to sorted method or associated-function names.
fn grouped(want: Call) -> Vec<(&'static str, Vec<String>)> {
    let interner = Interner::default();
    let known = Known::new(&interner);
    let mut groups: Vec<(&'static str, Vec<String>)> = Vec::new();
    for &b in ALL_BUILTINS {
        let (types, names, call) = builtin_info(b, &known);
        if call != want {
            continue;
        }
        for t in types {
            let entry = match groups.iter_mut().find(|(g, _)| g == t) {
                Some(e) => e,
                None => {
                    groups.push((t, Vec::new()));
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

fn json_groups(groups: &[(&str, Vec<String>)]) -> String {
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
    let int_types: Vec<String> = IntTy::ALL.iter().map(|t| t.name().to_string()).collect();
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
    let functions = grouped(Call::Function);
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
