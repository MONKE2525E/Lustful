#!/usr/bin/env python3
# Definition checks (fx-defcheck, SOL-COVERAGE-4 section C): a written
# type or bound in a definition must be well-formed where it is
# written, with no use of the item, exactly where rustc checks it
# (aliases and multi-param defaults are lazy in rustc and must stay
# accepted). Each generated program pairs one owner kind (alias,
# trait const, supertrait, fn/struct bound, impl header, default
# parameter, const item, trait default body, generic fn body,
# derive, impl supertrait obligation) with a valid or invalid inner
# type or bound, used or unused.
#
# Every case runs rustc 1.99, cold `lust check`, and (when both
# accept) built binaries compared on stdout and exit code. A lust
# timeout is a hang, never a reject. Exit 1 on any false accept
# (rustc rejects, lust check or build accepts), wrong output, or
# hang. False rejects are listed for review (lust is a subset).
#
# Usage: python3 scripts/defcheck_sweep.py [--jobs J] [--family F]
#        [--keep DIR]   (needs target/release/lust built)
import argparse, os, subprocess, sys, tempfile
from concurrent.futures import ProcessPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LUST = os.path.join(ROOT, "target/release/lust")

NEED = "struct Need<T: Copy>(T);\n"
SUP = "trait Sup<T: Copy> {}\n"
MAIN0 = "fn main() {}\n"
MAINP = 'fn main() { println!("ok"); }\n'

# An argument state: (name, type text, value expr of that type).
GOOD = ("good", "u8", "1u8")
BAD = ("bad", "String", "String::new()")
ARGS = [GOOD, BAD]

CASES = []  # (family, name, source)


def case(family, name, src):
    CASES.append((family, name, src))


def build_cases():
    for an, aty, aexpr in ARGS:
        case("alias", f"alias_unused_{an}", NEED + f"type X = Need<{aty}>;\n" + MAINP)
        case("alias", f"alias_nested_unused_{an}", NEED + f"type X = Option<Need<{aty}>>;\n" + MAINP)
        case("alias", f"alias_used_sig_{an}", NEED + f"type X = Need<{aty}>;\nfn f(_x: X) {{}}\n" + MAINP)
        case("alias", f"alias_used_let_{an}", NEED + f"type X = Need<{aty}>;\nfn main() {{ let _x: Option<X> = None; println!(\"ok\"); }}\n")
        case("alias", f"alias_used_field_{an}", NEED + f"type X = Need<{aty}>;\nstruct S {{ f: X }}\n" + MAINP)
        case("alias", f"alias_used_ret_{an}", NEED + f"type X = Need<{aty}>;\nfn f() -> X {{ Need({aexpr}) }}\n" + MAINP)
        case("alias", f"alias_generic_used_{an}", NEED + f"type X<T> = Need<T>;\nfn main() {{ let _x: Option<X<{aty}>> = None; println!(\"ok\"); }}\n")
        case("alias", f"alias_default_{an}", f"type X<T: Copy = {aty}> = Option<T>;\n" + MAINP)
        case("alias", f"alias_default_used_{an}", f"type X<T: Copy = {aty}> = Option<T>;\nfn main() {{ let _x: X = None; println!(\"ok\"); }}\n")
        case("traitconst", f"trait_const_req_{an}", NEED + f"trait Tr {{ const C: Need<{aty}>; }}\n" + MAINP)
        case("traitconst", f"trait_const_nested_{an}", NEED + f"trait Tr {{ const C: Option<Need<{aty}>>; }}\n" + MAINP)
        case("traitconst", f"trait_const_default_{an}", NEED + f"trait Tr {{ const C: Need<{aty}> = Need({aexpr}); }}\n" + MAINP)
        case("bound", f"supertrait_{an}", SUP + f"trait Sub: Sup<{aty}> {{}}\n" + MAINP)
        case("bound", f"supertrait_where_{an}", SUP + f"trait Sub where Self: Sup<{aty}> {{}}\n" + MAINP)
        case("bound", f"fn_bound_{an}", SUP + f"fn f<T: Sup<{aty}>>(_x: T) {{}}\n" + MAINP)
        case("bound", f"fn_where_{an}", SUP + f"fn f<T>(_x: T) where T: Sup<{aty}> {{}}\n" + MAINP)
        case("bound", f"fn_impl_trait_{an}", SUP + f"fn f(_x: impl Sup<{aty}>) {{}}\n" + MAINP)
        case("bound", f"struct_bound_{an}", SUP + f"struct S<T: Sup<{aty}>>(T);\n" + MAINP)
        case("bound", f"enum_bound_{an}", SUP + f"enum E<T: Sup<{aty}>> {{ V(T) }}\n" + MAINP)
        case("bound", f"assoc_bound_{an}", SUP + f"trait Tr {{ type A2: Sup<{aty}>; }}\n" + MAINP)
        case("bound", f"dyn_bound_{an}", SUP + f"fn f(_x: &dyn Sup<{aty}>) {{}}\n" + MAINP)
        case("bound", f"alias_bound_{an}", SUP + f"type X<T: Sup<{aty}>> = Option<T>;\n" + MAINP)
        case("impl", f"impl_trait_arg_{an}", SUP + f"struct S;\nimpl Sup<{aty}> for S {{}}\n" + MAINP)
        case("impl", f"impl_self_ty_{an}", NEED + f"trait Tr2 {{}}\nimpl Tr2 for Need<{aty}> {{}}\n" + MAINP)
        case("impl", f"impl_assoc_ty_{an}", NEED + f"trait Tr {{ type A2; }}\nstruct S;\nimpl Tr for S {{ type A2 = Need<{aty}>; }}\n" + MAINP)
        case("impl", f"binding_ty_{an}", NEED + f"trait Tr {{ type A2; }}\nfn f<T: Tr<A2 = Need<{aty}>>>(_x: T) {{}}\n" + MAINP)
        case("direct", f"fn_sig_{an}", NEED + f"fn f(_x: Need<{aty}>) {{}}\n" + MAINP)
        case("direct", f"fn_ret_{an}", NEED + f"fn f() -> Need<{aty}> {{ Need({aexpr}) }}\n" + MAINP)
        case("direct", f"field_{an}", NEED + f"struct S {{ f: Need<{aty}> }}\n" + MAINP)
        case("direct", f"enum_field_{an}", NEED + f"enum E {{ V(Need<{aty}>) }}\n" + MAINP)
        case("direct", f"const_item_{an}", NEED + f"const C: Need<{aty}> = Need({aexpr});\n" + MAINP)
        case("direct", f"inherent_const_{an}", NEED + f"struct S;\nimpl S {{ const C: Need<{aty}> = Need({aexpr}); }}\n" + MAINP)
        case("default", f"default_single_unused_{an}", f"struct D<T: Copy = {aty}>(T);\n" + MAINP)
        case("default", f"default_single_used_{an}", f"struct D<T: Copy = {aty}>(T);\nfn main() {{ let _x: Option<D> = None; println!(\"ok\"); }}\n")
        case("default", f"trait_default_unused_{an}", f"trait Tr<T: Copy = {aty}> {{}}\n" + MAINP)
        case("default", f"trait_default_bound_{an}", f"trait Tr<T: Copy = {aty}> {{}}\nfn f<X: Tr>(_x: X) {{}}\n" + MAINP)
    # Generic-parameter forms: the bound comes from the item env or not.
    case("alias", "alias_generic_unused_free", NEED + "type X<T> = Need<T>;\n" + MAINP)
    case("alias", "alias_generic_unused_bound", NEED + "type X<T: Copy> = Need<T>;\n" + MAINP)
    case("traitconst", "trait_const_generic_free", NEED + "trait Tr<T> { const C: Need<T>; }\n" + MAINP)
    case("traitconst", "trait_const_generic_bound", NEED + "trait Tr<T: Copy> { const C: Need<T>; }\n" + MAINP)
    case("traitconst", "trait_const_generic_where", NEED + "trait Tr<T> where T: Copy { const C: Need<T>; }\n" + MAINP)
    case("traitconst", "trait_const_self_assoc_bound", NEED + "trait Tr { type A2: Copy; const C: Need<Self::A2>; }\n" + MAINP)
    case("traitconst", "trait_const_self_assoc_free", NEED + "trait Tr { type A2; const C: Need<Self::A2>; }\n" + MAINP)
    case("traitconst", "trait_const_unsized", "trait Tr { const C: [u8]; }\n" + MAINP)
    case("bound", "supertrait_param_bound", SUP + "trait Sub<T: Copy>: Sup<T> {}\n" + MAINP)
    case("bound", "supertrait_param_free", SUP + "trait Sub<T>: Sup<T> {}\n" + MAINP)
    case("bound", "fn_bound_env_proof", SUP + "fn f<T, X: Copy>(_x: T, _y: X) where T: Sup<X> {}\n" + MAINP)
    case("bound", "fn_bound_env_missing", SUP + "fn f<T, X>(_x: T, _y: X) where T: Sup<X> {}\n" + MAINP)
    case("bound", "fn_bound_super_chain", "trait Sub: Copy {}\ntrait SupS<T: Sub> {}\nfn f<T, X: Sub>(_x: T, _y: X) where T: SupS<X> {}\n" + MAINP)
    case("bound", "multi_param_trait_gg", "trait Sup2<T: Copy, U: Clone> {}\nfn f<X: Sup2<u8, String>>(_x: X) {}\n" + MAINP)
    case("bound", "multi_param_trait_bg", "trait Sup2<T: Copy, U: Clone> {}\nfn f<X: Sup2<String, String>>(_x: X) {}\n" + MAINP)
    case("bound", "multi_param_trait_gb", "struct NoClone;\ntrait Sup2<T: Copy, U: Clone> {}\nfn f<X: Sup2<u8, NoClone>>(_x: X) {}\n" + MAINP)
    case("bound", "multi_param_trait_bb", "struct NoClone;\ntrait Sup2<T: Copy, U: Clone> {}\nfn f<X: Sup2<String, NoClone>>(_x: X) {}\n" + MAINP)
    case("bound", "where_form_trait_param", "trait SupW<T> where T: Copy {}\nfn f<X: SupW<String>>(_x: X) {}\n" + MAINP)
    case("bound", "where_form_trait_param_ok", "trait SupW<T> where T: Copy {}\nfn f<X: SupW<u8>>(_x: X) {}\n" + MAINP)
    # Defaults that mention two parameters (C4): lazy unused, checked on use.
    pair = "trait Pair<B> {}\nstruct D<A: Pair<B> = u8, B = u16>(A, B);\n"
    pair_impl = "trait Pair<B> {}\nimpl Pair<u16> for u8 {}\nstruct D<A: Pair<B> = u8, B = u16>(A, B);\n"
    for tag, pre in (("noimpl", pair), ("impl", pair_impl)):
        case("default", f"default_pair_unused_{tag}", pre + MAINP)
        case("default", f"default_pair_sig_{tag}", pre + "fn f(_x: D) {}\n" + MAINP)
        case("default", f"default_pair_let_{tag}", pre + 'fn main() { let _x: Option<D> = None; println!("ok"); }\n')
        case("default", f"default_pair_ctor_{tag}", pre + 'fn main() { let _ = D(1u8, 2u16); println!("ok"); }\n')
        case("default", f"default_pair_field_{tag}", pre + "struct S { f: D }\n" + MAINP)
    case("default", "default_pair_one_default", "trait Pair<B> {}\nstruct D<A: Pair<B>, B = u16>(A, B);\nfn f(_x: D<u8>) {}\n" + MAINP)
    case("default", "default_dep_on_param", "struct D<T, U = Vec<T>>(U);\n" + MAINP)
    # A where-form Adt bound through an alias and a field.
    needw = "struct NeedW<T>(T) where T: Copy;\n"
    for an, aty, _ in ARGS:
        case("alias", f"alias_where_unused_{an}", needw + f"type X = NeedW<{aty}>;\n" + MAINP)
        case("alias", f"alias_where_used_{an}", needw + f"type X = NeedW<{aty}>;\nfn f(_x: X) {{}}\n" + MAINP)
        case("traitconst", f"trait_const_where_{an}", needw + f"trait Tr {{ const C: NeedW<{aty}>; }}\n" + MAINP)
    # C6: never-read const bodies, every owner.
    bad_const = "const BAD: u8 = if true { 1 } else { false };\n"
    ok_const = "const GOOD: u8 = if true { 1 } else { 2 };\n"
    case("constbody", "const_dead_branch", bad_const + MAINP)
    case("constbody", "const_dead_branch_ok", ok_const + MAINP)
    case("constbody", "const_inherent_dead", "struct S;\nimpl S { const BAD: u8 = if true { 1 } else { false }; }\n" + MAINP)
    case("constbody", "const_trait_default_dead", "trait Tr { const BAD: u8 = if true { 1 } else { false }; }\n" + MAINP)
    case("constbody", "const_trait_default_ok", "trait Tr { const GOOD: u8 = if true { 1 } else { 2 }; }\n" + MAINP)
    # C7: never-called trait default bodies.
    case("body", "trait_default_body_bad", "trait Tr { fn f(&self) { let _: String = 1u8.into(); } }\n" + MAINP)
    case("body", "trait_default_body_ok", "trait Tr { fn f(&self) -> u8 { 1u8 } }\n" + MAINP)
    case("body", "trait_default_body_move", "trait Tr<T> { fn f(&self, x: T) { let y = x; let _z = x; let _ = y; } }\n" + MAINP)
    # C8: never-called generic fns.
    case("body", "generic_fn_move_twice", "fn bad<T>(x: T) { let y = x; let z = x; let _ = (y, z); }\n" + MAINP)
    case("body", "generic_fn_copy_ok", "fn good<T: Copy>(x: T) -> (T, T) { (x, x) }\n" + MAINP)
    case("body", "generic_fn_type_err", "fn bad<T>(_x: T) -> u8 { false }\n" + MAINP)
    case("body", "generic_fn_closure_move", "fn bad<T>(x: T) { let f = move || { let _ = &x; }; let _z = x; f(); }\n" + MAINP)
    # C5: unused generic derives (regression witnesses).
    case("derive", "derive_missing_inner", "struct Inner<T>(T);\n#[derive(Debug)]\nstruct Outer<T> { inner: Inner<T> }\n" + MAINP)
    case("derive", "derive_inner_ok", "#[derive(Debug)]\nstruct Inner<T>(T);\n#[derive(Debug)]\nstruct Outer<T> { inner: Inner<T> }\n" + MAINP)
    case("derive", "derive_stronger_inner",
         "use std::fmt;\nstruct Inner<T>(T);\nimpl<T: fmt::Debug + Clone> fmt::Debug for Inner<T> { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, \"I\") } }\n#[derive(Debug)]\nstruct Outer<T> { inner: Inner<T> }\n" + MAINP)
    # C3 family: an impl owes its trait's supertraits at its own args.
    case("implsuper", "super_lifetime_static_only",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl Tag<&'static u8> for S {}\nimpl<'a> NeedT<&'a u8> for S where S: Tag<&'static u8> {}\n" + MAINP)
    case("implsuper", "super_lifetime_no_where",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl Tag<&'static u8> for S {}\nimpl<'a> NeedT<&'a u8> for S {}\n" + MAINP)
    case("implsuper", "super_lifetime_ok",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl<'a> Tag<&'a u8> for S {}\nimpl<'a> NeedT<&'a u8> for S {}\n" + MAINP)
    case("implsuper", "super_lifetime_where_exact",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl<'a> NeedT<&'a u8> for S where S: Tag<&'a u8> {}\n" + MAINP)
    case("implsuper", "super_type_arg_mismatch",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl Tag<u8> for S {}\nimpl NeedT<u16> for S where S: Tag<u8> {}\n" + MAINP)
    case("implsuper", "super_type_arg_ok",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl Tag<u16> for S {}\nimpl NeedT<u16> for S {}\n" + MAINP)
    case("implsuper", "super_generic_where_other",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl<X> NeedT<X> for S where S: Tag<u8> {}\n" + MAINP)
    case("implsuper", "super_generic_where_exact",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl<X> NeedT<X> for S where S: Tag<X> {}\n" + MAINP)
    case("implsuper", "super_nested_chain_bad",
         "trait Tag<A> {}\ntrait Mid<A>: Tag<A> {}\ntrait NeedT<A>: Mid<A> {}\nstruct S;\nimpl Tag<&'static u8> for S {}\nimpl<'a> Mid<&'a u8> for S where S: Tag<&'static u8> {}\nimpl<'a> NeedT<&'a u8> for S {}\n" + MAINP)
    case("implsuper", "super_two_supers_one_bad",
         "trait Tag<A> {}\ntrait Tag2<A> {}\ntrait NeedT<A>: Tag<A> + Tag2<A> {}\nstruct S;\nimpl<'a> Tag<&'a u8> for S {}\nimpl Tag2<&'static u8> for S {}\nimpl<'a> NeedT<&'a u8> for S where S: Tag2<&'static u8> {}\n" + MAINP)
    case("implsuper", "super_static_arg_ok",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl Tag<&'static u8> for S {}\nimpl NeedT<&'static u8> for S {}\n" + MAINP)
    case("implsuper", "super_ref_in_tuple_bad",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl Tag<(&'static u8, u8)> for S {}\nimpl<'a> NeedT<(&'a u8, u8)> for S where S: Tag<(&'static u8, u8)> {}\n" + MAINP)
    case("implsuper", "super_mut_ref_bad",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl Tag<&'static mut u8> for S {}\nimpl<'a> NeedT<&'a mut u8> for S where S: Tag<&'static mut u8> {}\n" + MAINP)
    case("implsuper", "super_slice_ref_bad",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl Tag<&'static [u8]> for S {}\nimpl<'a> NeedT<&'a [u8]> for S where S: Tag<&'static [u8]> {}\n" + MAINP)
    case("implsuper", "super_box_ref_bad",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl Tag<Box<&'static u8>> for S {}\nimpl<'a> NeedT<Box<&'a u8>> for S where S: Tag<Box<&'static u8>> {}\n" + MAINP)
    case("implsuper", "super_second_lifetime_bad",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl<'a> Tag<(&'a u8, &'static u8)> for S {}\nimpl<'a, 'b> NeedT<(&'a u8, &'b u8)> for S where S: Tag<(&'a u8, &'static u8)> {}\n" + MAINP)
    case("implsuper", "super_generic_ref_where_ok",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl<'a, X> NeedT<&'a X> for S where S: Tag<&'a X> {}\n" + MAINP)
    case("implsuper", "super_generic_ref_where_static",
         "trait Tag<A> {}\ntrait NeedT<A>: Tag<A> {}\nstruct S;\nimpl<'a, X> NeedT<&'a X> for S where S: Tag<&'static X> {}\n" + MAINP)
    # Wrapped argument types: validity follows the innermost type.
    wrapped = [("good_opt", "Option<u8>"), ("bad_opt", "Option<String>"), ("good_tup", "(u8, u8)"),
               ("bad_tup", "(String, u8)"), ("good_arr", "[u8; 2]"), ("bad_arr", "[String; 2]")]
    for wn, wt in wrapped:
        case("traitconst", f"trait_const_wrap_{wn}", NEED + f"trait Tr {{ const C: Need<{wt}>; }}\n" + MAINP)
        case("bound", f"supertrait_wrap_{wn}", SUP + f"trait Sub: Sup<{wt}> {{}}\n" + MAINP)
        case("bound", f"fn_bound_wrap_{wn}", SUP + f"fn f<T: Sup<{wt}>>(_x: T) {{}}\n" + MAINP)
        case("bound", f"struct_bound_wrap_{wn}", SUP + f"struct S<T: Sup<{wt}>>(T);\n" + MAINP)
        case("bound", f"assoc_bound_wrap_{wn}", SUP + f"trait Tr {{ type A2: Sup<{wt}>; }}\n" + MAINP)
        case("alias", f"alias_used_wrap_{wn}", NEED + f"type X = Need<{wt}>;\nfn f(_x: X) {{}}\n" + MAINP)
        case("impl", f"impl_trait_arg_wrap_{wn}", SUP + f"struct S;\nimpl Sup<{wt}> for S {{}}\n" + MAINP)
    # A user trait as the required bound, not only Copy.
    needm = "trait Mk {}\nimpl Mk for u8 {}\nstruct NeedM<T: Mk>(T);\n"
    supm = "trait Mk {}\nimpl Mk for u8 {}\ntrait SupM<T: Mk> {}\n"
    for an, aty, _ in ARGS:
        case("traitconst", f"trait_const_mk_{an}", needm + f"trait Tr {{ const C: NeedM<{aty}>; }}\n" + MAINP)
        case("bound", f"supertrait_mk_{an}", supm + f"trait Sub: SupM<{aty}> {{}}\n" + MAINP)
        case("bound", f"fn_bound_mk_{an}", supm + f"fn f<T: SupM<{aty}>>(_x: T) {{}}\n" + MAINP)
        case("alias", f"alias_used_mk_{an}", needm + f"type X = NeedM<{aty}>;\nfn f(_x: X) {{}}\n" + MAINP)
        case("bound", f"fn_bound_clone_{an}", "trait SupC<T: Clone> {}\n" + f"fn f<X: SupC<{aty}>>(_x: X) {{}}\n" + MAINP)
    # The same invalid type in a used position of a valid program shape:
    # partition into a struct used by main through a generic fn.
    for an, aty, aexpr in ARGS:
        case("direct", f"generic_ctor_{an}", NEED + f"fn make<T: Copy>(x: T) -> Need<T> {{ Need(x) }}\nfn main() {{ let _n: Need<{aty}> = make({aexpr}); println!(\"ok\"); }}\n")


def run(cmd, timeout=25, env=None):
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env)
        return r.returncode, r.stdout, r.stderr
    except subprocess.TimeoutExpired:
        return None, "", "timeout"


def one(job):
    family, name, src, keep = job
    d = keep or tempfile.mkdtemp(prefix="defcheck-")
    if keep:
        os.makedirs(d, exist_ok=True)
    path = os.path.join(d, name + ".rs")
    with open(path, "w") as f:
        f.write(src)
    env = dict(os.environ, LUST_NO_DAEMON="1", TMPDIR=d)
    rrc, _, rerr = run(["rustc", "--edition", "2024", "-A", "warnings", path, "-o", os.path.join(d, "rbin")], env=env)
    if rrc is None:
        return (family, name, "rustc-hang", rerr)
    crc, _, cerr = run([LUST, "check", path], env=env)
    if crc is None:
        return (family, name, "hang", "lust check timeout")
    rustc_ok, lust_ok = rrc == 0, crc == 0
    if rustc_ok and lust_ok:
        brc, _, berr = run([LUST, "build", path, "-o", os.path.join(d, "lbin")], env=env)
        if brc is None:
            return (family, name, "hang", "lust build timeout")
        if brc != 0:
            return (family, name, "build-reject", berr[:200])
        orc, oout, _ = run([os.path.join(d, "rbin")], env=env)
        lrc, lout, _ = run([os.path.join(d, "lbin")], env=env)
        if orc is None or lrc is None:
            return (family, name, "hang", "run timeout")
        if (orc, oout) != (lrc, lout):
            return (family, name, "wrong-output", f"rustc=({orc},{oout!r}) lust=({lrc},{lout!r})")
        return (family, name, "ok", "")
    if rustc_ok and not lust_ok:
        return (family, name, "false-reject", cerr.strip().split("\n")[0][:160])
    if not rustc_ok and lust_ok:
        brc, _, _ = run([LUST, "build", path, "-o", os.path.join(d, "lbin")], env=env)
        if brc is None:
            return (family, name, "hang", "lust build timeout (rustc rejects)")
        return (family, name, "false-accept-check" if brc != 0 else "FALSE-ACCEPT", cerr[:120])
    return (family, name, "ok", "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--family", default="")
    ap.add_argument("--keep", default="")
    a = ap.parse_args()
    build_cases()
    jobs = [(f, n, s, os.path.join(a.keep, n) if a.keep else "") for (f, n, s) in CASES if not a.family or f == a.family]
    counts = {}
    bad = []
    with ProcessPoolExecutor(max_workers=a.jobs) as ex:
        for fam, name, cls, info in ex.map(one, jobs):
            counts[cls] = counts.get(cls, 0) + 1
            if cls != "ok":
                bad.append((fam, name, cls, info))
    print(f"defcheck_sweep: {len(jobs)} cases: " + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    for fam, name, cls, info in sorted(bad):
        print(f"  {cls:18s} {fam}/{name} {info}")
    fatal = [b for b in bad if b[2] in ("FALSE-ACCEPT", "false-accept-check", "wrong-output", "hang", "build-reject")]
    return 1 if fatal else 0


if __name__ == "__main__":
    sys.exit(main())
