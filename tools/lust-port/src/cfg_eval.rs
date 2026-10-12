//! Syntactic `#[cfg(...)]` evaluation for one target triple.
//! Values we can get from the triple (os, arch, family, env, vendor,
//! endian, pointer width) are decided. `feature ="..."`, custom cfg flags
//! and `target_feature` are undecidable here and recorded, never guessed.

use syn::punctuated::Punctuated;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Tri {
    True,
    False,
    Unknown,
}

impl Tri {
    pub fn and(self, o: Tri) -> Tri {
        match (self, o) {
            (Tri::False, _) | (_, Tri::False) => Tri::False,
            (Tri::True, Tri::True) => Tri::True,
            _ => Tri::Unknown,
        }
    }
    pub fn or(self, o: Tri) -> Tri {
        match (self, o) {
            (Tri::True, _) | (_, Tri::True) => Tri::True,
            (Tri::False, Tri::False) => Tri::False,
            _ => Tri::Unknown,
        }
    }
    pub fn not(self) -> Tri {
        match self {
            Tri::True => Tri::False,
            Tri::False => Tri::True,
            Tri::Unknown => Tri::Unknown,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Tri::True => "true",
            Tri::False => "false",
            Tri::Unknown => "unknown",
        }
    }
}

#[derive(Debug, Clone)]
pub struct TargetInfo {
    pub triple: String,
    pub arch: Option<String>,
    pub vendor: Option<String>,
    pub os: Option<String>,
    pub env: Option<String>,
    pub families: Vec<String>,
    pub endian: Option<String>,
    pub pointer_width: Option<String>,
}

const OSES: &[&str] = &[
    "linux",
    "macos",
    "darwin",
    "windows",
    "freebsd",
    "netbsd",
    "openbsd",
    "dragonfly",
    "solaris",
    "illumos",
    "haiku",
    "android",
    "ios",
    "tvos",
    "watchos",
    "visionos",
    "emscripten",
    "wasi",
    "wasip1",
    "wasip2",
    "hermit",
    "redox",
    "fuchsia",
    "aix",
    "hurd",
    "espidf",
    "vxworks",
    "nto",
    "uefi",
    "none",
];
const UNIX_OSES: &[&str] = &[
    "linux",
    "macos",
    "darwin",
    "freebsd",
    "netbsd",
    "openbsd",
    "dragonfly",
    "solaris",
    "illumos",
    "haiku",
    "android",
    "ios",
    "tvos",
    "watchos",
    "visionos",
    "emscripten",
    "redox",
    "fuchsia",
    "aix",
    "hurd",
    "vxworks",
    "nto",
];

impl TargetInfo {
    pub fn from_triple(triple: Option<&str>) -> TargetInfo {
        let triple = triple.map(|s| s.to_string()).unwrap_or_else(|| {
            // Host fallback from std consts. Not a real triple, but the
            // fields below are what cfg evaluation reads.
            format!("{}-host-{}", std::env::consts::ARCH, std::env::consts::OS)
        });
        let parts: Vec<&str> = triple.split('-').collect();
        let arch = parts.first().map(|s| s.to_string());
        let os_idx = parts.iter().position(|p| OSES.contains(p));
        let os = os_idx.map(|i| normalize_os(parts[i]));
        let vendor = match os_idx {
            Some(i) if i >= 2 => Some(parts[1].to_string()),
            _ => parts.get(1).filter(|p| !OSES.contains(p)).map(|s| s.to_string()),
        };
        let env = os_idx.and_then(|i| parts.get(i + 1)).map(|s| s.to_string());
        let mut families = Vec::new();
        if let Some(o) = &os {
            if UNIX_OSES.contains(&o.as_str()) {
                families.push("unix".to_string());
            }
            if o == "windows" {
                families.push("windows".to_string());
            }
        }
        if arch.as_deref().is_some_and(|a| a.starts_with("wasm")) {
            families.push("wasm".to_string());
        }
        let endian = match arch.as_deref() {
            Some("s390x") | Some("powerpc") | Some("powerpc64") | Some("sparc64") => Some("big".to_string()),
            Some(_) => Some("little".to_string()),
            None => None,
        };
        let pointer_width = match arch.as_deref() {
            Some("x86_64") | Some("aarch64") | Some("powerpc64") | Some("riscv64") | Some("s390x") | Some("sparc64")
            | Some("loongarch64") | Some("wasm64") => Some("64".to_string()),
            Some("i386") | Some("i586") | Some("i686") | Some("arm") | Some("wasm32") | Some("riscv32") => Some("32".to_string()),
            Some(a) if a.starts_with("arm") => Some("32".to_string()),
            _ => None,
        };
        TargetInfo { triple, arch, vendor, os, env, families, endian, pointer_width }
    }

    fn field(&self, key: &str) -> Option<Tri> {
        Some(match key {
            "unix" => yesno(self.families.iter().any(|f| f == "unix")),
            "windows" => yesno(self.os.as_deref() == Some("windows")),
            _ => return None,
        })
    }
}

fn normalize_os(os: &str) -> String {
    if os == "darwin" { "macos".to_string() } else { os.to_string() }
}
fn yesno(b: bool) -> Tri {
    if b { Tri::True } else { Tri::False }
}
fn cmp(field: &Option<String>, want: &str) -> Tri {
    match field {
        Some(v) => yesno(v == want),
        None => Tri::Unknown,
    }
}

#[derive(Debug, Default, Clone)]
pub struct CfgEval {
    pub state: Tri,
    pub mentions_test: bool,
    pub mentions_target: bool,
    /// Predicate spellings we could not decide, in source form.
    pub undecidable: Vec<String>,
}

impl Default for Tri {
    fn default() -> Self {
        Tri::Unknown
    }
}

/// Evaluates one `#[cfg(...)]` attribute.
pub fn eval_cfg_attr(attr: &syn::Attribute, t: &TargetInfo) -> CfgEval {
    match attr.parse_args::<syn::Meta>() {
        Ok(m) => eval_meta(&m, t),
        Err(_) => CfgEval { state: Tri::Unknown, undecidable: vec![quote::quote!(#attr).to_string()], ..Default::default() },
    }
}

/// Evaluates a cfg string as cargo writes it, e.g. `cfg(not(target_family = "wasm"))`
/// or a bare triple. Used for dependency target fields.
pub fn eval_cfg_str(s: &str, t: &TargetInfo) -> Tri {
    let s = s.trim();
    if let Some(inner) = s.strip_prefix("cfg(").and_then(|x| x.strip_suffix(')')) {
        match syn::parse_str::<syn::Meta>(inner) {
            Ok(m) => eval_meta(&m, t).state,
            Err(_) => Tri::Unknown,
        }
    } else {
        // A plain triple: match only on exact equality.
        yesno(s == t.triple)
    }
}

pub fn eval_meta(m: &syn::Meta, t: &TargetInfo) -> CfgEval {
    let mut out = CfgEval { state: Tri::Unknown, ..Default::default() };
    match m {
        syn::Meta::Path(p) => {
            let name = p.segments.iter().map(|s| s.ident.to_string()).collect::<Vec<_>>().join("::");
            match name.as_str() {
                // Treated as true here: test lowering is a scope label,
                // not a target property. See walk: cfg(test) sets the
                // test-only category on its own.
                "test" => {
                    out.mentions_test = true;
                    out.state = Tri::True;
                }
                "unix" | "windows" => {
                    out.mentions_target = true;
                    out.state = t.field(&name).unwrap_or(Tri::Unknown);
                }
                _ => out.undecidable.push(name),
            }
        }
        syn::Meta::NameValue(nv) => {
            let key = nv.path.segments.iter().map(|s| s.ident.to_string()).collect::<Vec<_>>().join("::");
            let val = match &nv.value {
                syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(s), .. }) => Some(s.value()),
                _ => None,
            };
            if key.starts_with("target_") {
                out.mentions_target = true;
            }
            let Some(val) = val else {
                out.undecidable.push(key);
                return out;
            };
            out.state = match key.as_str() {
                "target_os" => cmp(&t.os, &normalize_os(&val)),
                "target_arch" => cmp(&t.arch, &val),
                "target_vendor" => cmp(&t.vendor, &val),
                "target_env" | "target_abi" => cmp(&t.env, &val),
                "target_family" => {
                    if t.families.is_empty() && t.os.is_none() {
                        Tri::Unknown
                    } else {
                        yesno(t.families.iter().any(|f| f == &val))
                    }
                }
                "target_endian" => cmp(&t.endian, &val),
                "target_pointer_width" => cmp(&t.pointer_width, &val),
                _ => {
                    out.undecidable.push(format!("{key} = \"{val}\""));
                    Tri::Unknown
                }
            };
        }
        syn::Meta::List(l) => {
            let name = l.path.segments.iter().map(|s| s.ident.to_string()).collect::<Vec<_>>().join("::");
            let args = l.parse_args_with(Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated);
            let Ok(args) = args else {
                out.undecidable.push(name);
                return out;
            };
            let subs: Vec<CfgEval> = args.iter().map(|a| eval_meta(a, t)).collect();
            for s in &subs {
                out.mentions_test |= s.mentions_test;
                out.mentions_target |= s.mentions_target;
                out.undecidable.extend(s.undecidable.iter().cloned());
            }
            out.state = match name.as_str() {
                "all" => subs.iter().fold(Tri::True, |a, s| a.and(s.state)),
                "any" => subs.iter().fold(Tri::False, |a, s| a.or(s.state)),
                "not" if subs.len() == 1 => subs[0].state.not(),
                _ => {
                    out.undecidable.push(name);
                    Tri::Unknown
                }
            };
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ev(s: &str, triple: &str) -> CfgEval {
        let t = TargetInfo::from_triple(Some(triple));
        eval_meta(&syn::parse_str::<syn::Meta>(s).unwrap(), &t)
    }

    #[test]
    fn target_fields() {
        let t = TargetInfo::from_triple(Some("x86_64-unknown-linux-gnu"));
        assert_eq!(t.os.as_deref(), Some("linux"));
        assert_eq!(t.arch.as_deref(), Some("x86_64"));
        assert_eq!(t.env.as_deref(), Some("gnu"));
        assert!(t.families.iter().any(|f| f == "unix"));
        let m = TargetInfo::from_triple(Some("aarch64-apple-darwin"));
        assert_eq!(m.os.as_deref(), Some("macos"));
        assert_eq!(m.vendor.as_deref(), Some("apple"));
        let w = TargetInfo::from_triple(Some("wasm32-wasip1"));
        assert!(w.families.iter().any(|f| f == "wasm"));
    }

    #[test]
    fn cfg_decide() {
        assert_eq!(ev(r#"target_os = "linux""#, "x86_64-unknown-linux-gnu").state, Tri::True);
        assert_eq!(ev(r#"target_os = "windows""#, "x86_64-unknown-linux-gnu").state, Tri::False);
        assert_eq!(ev("unix", "x86_64-unknown-linux-gnu").state, Tri::True);
        assert_eq!(ev("windows", "x86_64-pc-windows-msvc").state, Tri::True);
        assert_eq!(ev(r#"all(unix, not(target_os = "macos"))"#, "x86_64-unknown-linux-gnu").state, Tri::True);
        assert_eq!(ev(r#"any(windows, target_os = "macos")"#, "x86_64-unknown-linux-gnu").state, Tri::False);
        assert_eq!(ev(r#"target_family = "wasm""#, "wasm32-wasip1").state, Tri::True);
        let f = ev(r#"feature = "jemalloc""#, "x86_64-unknown-linux-gnu");
        assert_eq!(f.state, Tri::Unknown);
        assert_eq!(f.undecidable, vec![r#"feature = "jemalloc""#.to_string()]);
        let test = ev("test", "x86_64-unknown-linux-gnu");
        assert!(test.mentions_test);
        let tri = TargetInfo::from_triple(Some("x86_64-unknown-linux-gnu"));
        assert_eq!(eval_cfg_str(r#"cfg(not(target_family = "wasm"))"#, &tri), Tri::True);
        assert_eq!(eval_cfg_str(r#"cfg(windows)"#, &tri), Tri::False);
    }
}
