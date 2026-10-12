#!/usr/bin/env python3
# Scale gate harness (docs/ARCH.md section 9.3, "Scale gate, every
# wave"). W-DRIVER runs it at wave A landings. It reports, per edit
# scenario on its own row (cold checks and edits never merge):
# changed bodies rechecked, bodies reused by recorded reads,
# invalidated binding/method-set queries, instances (slots) visited,
# C bytes emitted, dirty units, units compiled by tcc, unit objects
# reused from disk, whether the table unit rebuilt, wall times for
# check and build, link time (from --timings stages), and peak daemon
# memory (RSS). Counters come from the compiler's one-line
# `lust-stats:` output (LUST_STATS=1), not from this script's guesses.
#
# Wave A scenarios only (ARCH 9.3): fresh cold, cached cold after a
# daemon restart (slot manifest plus disk objects), a new pub fn in
# single-file form, a type edit that changes a layout, a derive edit
# (a macro edit that adds a generated item), and the restart row. The
# inherent-method, cross-crate generic, and added-generic-instance
# scenarios need the MGP and join later; listing them as run here
# would be wrong.
#
# The ts-rust slice is pinned and grows per wave. Wave A slice: the
# three owned kernel amalgams under tests/kernels/*-amalgam (real
# ts-rust code, single-file form), host target, no features. Lust
# cannot build them yet, so the slice rows report the rustc check
# time, the lust check time, and lust's first diagnostic instead of
# edit counters.
#
# Usage: python3 scripts/scale-gate.py [--modules 40] [--json out.json] [--multi]
# --multi measures the same crate split into one module file per
# warehouse copy (bench/realish/make_multi.py, the resolver path)
# with per-edit scenarios: body edit, new fn, signature edit, type
# edit, import edit, new file. Run both forms to compare against
# the single-file path.
# Line count reported is physical source lines of the generated crate.
import json, os, signal, subprocess, sys, tempfile, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LUST = os.path.join(ROOT, "target/release/lust")
MODULES = 40
JSON_OUT = None
MULTI = False
args = sys.argv[1:]
while args:
    a = args.pop(0)
    if a == "--modules":
        MODULES = int(args.pop(0))
    elif a == "--json":
        JSON_OUT = args.pop(0)
    elif a == "--multi":
        MULTI = True
    else:
        sys.exit(f"unknown argument: {a}")


def parse_stats(stderr):
    out = {}
    for line in stderr.splitlines():
        if line.startswith("lust-stats:"):
            for kv in line.split(":", 1)[1].split():
                k, _, v = kv.partition("=")
                out[k] = int(v) if v.isdigit() else v
    return out


def link_ms(stderr):
    total = 0.0
    for line in stderr.splitlines():
        parts = line.rsplit(None, 2)
        if len(parts) == 3 and parts[2] == "ms" and parts[0].strip().startswith("link"):
            try:
                total += float(parts[1])
            except ValueError:
                pass
    return total


def print_rows(rows, rss, lines, work, label):
    print(f"scale gate ({label}): {MODULES} warehouse modules, {lines} physical lines, work dir {work}")
    print(f"daemon memory after cold build: RSS {rss} kB")
    print()
    hdr = ("scenario", "check", "build", "link", "bodies", "reused", "inval", "inst", "C KB", "dirtyU", "tccU", "diskU", "tbl")
    print(" ".join(f"{h:>7}" if i else f"{h:<46}" for i, h in enumerate(hdr)))
    for r in rows:
        print(f"{r['scenario']:<46} {r['check_ms']:>6.0f} {r['build_ms']:>6.0f} {r['link_ms']:>6.0f} "
              f"{r['changed_bodies']:>7} {r['reused_bodies']:>7} {r['invalidated_queries']:>7} {r['instances']:>7} "
              f"{(r['c_bytes'] or 0) // 1024:>7} {r['dirty_units']:>7} {r['units_compiled']:>7} {r['units_from_disk']:>7} {r['table_rebuilt']:>7}"
              f"  [{r['mode']}] {r['checksum']}")


def main():
    if MULTI:
        return main_multi()
    if not os.path.exists(LUST):
        sys.exit(f"{LUST} not built; run cargo build --release first")
    work = tempfile.mkdtemp(prefix="lust-scale-")
    crate = os.path.join(work, "crate.rs")
    with open(crate, "w") as f:
        subprocess.run([sys.executable, os.path.join(ROOT, "bench/realish/make.py"), str(MODULES)],
                       stdout=f, check=True)
    lines = sum(1 for _ in open(crate))
    env = dict(os.environ, LUST_DAEMON_SOCKET=os.path.join(work, "s.sock"),
               LUST_CACHE_DIR=os.path.join(work, "cache"), LUST_STATS="1",
               LUST_DAEMON_IDLE="120s")
    prog = os.path.join(work, "prog")
    rows = []

    def run(cmd):
        start = time.perf_counter()
        r = subprocess.run(cmd, cwd=work, env=env, capture_output=True, text=True)
        return (time.perf_counter() - start) * 1000, r

    def build_row(name, row_env=None):
        # Front-end counters come from the check (it processes the edit
        # first); unit counters come from the build. Each session row is
        # one edit state, never a merge of two scenario kinds.
        ct, cr = run([LUST, "check", "--timings", crate]) if row_env is None else run_env([LUST, "check", "--timings", crate], row_env)
        bt, br = run([LUST, "build", "--timings", crate, "-o", prog]) if row_env is None else run_env([LUST, "build", "--timings", crate, "-o", prog], row_env)
        assert cr.returncode == 0, f"{name}: check failed\n{cr.stderr[-800:]}"
        assert br.returncode == 0, f"{name}: build failed\n{br.stderr[-800:]}"
        run_r = subprocess.run([prog], capture_output=True, text=True)
        assert run_r.returncode == 0, f"{name}: program failed"
        front, back = parse_stats(cr.stderr), parse_stats(br.stderr)
        row = {
            "scenario": name,
            "check_ms": round(ct, 1), "build_ms": round(bt, 1),
            "link_ms": round(link_ms(br.stderr), 1),
            "changed_bodies": front.get("rechecked"), "reused_bodies": front.get("reused"),
            "invalidated_queries": front.get("invalidated"), "instances": back.get("instances"),
            "c_bytes": back.get("c_bytes"), "dirty_units": back.get("dirty_units"),
            "units_compiled": back.get("units_compiled"), "units_from_disk": back.get("unit_cache_hits"),
            "table_rebuilt": back.get("table_rebuilt"), "mode": front.get("mode"),
            "checksum": run_r.stdout.strip().splitlines()[-1] if run_r.stdout.strip() else "",
        }
        rows.append(row)
        return row

    def run_env(cmd, use_env):
        start = time.perf_counter()
        r = subprocess.run(cmd, cwd=work, env=use_env, capture_output=True, text=True)
        return (time.perf_counter() - start) * 1000, r

    def apply(module, old, new):
        src = open(crate).read()
        marker = f"// ==================== module {module} ===================="
        start = src.index(marker)
        end = src.find("// ==================== module ", start + len(marker))
        end = len(src) if end < 0 else end
        section = src[start:end]
        old, new = old.replace("{m}", str(module)), new.replace("{m}", str(module))
        assert old in section, f"edit not found in module {module}: {old!r}"
        open(crate, "w").write(src[:start] + section.replace(old, new, 1) + src[end:])

    daemon = None

    def start_daemon():
        # An explicit daemon (not client autostart): every request below
        # is daemon-served, so the whole-request cold cache in the client
        # never answers a row that claims to measure the daemon.
        nonlocal daemon
        daemon = subprocess.Popen([LUST, "daemon"], cwd=work, env=env,
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        for _ in range(200):
            if os.path.exists(os.path.join(work, "s.sock")):
                return
            time.sleep(0.05)
        sys.exit("daemon did not start")

    def daemon_rss_kb():
        if not daemon:
            return None
        try:
            for line in open(f"/proc/{daemon.pid}/status"):
                if line.startswith("VmRSS:"):
                    return int(line.split()[1])
        except OSError:
            return None

    def kill_daemon():
        nonlocal daemon
        if daemon:
            daemon.kill()
            daemon.wait()
            daemon = None
        for f in ("s.sock", "s.sock.lock"):
            try:
                os.remove(os.path.join(work, f))
            except FileNotFoundError:
                pass

    print(f"scale gate: 31k crate = {MODULES} warehouse modules, {lines} physical lines, work dir {work}")
    cold_env = dict(env, LUST_NO_DAEMON="1", LUST_CACHE_DIR=os.path.join(work, "cold-cache"))
    build_row("fresh cold (one-shot, empty caches)", row_env=cold_env)
    start_daemon()
    build_row("fresh cold (new daemon session)")
    build_row("warm no-op (daemon)")
    rss = daemon_rss_kb()

    apply(21, "fn validate_m{m}(order: &Order_m{m}) -> Option<OrderError_m{m}> {",
          "fn qty_ok_m{m}(q: i64) -> bool {\n    q > 0 && q <= 50\n}\n\nfn validate_m{m}(order: &Order_m{m}) -> Option<OrderError_m{m}> {")
    build_row("new pub fn (single-file form)")

    # Field order swap: offsets move, every literal still names its
    # fields, so the crate still builds. This is the layout (niche
    # class) edit the wave A list names.
    apply(7, "    price_cents: i64,\n    weight_grams: i64,", "    weight_grams: i64,\n    price_cents: i64,")
    build_row("type edit that changes a layout (field offsets)")

    apply(9, "#[derive(Debug)]\nstruct Inventory_m{m} {", "#[derive(Debug, Clone)]\nstruct Inventory_m{m} {")
    build_row("derive edit (macro-generated item added)")

    kill_daemon()
    start_daemon()
    build_row("cached cold after restart (manifest + disk objects)")
    build_row("restart warm no-op")

    # ---- ts-rust slice (pinned; see the header) ----
    slice_rows = []
    for k in ("gostring-amalgam", "json-amalgam", "scanner-amalgam"):
        entry = os.path.join(ROOT, "tests/kernels", k, "src/main.rs")
        n = sum(1 for _ in open(entry))
        rt, rr = run(["rustc", "--edition", "2024", "-C", "panic=abort", "-C", "overflow-checks=on",
                      "-A", "warnings", "--emit=metadata", "-o", os.path.join(work, "slice.rmeta"), entry])
        lt, lr = run([LUST, "check", entry])
        first = next((l for l in lr.stderr.splitlines() if l.startswith("error")), "")
        slice_rows.append({"slice": k, "lines": n, "rustc_check_ms": round(rt, 1),
                           "rustc_ok": rr.returncode == 0, "lust_check_ms": round(lt, 1),
                           "lust_ok": lr.returncode == 0, "lust_first_error": first[:110]})

    print(f"daemon memory after cold build: RSS {rss} kB")
    print()
    hdr = ("scenario", "check", "build", "link", "bodies", "reused", "inval", "inst", "C KB", "dirtyU", "tccU", "diskU", "tbl")
    print(" ".join(f"{h:>7}" if i else f"{h:<46}" for i, h in enumerate(hdr)))
    for r in rows:
        print(f"{r['scenario']:<46} {r['check_ms']:>6.0f} {r['build_ms']:>6.0f} {r['link_ms']:>6.0f} "
              f"{r['changed_bodies']:>7} {r['reused_bodies']:>7} {r['invalidated_queries']:>7} {r['instances']:>7} "
              f"{(r['c_bytes'] or 0) // 1024:>7} {r['dirty_units']:>7} {r['units_compiled']:>7} {r['units_from_disk']:>7} {r['table_rebuilt']:>7}"
              f"  [{r['mode']}] {r['checksum']}")
    print()
    print("ts-rust slice (pinned: tests/kernels/*-amalgam entries, host target, no features):")
    for s in slice_rows:
        print(f"  {s['slice']:<18} {s['lines']:>6} lines  rustc check {s['rustc_check_ms']:>8.0f} ms ok={s['rustc_ok']}  "
              f"lust check {s['lust_check_ms']:>6.0f} ms ok={s['lust_ok']}  {s['lust_first_error']}")
    if JSON_OUT:
        with open(JSON_OUT, "w") as f:
            json.dump({"crate_lines": lines, "modules": MODULES, "daemon_rss_kb": rss,
                       "rows": rows, "ts_slice": slice_rows}, f, indent=1)
        print(f"json: {JSON_OUT}")
    kill_daemon()



def main_multi():
    if not os.path.exists(LUST):
        sys.exit(f"{LUST} not built; run cargo build --release first")
    work = tempfile.mkdtemp(prefix="lust-scale-multi-")
    crate_dir = os.path.join(work, "crate")
    subprocess.run([sys.executable, os.path.join(ROOT, "bench/realish/make_multi.py"), str(MODULES), crate_dir], check=True)
    crate = os.path.join(crate_dir, "main.rs")
    lines = sum(1 for f in os.listdir(crate_dir) if f.endswith(".rs") for _ in open(os.path.join(crate_dir, f)))
    env = dict(os.environ, LUST_DAEMON_SOCKET=os.path.join(work, "s.sock"),
               LUST_CACHE_DIR=os.path.join(work, "cache"), LUST_STATS="1",
               LUST_DAEMON_IDLE="120s")
    prog = os.path.join(work, "prog")
    rows = []

    def run(cmd, use_env=None):
        start = time.perf_counter()
        r = subprocess.run(cmd, cwd=work, env=use_env or env, capture_output=True, text=True)
        return (time.perf_counter() - start) * 1000, r

    def build_row(name, row_env=None):
        ct, cr = run([LUST, "check", "--timings", crate], row_env)
        bt, br = run([LUST, "build", "--timings", crate, "-o", prog], row_env)
        assert cr.returncode == 0, f"{name}: check failed\n{cr.stderr[-800:]}"
        assert br.returncode == 0, f"{name}: build failed\n{br.stderr[-800:]}"
        run_r = subprocess.run([prog], capture_output=True, text=True)
        assert run_r.returncode == 0, f"{name}: program failed"
        front, back = parse_stats(cr.stderr), parse_stats(br.stderr)
        row = {
            "scenario": name,
            "check_ms": round(ct, 1), "build_ms": round(bt, 1),
            "link_ms": round(link_ms(br.stderr), 1),
            "changed_bodies": front.get("rechecked"), "reused_bodies": front.get("reused"),
            "invalidated_queries": front.get("invalidated"), "instances": back.get("instances"),
            "c_bytes": back.get("c_bytes"), "dirty_units": back.get("dirty_units"),
            "units_compiled": back.get("units_compiled"), "units_from_disk": back.get("unit_cache_hits"),
            "table_rebuilt": back.get("table_rebuilt"), "mode": front.get("mode"),
            "reemitted": back.get("reemitted"),
            "checksum": run_r.stdout.strip().splitlines()[-1] if run_r.stdout.strip() else "",
        }
        rows.append(row)
        return row

    def edit(rel, old, new):
        path = os.path.join(crate_dir, rel)
        text = open(path).read()
        assert old in text, f"edit not found in {rel}: {old!r}"
        open(path, "w").write(text.replace(old, new, 1))

    daemon = None

    def start_daemon():
        nonlocal daemon
        daemon = subprocess.Popen([LUST, "daemon"], cwd=work, env=env,
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        for _ in range(200):
            if os.path.exists(os.path.join(work, "s.sock")):
                return
            time.sleep(0.05)
        sys.exit("daemon did not start")

    def daemon_rss_kb():
        if not daemon:
            return None
        try:
            for line in open(f"/proc/{daemon.pid}/status"):
                if line.startswith("VmRSS:"):
                    return int(line.split()[1])
        except OSError:
            return None

    def kill_daemon():
        nonlocal daemon
        if daemon:
            daemon.kill()
            daemon.wait()
            daemon = None
        for f in ("s.sock", "s.sock.lock"):
            try:
                os.remove(os.path.join(work, f))
            except FileNotFoundError:
                pass

    cold_env = dict(env, LUST_NO_DAEMON="1", LUST_CACHE_DIR=os.path.join(work, "cold-cache"))
    build_row("fresh cold (one-shot, empty caches)", row_env=cold_env)
    start_daemon()
    build_row("fresh cold (new daemon session)")
    build_row("warm no-op (daemon)")
    rss = daemon_rss_kb()

    edit("m21.rs", "if qty >= 10 { subtotal / 20 } else { 0 }", "if qty >= 8 { subtotal / 25 } else { 0 }")
    build_row("body edit (one file)")
    edit("m21.rs", "if qty >= 8 { subtotal / 25 } else { 0 }", "if qty >= 10 { subtotal / 20 } else { 0 }")
    build_row("body edit back (disk unit reuse)")

    edit("m21.rs", "fn validate_m21(order: &Order_m21) -> Option<OrderError_m21> {",
         "fn qty_ok_m21(q: i64) -> bool {\n    q > 0 && q <= 50\n}\n\nfn validate_m21(order: &Order_m21) -> Option<OrderError_m21> {")
    build_row("new fn (one file)")

    edit("m11.rs", "fn validate_m11(order: &Order_m11)", "pub fn validate_m11(order: &Order_m11)")
    build_row("signature edit (visibility flip)")

    edit("m7.rs", "    price_cents: i64,\n    weight_grams: i64,", "    weight_grams: i64,\n    price_cents: i64,")
    build_row("type edit that changes a layout (field offsets)")

    edit("main.rs", "use crate::m3::run_module_m3 as run3;", "use crate::m4::run_module_m4 as run3;")
    build_row("import edit (alias retarget, output must move)")

    # New file: one more warehouse copy as m40 plus its mod line and call.
    subprocess.run([sys.executable, os.path.join(ROOT, "bench/realish/make_multi.py"), str(MODULES + 1), os.path.join(work, "gen41")], check=True)
    import shutil
    shutil.copy(os.path.join(work, "gen41", f"m{MODULES}.rs"), os.path.join(crate_dir, f"m{MODULES}.rs"))
    edit("main.rs", f"mod m{MODULES - 1};", f"mod m{MODULES - 1};\nmod m{MODULES};")
    edit("main.rs", "    println!", f"    total += crate::m{MODULES}::run_module_m{MODULES}();\n    println!")
    build_row("new file (module 41)")

    kill_daemon()
    start_daemon()
    build_row("cached cold after restart (manifest + disk objects)")
    build_row("restart warm no-op")

    print_rows(rows, rss, lines, work, "multi-file resolver path")
    if JSON_OUT:
        with open(JSON_OUT, "w") as f:
            json.dump({"crate_lines": lines, "modules": MODULES, "daemon_rss_kb": rss, "multi": True, "rows": rows}, f, indent=1)
        print(f"json: {JSON_OUT}")
    kill_daemon()


if __name__ == "__main__":
    main()
