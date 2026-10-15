#!/usr/bin/env python3
# Unit tests for the --check comparison in scripts/port-scan-sync.py:
# a committed status must equal the status the probes derive, a
# supported feature must sit at milestone 0 (what --write sets), a
# probe id with no table row fails, and unprobed or manual features
# are reported as unchecked instead of passing silently.
# Usage: python3 scripts/test-port-scan-sync.py   (exit 0 = pass)
import importlib.util
import os

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("port_scan_sync", os.path.join(HERE, "port-scan-sync.py"))
pss = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pss)

failures = []


def check(name, cond, detail=""):
    print(f"{'ok' if cond else 'FAIL'} {name}" + (f": {detail}" if detail and not cond else ""))
    if not cond:
        failures.append(name)


def feat(fid, status, milestone=0):
    return {"id": fid, "status": status, "milestone": milestone}


def probe(fid, verdict, file="p.rs"):
    return {"file": file, "feature": fid, "verdict": verdict}


# feature_status: the three derived statuses, plus manual.
check("all pass is supported", pss.feature_status([probe("a", "pass")]) == "supported")
check("some pass is partial", pss.feature_status([probe("a", "pass"), probe("a", "reject")]) == "partial")
check("no pass is unsupported", pss.feature_status([probe("a", "reject"), probe("a", "runfail")]) == "unsupported")
check("lust-only accept is manual", pss.feature_status([probe("a", "lust-only-accept")]) == "manual")

features = [
    feat("ok.supported", "supported", 0),
    feat("stale.partial", "partial", 5),       # probes now say supported (the ext.memchr case)
    feat("stale.milestone", "supported", 5),  # status right, milestone not what --write sets
    feat("ok.unsupported", "unsupported", 7),
    feat("no.probe", "unsupported", 7),
    feat("needs.human", "unsupported", None),
    feat("bad.probe", "partial", 5),
]
by_feature = {
    "ok.supported": [probe("ok.supported", "pass")],
    "stale.partial": [probe("stale.partial", "pass"), probe("stale.partial", "pass", "q.rs")],
    "stale.milestone": [probe("stale.milestone", "pass")],
    "ok.unsupported": [probe("ok.unsupported", "reject")],
    "needs.human": [probe("needs.human", "lust-only-accept")],
    "bad.probe": [probe("bad.probe", "pass"), probe("bad.probe", "wrong", "w.rs")],
    "not.in.table": [probe("not.in.table", "pass")],
}
derived = {fid: pss.feature_status(rs) for fid, rs in by_feature.items()}
res = pss.check_features(features, derived, by_feature)
failed_ids = [fid for fid, _msg in res["failed"]]
unchecked_ids = [fid for fid, _why in res["unchecked"]]

check("matching features pass", res["passed"] == ["ok.supported", "ok.unsupported"], str(res))
check("stale status fails", "stale.partial" in failed_ids, str(res))
check(
    "stale status message names both statuses",
    any(fid == "stale.partial" and "partial" in msg and "supported" in msg for fid, msg in res["failed"]),
    str(res["failed"]),
)
check("stale milestone fails", "stale.milestone" in failed_ids, str(res))
check("wrong-output probe fails its feature", "bad.probe" in failed_ids, str(res))
check("probe id not in table fails", "not.in.table" in failed_ids, str(res))
check("unprobed feature is unchecked, not passed", "no.probe" in unchecked_ids and "no.probe" not in res["passed"], str(res))
check("manual feature is unchecked, not failed", "needs.human" in unchecked_ids and "needs.human" not in failed_ids, str(res))

print(f"test-port-scan-sync: {'FAILED ' + repr(failures) if failures else 'all passed'}")
raise SystemExit(1 if failures else 0)
