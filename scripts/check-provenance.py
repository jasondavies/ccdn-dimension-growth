#!/usr/bin/env python3
"""Verify vendored provenance and that no mathematical source escapes the root import."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / "vendor" / "bombieri-vaaler"
metadata = json.loads((VENDOR / "upstream.json").read_text())
expected = metadata["files"] | metadata["patched_files"]
actual = {str(p.relative_to(VENDOR)) for p in (VENDOR / "ArithmeticHeights").rglob("*.lean")}
if actual != set(expected):
    raise SystemExit("Vendored file inventory differs from the provenance manifest")
for relative, digest in expected.items():
    if hashlib.sha256((VENDOR / relative).read_bytes()).hexdigest() != digest:
        raise SystemExit(f"Vendored source hash mismatch: {relative}")

MERTENS = ROOT / "vendor" / "mertens"
mertens = json.loads((MERTENS / "upstream.json").read_text())
if {str(p.relative_to(MERTENS)) for p in MERTENS.rglob("*.lean")} != {mertens["path"]}:
    raise SystemExit("Vendored Mertens file inventory differs from the provenance manifest")
mertens_digest = hashlib.sha256((MERTENS / mertens["path"]).read_bytes()).hexdigest()
if mertens_digest != mertens["adapted_sha256"]:
    raise SystemExit("Adapted Mertens source differs from the provenance manifest")

modules = {
    ".".join(p.relative_to(ROOT).with_suffix("").parts): p
    for p in (ROOT / "CCDN").rglob("*.lean")
}
modules["CCDN"] = ROOT / "CCDN.lean"
modules.update({
    ".".join(p.relative_to(VENDOR).with_suffix("").parts): p
    for p in (VENDOR / "ArithmeticHeights").rglob("*.lean")
})
modules[mertens["module"]] = MERTENS / mertens["path"]
seen = set()

def visit(name):
    if name in seen:
        return
    seen.add(name)
    for dep in re.findall(r"^(?:public )?import (?:all )?(\S+)", modules[name].read_text(), re.M):
        if dep in modules:
            visit(dep)
        elif dep.startswith(("CCDN", "ArithmeticHeights", "Mertens")):
            raise SystemExit(f"Missing project dependency: {dep}")

visit("CCDN")
missing = set(modules) - seen
if missing:
    raise SystemExit(f"Mathematical sources omitted from build/audit: {sorted(missing)}")
print(f"Source checks passed: {len(expected) + 1} vendor hashes; {len(seen)} reachable modules.")
