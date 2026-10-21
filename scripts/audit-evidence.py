#!/usr/bin/env python3
"""Validate docs/completion-audit.json: its schema, and that every evidence declaration exists.

The schema (keys, status enums, cross-references) is described in docs/audit-schema.md and
encoded in scripts/audit_schema.py. Each evidence entry names a Lean declaration and the file
that declares it; the declaration must be found, fully qualified, in that file. Evidence in the
pinned Mathlib checkout (.lake/packages/mathlib) is checked when that package has been fetched,
and the recorded Mathlib and Mertens revisions must match lake-manifest.json and
vendor/mertens/upstream.json. All problems are reported before exiting.
"""
import argparse
import json
import sys
from pathlib import Path

import audit_schema
from common import ROOT, declarations

MATHLIB = ROOT / ".lake" / "packages" / "mathlib"


def check_revisions(audit: dict, problems: list[str]) -> None:
    revisions = audit.get("dependency_revisions", {})
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    if revisions.get("mathlib") != mathlib:
        problems.append(f"dependency_revisions.mathlib {revisions.get('mathlib')} differs from "
                        f"lake-manifest.json ({mathlib})")
    mertens = json.loads((ROOT / "vendor/mertens/upstream.json").read_text(encoding="utf-8"))
    expected = (mertens["repository"].removeprefix("https://github.com/") + "@"
                + mertens["revision"])
    if revisions.get("mertens_adaptation") != expected:
        problems.append(f"dependency_revisions.mertens_adaptation differs from "
                        f"vendor/mertens/upstream.json ({expected})")


def main() -> int:
    argparse.ArgumentParser(description=__doc__.splitlines()[0]).parse_args()
    audit = audit_schema.load()
    problems = audit_schema.validate(audit)
    check_revisions(audit, problems)

    cache: dict[Path, dict[str, int]] = {}
    skipped = []
    for entry in audit.get("evidence", []):
        if not {"id", "file", "declaration"} <= entry.keys():
            continue  # already reported by the schema check
        path = ROOT / entry["file"]
        if path.is_relative_to(MATHLIB) and not MATHLIB.is_dir():
            skipped.append(entry["id"])
            continue
        if not path.is_file():
            problems.append(f"{entry['id']}: file {entry['file']} does not exist")
            continue
        if path not in cache:
            cache[path] = declarations(path)
        if entry["declaration"] not in cache[path]:
            problems.append(f"{entry['id']}: {entry['declaration']} is not declared in "
                            f"{entry['file']} (if it was renamed or moved, edit the entry)")

    if problems:
        print("Completion audit check failed:")
        print("\n".join(f"  {problem}" for problem in problems))
        return 1
    checked = len(audit["evidence"]) - len(skipped)
    print(f"Completion audit: schema valid; {checked} evidence declarations found in their files.")
    if skipped:
        print(f"  Skipped {', '.join(skipped)}: Mathlib is not fetched under .lake/packages "
              "(run `lake exe cache get` or `lake build` first).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
