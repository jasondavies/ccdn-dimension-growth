#!/usr/bin/env python3
"""Check that facts repeated across the repository's files agree.

* The compared theorems: `theorem_names` in comparator.json, the `lean` names of the
  `alignment` in formalization.yaml, the `#print axioms CCDN.Submission.*` lines of Axioms.lean,
  the theorems of Challenge.lean, the theorems proved in Solution.lean, and the theorem table of
  README.md.
* The toolchain and Mathlib revision quoted in README.md, against lean-toolchain, lakefile.toml
  and lake-manifest.json.
* The discrepancy table of README.md, against the statuses and `in_addenda` flags of
  docs/completion-audit.json, and the numbers of audited statements and external inputs quoted
  in README.md and formalization.yaml.

All problems are reported before exiting.
"""
import argparse
import json
import re
import sys

import audit_schema
from common import ROOT, declarations, lakefile

NAMESPACE = "CCDN.Submission."


def compared_theorems(problems: list[str]) -> int:
    comparator = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    expected = set(comparator["theorem_names"])
    yaml_text = (ROOT / "formalization.yaml").read_text(encoding="utf-8")
    sources = {
        "formalization.yaml alignment": set(re.findall(r'^\s*lean:\s*"([^"]+)"', yaml_text, re.M)),
        "Axioms.lean #print axioms": set(re.findall(
            r"^#print axioms (CCDN\.Submission\.\S+)",
            (ROOT / "Axioms.lean").read_text(encoding="utf-8"), re.M)),
    }
    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    theorem_names = set(re.findall(r"^theorem (\S+)", challenge, re.M))
    sources["Challenge.lean theorems"] = {NAMESPACE + name for name in theorem_names}
    for name, found in sources.items():
        for missing in sorted(expected - found):
            problems.append(f"{name}: missing compared theorem {missing}")
        for extra in sorted(found - expected):
            problems.append(f"{name}: {extra} is not in comparator.json")
    solution = set(declarations(ROOT / "Solution.lean"))
    for missing in sorted(expected - solution):
        problems.append(f"Solution.lean: does not prove {missing}")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    for name in sorted(expected):
        if f"`{name.removeprefix(NAMESPACE)}`" not in readme:
            problems.append(f"README.md: compared theorem {name} is not listed")
    return len(expected)


def versions(problems: list[str]) -> None:
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    version = toolchain.split(":", 1)[1]
    quoted = re.findall(r"toolchain is Lean `([^`]+)`", readme)
    if quoted != [version]:
        problems.append(f"README.md quotes Lean {quoted}, lean-toolchain has {version}")
    required = next(r["rev"] for r in lakefile()["require"] if r["name"] == "mathlib")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    locked = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    if required != locked:
        problems.append(f"lakefile.toml requires Mathlib {required}, lake-manifest.json has "
                        f"{locked}")
    quoted = re.findall(r"Mathlib is pinned to\s+`([0-9a-f]+)`", readme)
    if quoted != [locked]:
        problems.append(f"README.md quotes Mathlib {quoted}, lake-manifest.json has {locked}")


def discrepancies(problems: list[str]) -> int:
    audit = audit_schema.load()
    expected = {r["source_label"]: r for r in audit["requirements"]
                if r["statement_status"] in audit_schema.DISCREPANCIES}
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    section = readme.split("## Discrepancies with the paper", 1)[-1].split("\n## ", 1)[0]
    rows = {}
    for line in section.splitlines():
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) == 5 and audit_schema.LABEL.fullmatch(cells[0]):
            rows[cells[0]] = cells
    for label in sorted(expected.keys() - rows.keys()):
        problems.append(f"README.md discrepancy table: missing {label} "
                        f"({expected[label]['statement_status']} in the audit)")
    for label in sorted(rows.keys() - expected.keys()):
        problems.append(f"README.md discrepancy table: {label} is not a discrepancy in the audit")
    for label in sorted(rows.keys() & expected.keys()):
        _, _, addenda, _, status = rows[label]
        requirement = expected[label]
        if status != requirement["statement_status"]:
            problems.append(f"README.md discrepancy table: {label} is '{status}', the audit says "
                            f"'{requirement['statement_status']}'")
        if addenda.split()[0] != ("yes" if requirement["in_addenda"] else "no"):
            problems.append(f"README.md discrepancy table: {label} 'In addenda' is '{addenda}', "
                            f"the audit says {requirement['in_addenda']}")

    counts = {"statements": len(audit["requirements"]),
              "externals": len(audit["external_dependencies"])}
    patterns = {"statements": [r"(\d+)\s+audited\s+(?:statements|requirements)",
                               r"all\s+(\d+)\s+requirements"],
                "externals": [r"lists all\s+(\d+)\s+with their Lean"]}
    for document in ("README.md", "formalization.yaml"):
        text = (ROOT / document).read_text(encoding="utf-8")
        for kind, regexes in patterns.items():
            for regex in regexes:
                for number in re.findall(regex, text):
                    if int(number) != counts[kind]:
                        problems.append(f"{document}: quotes {number} {kind}, the audit has "
                                        f"{counts[kind]}")
    return len(expected)


def main() -> int:
    argparse.ArgumentParser(description=__doc__.splitlines()[0]).parse_args()
    problems: list[str] = []
    theorems = compared_theorems(problems)
    versions(problems)
    rows = discrepancies(problems)
    if problems:
        print("Consistency check failed:")
        print("\n".join(f"  {problem}" for problem in problems))
        return 1
    print(f"Consistency: {theorems} compared theorems, the toolchain and Mathlib pins, and "
          f"{rows} discrepancies agree across the repository.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
