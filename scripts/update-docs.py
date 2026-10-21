#!/usr/bin/env python3
"""Generate docs/modules.md and docs/statements.md from the sources and the completion audit.

docs/modules.md lists every module of the two libraries by directory, with the first sentence of
its module docstring. docs/statements.md tabulates the audited statements of the paper and the external
inputs recorded in docs/completion-audit.json, linking each Lean declaration to the line that
declares it. `--check` fails when either file is out of date; line anchors that have merely
drifted are reported but do not fail the check, so editing a Lean file never breaks CI by itself.
"""
import argparse
import re
import sys
from pathlib import Path

import audit_schema
from common import FOUNDATION, MAIN, PAPER, ROOT, SIDE_RESULT, declarations, \
    library_module_paths, module_name

MODULES = ROOT / "docs" / "modules.md"
STATEMENTS = ROOT / "docs" / "statements.md"
ANCHOR = re.compile(r"#L\d+\)")

# Every directory holding modules, relative to the repository root, with its description.
DIRECTORIES = {
    "CCDN": "Main results, with their statements and one endpoint module per result",
    "CCDN/Algebra": "Polynomial and commutative-algebra lemmas",
    "CCDN/Analysis": "Real and prime-number estimates",
    "CCDN/AuxiliaryPolynomial": "Auxiliary polynomials, positioning and bad primes (Sections 3.1, "
                                "3.3, 3.4, 4.2)",
    "CCDN/ClassGroup": "Two-torsion in class groups (Theorem 6)",
    "CCDN/Curve": "Curve counts (Theorems 2 and 3, and the curve case of Theorem 1)",
    "CCDN/Determinant": "Local and global determinant estimates (Sections 2 and 3.2)",
    "CCDN/ForMathlib": "General results suitable for Mathlib",
    "CCDN/Height": "Heights, boxes and point counts",
    "CCDN/Hilbert": "Hilbert functions, dimension and degree",
    "CCDN/Hypersurface": "Hyperplane slicing and hypersurface counts (Sections 4.1, 4.3)",
    "CCDN/LowerBound": "Lower-bound constructions (Proposition 5, Section 6)",
    "CCDN/Noether": "Noether irreducibility forms (Theorem 3.2.2)",
    "CCDN/Plane": "Plane curves, including the scaled plane model",
    "CCDN/Projection": "Projections and bounded linear Noether normalisation (the projection steps "
                       "of Theorems 1–3)",
    "CCDN/Surface": "Surfaces (Propositions 4.3.3, 4.3.4, Theorem 4.3.5)",
    "CCDNPaper/Algebra": "Polynomial and commutative-algebra lemmas used only by the paper "
                         "library",
    "CCDNPaper/Analysis": "Numerical lemmas for the sharpness statements of Section 6",
    "CCDNPaper/AuxiliaryPolynomial": "Auxiliary polynomials with the literal affine bad-prime "
                                     "factor (Proposition 4.2.1) and positioned estimates "
                                     "(Lemmas 3.3.2, 3.3.3)",
    "CCDNPaper/Center": "Chow forms, good centres and Plücker equations (Section 5); entry point "
                        "`BirationalComplementProjection`",
    "CCDNPaper/Curve": "Affine curve degree and the filtered Hilbert polynomial",
    "CCDNPaper/Determinant": "Local determinant lemmas in the paper's generality (Lemmas 2.1, 2.2, "
                             "2.4)",
    "CCDNPaper/ForMathlib": "General results suitable for Mathlib, used only by the paper library",
    "CCDNPaper/Hilbert": "Hilbert polynomials under coefficient extension, coordinate change and "
                         "projective closure",
    "CCDNPaper/Hypersurface": "Grid bounds and varieties not defined over ℚ (Section 4.1), and "
                              "hyperplane sections (Lemma 4.3.7)",
    "CCDNPaper/LowerBound": "Grid constructions for the lower bounds of Section 6",
    "CCDNPaper/Plane": "Coprime Newton edges (Corollary 4.2.5)",
    "CCDNPaper/Projection": "Affine projections (Proposition 4.3.1)",
    "CCDNPaper/Surface": "Salberger's surface cover as stated (Theorem 4.3.5)",
    "CCDNPaper/Counterexample": "Counterexamples to printed intermediate statements",
    "CCDNPaper/Statements": "The paper's intermediate statements and side results as stated "
                            "there, not used by the main results",
}


def first_sentence(path: Path) -> str:
    match = re.search(r"/-!(.*?)-/", path.read_text(encoding="utf-8"), re.S)
    if match is None:
        return ""
    text = " ".join(line.strip() for line in match.group(1).splitlines()
                    if line.strip() and not line.strip().startswith("#"))
    sentence = re.split(r"(?<=[.!?])\s", text, maxsplit=1)[0]
    return sentence.replace("|", "\\|")


def render_modules() -> str:
    groups: dict[str, list[Path]] = {}
    for path in library_module_paths():
        groups.setdefault(path.parent.relative_to(ROOT).as_posix(), []).append(path)
    unknown = sorted(set(groups) - set(DIRECTORIES))
    if unknown:
        raise SystemExit(f"Describe these directories in scripts/update-docs.py: {unknown}")

    def tier(name: str) -> tuple[int, int]:
        library, _, rest = name.partition("/")
        top = rest.split("/")[0]
        base = 3 if library == PAPER else 0
        if top in SIDE_RESULT and library == PAPER:
            return (6, 0)
        if rest == "":
            return (base, 0)
        return (base + 1, FOUNDATION.index(top)) if top in FOUNDATION else (base + 2, 0)

    def listing(tier_dirs) -> str:
        return ", ".join(f"`{name}/`" for name in tier_dirs)

    lines = ["# Modules", "",
             "Generated by `scripts/update-docs.py` from the module docstrings. The modules form "
             f"two libraries. The main library `{MAIN}` (below `{MAIN}/`) contains exactly the "
             "modules that the six main results need; `Solution.lean` and the comparator use only "
             f"it. The paper library `{PAPER}` (below `{PAPER}/`) imports `{MAIN}` and holds the "
             f"rest of the paper; `{MAIN}` never imports it. The directories form tiers, which "
             "`scripts/check-layers.py` enforces:", "",
             f"* `{MAIN}/`: `Statements.lean` states the main results and imports only the "
             "foundation; each other module is the endpoint of one result and is imported by no "
             "library module.",
             f"* Foundation ({listing(FOUNDATION)}, in either library): general results, which "
             "import only Mathlib, the vendored libraries and each other.",
             "* Topics (the other directories): the proof routes, each in the directory of its "
             f"topic. Those of `{PAPER}/` hold the results that only the paper library uses, and "
             f"`{PAPER}/Center/` is Section 5 of the paper, which no main result uses.",
             f"* Side results ({listing(f'{PAPER}/{name}' for name in SIDE_RESULT)}): "
             "counterexamples, and the paper's intermediate statements as stated there; imported "
             "by no other directory.", ""]
    for directory in sorted(groups, key=lambda name: (tier(name), name)):
        lines += [f"## `{directory}/`: {DIRECTORIES[directory]}", "", "| Module | Content |",
                  "| --- | --- |"]
        for path in groups[directory]:
            link = path.relative_to(ROOT / "docs", walk_up=True)
            lines.append(f"| [`{module_name(path)}`]({link}) | {first_sentence(path)} |")
        lines.append("")
    return "\n".join(lines)


def render_statements() -> str:
    audit = audit_schema.load()
    problems = audit_schema.validate(audit)
    if problems:
        raise SystemExit("docs/completion-audit.json is malformed (run scripts/audit-evidence.py):"
                         "\n  " + "\n  ".join(problems))
    evidence = {item["id"]: item for item in audit["evidence"]}
    cache: dict[str, dict[str, int]] = {}

    def link(ref: str, counterexamples=()) -> str:
        item = evidence[ref]
        file, name = item["file"], item["declaration"]
        if file.startswith(".lake/"):  # external: link to the pinned Mathlib revision
            target = ("https://github.com/leanprover-community/mathlib4/blob/"
                      f"{audit['dependency_revisions']['mathlib']}/"
                      f"{file.removeprefix('.lake/packages/mathlib/')}")
        else:
            target = f"../{file}"
        path = ROOT / file
        if path.is_file():
            if file not in cache:
                cache[file] = declarations(path)
            if name in cache[file]:
                target += f"#L{cache[file][name]}"
        text = f"[`{name.removeprefix('CCDN.')}`]({target})"
        return text + " (counterexample)" if ref in counterexamples else text

    requirements = audit["requirements"]
    counts = {status: sum(r["statement_status"] == status for r in requirements)
              for status in audit_schema.STATUSES}
    lines = ["# Audited statements", "",
             "Generated by `scripts/update-docs.py` from `docs/completion-audit.json`, which also "
             "records the scope notes and the full text of each correction "
             "([schema](audit-schema.md)). Discrepancies with the paper are explained in "
             "[discrepancies.md](discrepancies.md).", "",
             f"## Statements of the paper ({len(requirements)})", "",
             "| Status | Meaning | Count |", "| --- | --- | --- |"]
    lines += [f"| `{status}` | {meaning} | {counts[status]} |"
              for status, meaning in audit_schema.STATUSES.items()]
    lines += ["", "A `matched` entry may be qualified: "
              + "; ".join(f"*{key.replace('_', ' ')}*: {value}"
                          for key, value in audit_schema.QUALIFIERS.items()) + ".", "",
              "| Paper | Status | In addenda | Lean declarations |",
              "| --- | --- | --- | --- |"]
    for requirement in requirements:
        status = requirement["statement_status"]
        if "qualifier" in requirement:
            status += f" ({requirement['qualifier'].replace('_', ' ')})"
        addenda = {True: "yes", False: "no"}.get(requirement.get("in_addenda"), "")
        counterexamples = set(requirement.get("counterexample_refs", []))
        names = ", ".join(link(ref, counterexamples) for ref in requirement["evidence_refs"])
        lines.append(f"| {requirement['source_label']} | {status} | {addenda} | {names} |")

    externals = audit["external_dependencies"]
    lines += ["", f"## External inputs cited by the paper ({len(externals)})", "",
              "None of these is assumed. Statuses: "
              + "; ".join(f"`{key}`: {value}"
                          for key, value in audit_schema.DEPENDENCY_STATUSES.items()) + ".", "",
              "| Input | Status | Lean declarations |", "| --- | --- | --- |"]
    for item in externals:
        names = ", ".join(link(ref) for ref in item["evidence_refs"])
        reference = item["reference"].replace("|", "\\|")
        lines.append(f"| {reference} | {item['dependency_status']} | {names} |")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="fail if the files are stale")
    check = parser.parse_args().check
    stale, drifted = [], []
    for target, text in ((MODULES, render_modules()), (STATEMENTS, render_statements())):
        name = str(target.relative_to(ROOT))
        if not check:
            target.write_text(text, encoding="utf-8")
            continue
        current = target.read_text(encoding="utf-8") if target.exists() else ""
        if current == text:
            continue
        if ANCHOR.sub(")", current) == ANCHOR.sub(")", text):
            drifted.append(name)
        else:
            stale.append(name)
    if stale:
        print(f"Out of date: {', '.join(stale)}; run scripts/update-docs.py")
        return 1
    if check:
        print("Generated documentation is current.")
        if drifted:
            print(f"  Note: line anchors in {', '.join(drifted)} have drifted; "
                  "run scripts/update-docs.py to refresh them.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
