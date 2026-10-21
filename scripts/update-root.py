#!/usr/bin/env python3
"""Generate CCDN.lean and CCDNPaper.lean, the root modules of the two libraries.

Each root imports every module of its library (the modules below `CCDN/`, respectively
`CCDNPaper/`). `--check` fails when a root is out of date instead of rewriting it.
"""
import argparse
import sys

from common import LIBRARIES, MAIN, PAPER, ROOT, library_module_paths, module_name

HEADER = """/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
"""
DOCS = {
    MAIN: """/-!
# CCDN

Root module of the formalisation of Castryck, Cluckers, Dittmann and Nguyen, *The dimension
growth conjecture, polynomial in the degree and without logarithmic factors* (Algebra & Number
Theory 14, 2020). It imports every module of the main library; `scripts/update-root.py`
generates it. Section 5 of the paper, the paper's intermediate statements as printed and the
counterexamples are in the separate library `CCDNPaper`, which this library does not import.

The main results are:
* `CCDN.projective_dimension_growth` (Theorem 1);
* `CCDN.projectiveCurveBound` (Theorem 2);
* `CCDN.affineCurveBound` (Theorem 3);
* `CCDN.affine_hypersurface_dimension_growth` and its rational form (Theorem 4);
* `CCDN.projective_integral_curve_lower_bound` (Proposition 5);
* `CCDN.classGroup_two_torsion_bound` (Theorem 6).

`Challenge.lean` states them using Mathlib only, and `Solution.lean` derives those statements
from this library.
-/
""",
    PAPER: """/-!
# CCDNPaper

Root module of the paper library of the CCDN formalisation. It imports every module of the
library; `scripts/update-root.py` generates it. The library builds on the main library `CCDN`
and holds the parts of the paper that the main results do not use:
* `CCDNPaper/Center/`: Section 5 (Chow forms, good centres and Plücker equations);
* `CCDNPaper/Statements/`: the paper's intermediate statements and side results as printed
  (or as corrected), linked to their labels in `docs/statements.md`;
* `CCDNPaper/Counterexample/`: the formal refutations of printed intermediate statements.

Its declarations live in the namespace `CCDN`, like those of the main library.
-/
""",
}


def render(library: str) -> str:
    modules = sorted(module_name(path) for path in library_module_paths(library))
    imports = "".join(f"public import {module}\n" for module in modules)
    return HEADER + "module\n\n" + imports + "\n" + DOCS[library]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="fail if a root module is stale")
    check = parser.parse_args().check
    stale = []
    for library in LIBRARIES:
        target = ROOT / f"{library}.lean"
        expected = render(library)
        if not check:
            target.write_text(expected, encoding="utf-8")
        elif not target.exists() or target.read_text(encoding="utf-8") != expected:
            stale.append(target.name)
    if stale:
        print(f"Out of date: {', '.join(stale)}; run scripts/update-root.py")
        return 1
    if check:
        print(f"{' and '.join(f'{name}.lean' for name in LIBRARIES)} import every module of "
              "their libraries.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
