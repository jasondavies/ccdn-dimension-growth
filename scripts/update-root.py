#!/usr/bin/env python3
"""Generate CCDN.lean, the root module importing every module of the library.

`--check` fails when CCDN.lean is out of date instead of rewriting it.
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "CCDN.lean"
HEADER = """module

/-!
# CCDN

Root module of the formalisation of Castryck, Cluckers, Dittmann and Nguyen, *The dimension
growth conjecture, polynomial in the degree and without logarithmic factors* (Algebra & Number
Theory 14, 2020). It imports every module of the library; `scripts/update-root.py` generates it.

The main results are:
* `CCDN.projective_dimension_growth_explicit` (Theorem 1);
* `CCDN.projectiveCurveBound` (Theorem 2);
* `CCDN.affineCurveBound` (Theorem 3);
* `CCDN.top_form_hypersurface_dimension_growth_cubic` and its rational form (Theorem 4);
* `CCDN.projective_integral_curve_lower_bound` (Proposition 5);
* `CCDN.classGroup_two_torsion_bound` (Theorem 6).

`Challenge.lean` states them using Mathlib only, and `Solution.lean` derives those statements
from this library.
-/

"""


def render() -> str:
    modules = sorted(
        ".".join(path.relative_to(ROOT).with_suffix("").parts)
        for path in (ROOT / "CCDN").rglob("*.lean")
    )
    return HEADER + "".join(f"public import {module}\n" for module in modules)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="fail if CCDN.lean is stale")
    expected = render()
    if parser.parse_args().check:
        if TARGET.read_text(encoding="utf-8") != expected:
            print("CCDN.lean is out of date; run scripts/update-root.py")
            return 1
        print("CCDN.lean imports every library module.")
        return 0
    TARGET.write_text(expected, encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
