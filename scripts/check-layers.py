#!/usr/bin/env python3
"""Check the layering of the library directories.

* Foundation tier: a module in one of the FOUNDATION directories of `CCDN/` imports only
  Mathlib, the vendored libraries and other foundation modules, never a topic directory.
* `CCDN/Statements.lean`, which states the main results, imports only foundation modules.
* Endpoints: the other modules at the top of `CCDN/` prove the main results and are imported
  by no library module (only by the root CCDN.lean, Solution.lean and Axioms.lean).
* Side results: a module in a SIDE_RESULT directory (counterexamples and restatements of the
  paper's literal statements) is imported by no module outside that directory.

All violations are reported before exiting.
"""
import argparse
import sys

from common import ROOT, imports, library_module_paths, module_name

FOUNDATION = ("ForMathlib", "Algebra", "Analysis", "Height", "Hilbert")
SIDE_RESULT = ("Counterexample", "Paper")
STATEMENTS = "CCDN.Statements"


def directory(name: str) -> str:
    """The top-level directory of `CCDN.Dir.Module` (empty for a module at the top of CCDN/)."""
    parts = name.split(".")
    return parts[1] if len(parts) > 2 else ""


def main() -> int:
    argparse.ArgumentParser(description=__doc__.splitlines()[0]).parse_args()
    modules = {module_name(path): path for path in library_module_paths()}
    endpoints = {name for name in modules if directory(name) == "" and name != STATEMENTS}
    problems: list[str] = []
    for name, path in sorted(modules.items()):
        source = path.relative_to(ROOT).as_posix()
        home = directory(name)
        for target in imports(path):
            if target not in modules:
                continue  # Mathlib or a vendored library
            there = directory(target)
            if (home in FOUNDATION or name == STATEMENTS) and there not in FOUNDATION:
                what = "foundation module" if home in FOUNDATION else "the statements module"
                problems.append(f"{source}: {what} imports {target}, which is not in a foundation "
                                f"directory ({', '.join(FOUNDATION)}); move the shared part down "
                                "or move this module into the topic directory that uses it")
            if target in endpoints:
                problems.append(f"{source}: imports the endpoint {target}; move the needed result "
                                "into a topic directory and let the endpoint import it")
            if there in SIDE_RESULT and there != home:
                problems.append(f"{source}: imports the side result {target} (CCDN/{there}/ is "
                                "imported only from within that directory)")
    if problems:
        print("Layering check failed:")
        print("\n".join(f"  {problem}" for problem in problems))
        return 1
    foundation = sum(directory(name) in FOUNDATION for name in modules)
    print(f"Layering: the {foundation} foundation modules ({', '.join(FOUNDATION)}) and "
          f"{STATEMENTS} import no topic module; the {len(endpoints)} endpoints and the side "
          f"results ({', '.join(SIDE_RESULT)}) are imported by no other library module.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
