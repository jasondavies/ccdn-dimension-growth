#!/usr/bin/env python3
"""Check the layering of the two libraries and of their directories.

* Libraries: no module of the main library `CCDN` (below `CCDN/`, or the root CCDN.lean)
  imports a module of the paper library `CCDNPaper`; `CCDNPaper` may import `CCDN`.
* Foundation tier: a module in one of the FOUNDATION directories imports only Mathlib, the
  vendored libraries and other foundation modules, never a topic directory.
* `CCDN/Statements.lean`, which states the main results, imports only foundation modules.
* Endpoints: the other modules at the top of `CCDN/` prove the main results and are imported
  by no library module (only by the root CCDN.lean, Solution.lean and Axioms.lean).
* Side results: a module in a SIDE_RESULT directory of `CCDNPaper/` (counterexamples and the
  paper's statements as printed) is imported by no module outside that directory.

All violations are reported before exiting.
"""
import argparse
import sys

from common import FOUNDATION, MAIN, PAPER, ROOT, SIDE_RESULT, imports, library_module_paths, \
    module_name

STATEMENTS = f"{MAIN}.Statements"


def library(name: str) -> str:
    return name.split(".")[0]


def directory(name: str) -> str:
    """The top-level directory of `Lib.Dir.Module` (empty for a module at the top of `Lib/`)."""
    parts = name.split(".")
    return parts[1] if len(parts) > 2 else ""


def main() -> int:
    argparse.ArgumentParser(description=__doc__.splitlines()[0]).parse_args()
    modules = {module_name(path): path for path in library_module_paths()}
    sources = dict(modules, **{name: ROOT / f"{name}.lean" for name in (MAIN, PAPER)})
    endpoints = {name for name in modules
                 if library(name) == MAIN and directory(name) == "" and name != STATEMENTS}
    problems: list[str] = []
    for name, path in sorted(sources.items()):
        source = path.relative_to(ROOT).as_posix()
        home = directory(name)
        for target in imports(path):
            if library(target) == PAPER and library(name) == MAIN:
                problems.append(f"{source}: the main library imports {target} from the paper "
                                f"library {PAPER}; {MAIN} must not depend on {PAPER} (move the "
                                f"needed result into {MAIN}/, or this module into {PAPER}/)")
            if target not in modules or name in (MAIN, PAPER):
                continue  # Mathlib, a vendored library, or an import of a root module
            there = directory(target)
            if (home in FOUNDATION or name == STATEMENTS) and there not in FOUNDATION:
                what = "foundation module" if home in FOUNDATION else "the statements module"
                problems.append(f"{source}: {what} imports {target}, which is not in a foundation "
                                f"directory ({', '.join(FOUNDATION)}); move the shared part down "
                                "or move this module into the topic directory that uses it")
            if target in endpoints:
                problems.append(f"{source}: imports the endpoint {target}; move the needed result "
                                "into a topic directory and let the endpoint import it")
            if (library(target) == PAPER and there in SIDE_RESULT
                    and (library(name), home) != (PAPER, there)):
                problems.append(f"{source}: imports the side result {target} ({PAPER}/{there}/ "
                                "is imported only from within that directory)")
    if problems:
        print("Layering check failed:")
        print("\n".join(f"  {problem}" for problem in problems))
        return 1
    foundation = sum(directory(name) in FOUNDATION for name in modules)
    print(f"Layering: {MAIN} imports nothing from {PAPER}; the {foundation} foundation modules "
          f"({', '.join(FOUNDATION)}) and {STATEMENTS} import no topic module; the "
          f"{len(endpoints)} endpoints and the side results ({', '.join(SIDE_RESULT)}) are "
          "imported by no other library module.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
