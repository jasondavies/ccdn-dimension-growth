#!/usr/bin/env python3
"""Verify vendored provenance and that no project module escapes the root import.

Checks that the vendored Bombieri–Vaaler and Mertens sources match the hashes recorded in their
`upstream.json`, that reverse-applying `lean-4.35.patch` to the patched Bombieri–Vaaler files
reproduces the upstream hashes, that every module of the `CCDN` and `CCDNPaper` libraries and of
the vendored libraries declared in lakefile.toml is reachable from one of the roots `CCDN.lean`
and `CCDNPaper.lean`, and that each of these modules belongs to exactly one `lean_lib` (Lake
assigns a module to the library whose root name is a prefix of the module name). All problems are
reported before exiting.
"""
import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from common import LIBRARIES, MAIN, PAPER, ROOT, import_closure, imports, lean_libraries, \
    project_modules, relative, sha256, vendor_libraries

BOMBIERI_VAALER = ROOT / "vendor" / "bombieri-vaaler"
MERTENS = ROOT / "vendor" / "mertens"
PROJECT_PREFIXES = LIBRARIES + tuple(name for name, _ in vendor_libraries())


def check_bombieri_vaaler(errors: list[str]) -> int:
    metadata = json.loads((BOMBIERI_VAALER / "upstream.json").read_text(encoding="utf-8"))
    upstream, patched = metadata["files"], metadata["patched_files"]
    expected = upstream | patched
    actual = {relative(path).removeprefix("vendor/bombieri-vaaler/")
              for path in (BOMBIERI_VAALER / "ArithmeticHeights").rglob("*.lean")}
    for name in sorted(actual - set(expected)):
        errors.append(f"vendor/bombieri-vaaler/{name}: not recorded in upstream.json")
    for name in sorted(set(expected) - actual):
        errors.append(f"vendor/bombieri-vaaler/{name}: recorded in upstream.json but missing")
    for name in sorted(actual & set(expected)):
        if sha256(BOMBIERI_VAALER / name) != expected[name]:
            errors.append(f"vendor/bombieri-vaaler/{name}: hash differs from upstream.json")

    # Reverse-apply the compatibility patch: it must take each patched file back to upstream.
    patch = BOMBIERI_VAALER / "lean-4.35.patch"
    with tempfile.TemporaryDirectory() as scratch:
        for name in patched:
            target = Path(scratch) / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(BOMBIERI_VAALER / name, target)
        result = subprocess.run(["git", "apply", "--reverse", str(patch)], cwd=scratch,
                                capture_output=True, text=True)
        if result.returncode != 0:
            errors.append(f"{relative(patch)} does not reverse-apply: {result.stderr.strip()}")
        else:
            for name in patched:
                if sha256(Path(scratch) / name) != upstream.get(name):
                    errors.append(f"{relative(patch)} does not map {name} back to its upstream "
                                  "hash")
    return len(expected)


def check_mertens(errors: list[str]) -> int:
    metadata = json.loads((MERTENS / "upstream.json").read_text(encoding="utf-8"))
    actual = {relative(path).removeprefix("vendor/mertens/") for path in MERTENS.rglob("*.lean")}
    if actual != {metadata["path"]}:
        errors.append(f"vendor/mertens: Lean files {sorted(actual)} differ from the recorded "
                      f"{metadata['path']}")
    elif sha256(MERTENS / metadata["path"]) != metadata["adapted_sha256"]:
        errors.append(f"vendor/mertens/{metadata['path']}: hash differs from adapted_sha256")
    return 1


def owners(name: str) -> list[str]:
    """The `lean_lib`s whose (default) root is a name prefix of the module `name`."""
    return [lib for lib, _ in lean_libraries()
            if name == lib or name.startswith(lib + ".")]


def check_reachability(errors: list[str]) -> dict[str, int]:
    modules = project_modules()
    for name, path in sorted(modules.items()):
        for dep in imports(path):
            if dep not in modules and dep.startswith(PROJECT_PREFIXES):
                errors.append(f"{relative(path)}: imports missing project module {dep}")
        if len(found := owners(name)) != 1:
            errors.append(f"{relative(path)}: module {name} belongs to {len(found)} libraries "
                          f"({', '.join(found) or 'none'}), not exactly one")
    reachable = import_closure(list(LIBRARIES), modules)
    library = {name for name in modules if name.startswith(PROJECT_PREFIXES)}
    for name in sorted(library - reachable):
        errors.append(f"{relative(modules[name])}: not imported (transitively) by CCDN.lean or "
                      "CCDNPaper.lean")
    own = {lib: sum(owners(name) == [lib] for name in reachable) for lib in LIBRARIES}
    return {"total": len(reachable), "main": import_closure([MAIN], modules), **own}


def main() -> int:
    argparse.ArgumentParser(description=__doc__.splitlines()[0]).parse_args()
    errors: list[str] = []
    hashes = check_bombieri_vaaler(errors) + check_mertens(errors)
    counts = check_reachability(errors)
    if errors:
        print("Provenance check failed:")
        print("\n".join(f"  {error}" for error in errors))
        return 1
    print(f"Provenance: {hashes} vendor hashes and the compatibility patch match; "
          f"{len(counts['main'])} modules reachable from {MAIN}.lean and {counts['total']} from "
          f"{MAIN}.lean and {PAPER}.lean ({counts[MAIN]} in {MAIN} and {counts[PAPER]} in {PAPER}, "
          "roots included; each module in exactly one library).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
