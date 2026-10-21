#!/usr/bin/env python3
"""Normalize the import block of every module of the CCDN and CCDNPaper libraries.

The header of each module below `CCDN/` and `CCDNPaper/`, and of the roots `CCDN.lean` and
`CCDNPaper.lean`, must read: the `module` line, one blank line, the `public import` lines sorted
by module name, the plain `import` (and `import all`) lines sorted by module name, then one
blank line and the module docstring `/-! ... -/`. Nothing else may stand between `module` and the docstring. The sort order is
Python's string order on module names, the order in which scripts/update-root.py writes the
roots, so the generated root modules already satisfy this layout.

`--check` reports the modules whose header differs instead of rewriting them.
"""
import argparse
import re
import sys

from common import library_module_paths, relative, root_files

MODULE = re.compile(r"^module\b")
IMPORT_LINE = re.compile(r"^(public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\s-]+)\s*$")


def normalize(text: str) -> tuple[str | None, str | None]:
    """The normalized text, or `(None, problem)` when the header cannot be normalized."""
    lines = text.split("\n")
    start = next((i for i, line in enumerate(lines) if MODULE.match(line)), None)
    if start is None or lines[start] != "module":
        return None, "has no bare `module` line"
    public: dict[str, str] = {}
    plain: dict[str, str] = {}
    end = start + 1
    while end < len(lines):
        line = lines[end]
        if match := IMPORT_LINE.match(line):
            line = " ".join(line.split())
            (public if match.group(1) else plain)[line] = match.group(2)
        elif line.strip():
            break
        end += 1
    if end == len(lines) or not lines[end].startswith("/-!"):
        return None, "must follow its imports with the module docstring `/-! ... -/`"
    header = ["module", ""]
    for block in (public, plain):
        header += sorted(block, key=lambda line: (block[line], line))
    if public or plain:
        header.append("")
    return "\n".join(lines[:start] + header + lines[end:]), None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="fail if an import block is not normalized")
    check = parser.parse_args().check
    paths = root_files() + library_module_paths()
    failed = False
    changed = 0
    for path in paths:
        text = path.read_text(encoding="utf-8")
        expected, problem = normalize(text)
        if problem:
            print(f"{relative(path)}: {problem}")
            failed = True
        elif expected != text:
            changed += 1
            if check:
                print(f"{relative(path)}: import block is not normalized; "
                      "run scripts/normalize-imports.py")
                failed = True
            else:
                path.write_text(expected, encoding="utf-8")
    if check and not failed:
        print(f"Imports: the {len(paths)} library modules list their public, then plain imports, "
              "each sorted, between `module` and the docstring.")
    elif not check:
        print(f"Normalized the import blocks of {changed} of {len(paths)} modules.")
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
