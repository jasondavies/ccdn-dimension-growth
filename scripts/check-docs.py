#!/usr/bin/env python3
"""Check that the hand-written documentation cites files and declarations that exist.

* Every relative Markdown link in README.md and docs/ (including docs/history/) must resolve.
* A link of the form [`name`](path/To/File.lean) must point to a file that declares `name`.
* In docs/overview.md, whose paths are relative to CCDN/, each section names its endpoint module
  in its heading, for example "(`AffineCurveBound.lean`)". Every module the section cites must
  lie in the import closure of that endpoint (of CCDN.lean for a section without one), every
  directory it cites must exist, and every declaration name it cites must be declared in that
  closure.

All problems are reported before exiting.
"""
import argparse
import re
import sys
from pathlib import Path

from common import LIBRARY, ROOT, declarations, import_closure, project_modules, relative

DOCUMENTS = [ROOT / "README.md", *sorted((ROOT / "docs").rglob("*.md"))]
GENERATED = {ROOT / "docs" / "modules.md", ROOT / "docs" / "statements.md"}
OVERVIEW = ROOT / "docs" / "overview.md"
LINK = re.compile(r"\[([^\]]*)\]\(([^)\s]+)\)")
CODE = re.compile(r"`([^`]+)`")
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def looks_like_declaration(token: str) -> bool:
    """A backticked token that is a Lean name rather than mathematics or a path."""
    return (IDENTIFIER.fullmatch(token) is not None and len(token) >= 6
            and not token.endswith(".lean")
            and ("_" in token or re.search(r"[a-z][A-Z]", token) is not None))


class Declarations:
    """Fully qualified declaration names per file, parsed on demand."""

    def __init__(self) -> None:
        self.cache: dict[Path, set[str]] = {}

    def __call__(self, path: Path) -> set[str]:
        if path not in self.cache:
            self.cache[path] = set(declarations(path))
        return self.cache[path]

    def declares(self, paths, name: str) -> bool:
        return any(full == name or full.endswith("." + name)
                   for path in paths for full in self(path))


def check_links(document: Path, decls: Declarations, problems: list[str]) -> None:
    text = document.read_text(encoding="utf-8")
    for label, target in LINK.findall(text):
        if re.match(r"[a-z]+:", target) or target.startswith("#"):
            continue
        path = (document.parent / target.split("#", 1)[0]).resolve()
        if not path.exists():
            problems.append(f"{relative(document)}: broken link {target}")
            continue
        code = CODE.fullmatch(label)
        if (document not in GENERATED and code and path.suffix == ".lean"
                and looks_like_declaration(code.group(1))
                and not decls.declares([path], code.group(1))):
            problems.append(f"{relative(document)}: {relative(path)} does not declare "
                            f"{code.group(1)}")


def check_overview(decls: Declarations, problems: list[str]) -> int:
    modules = project_modules()
    paths_of = {name: path for name, path in modules.items()}
    sections = re.split(r"^## ", OVERVIEW.read_text(encoding="utf-8"), flags=re.M)[1:]
    cited = 0
    for section in sections:
        heading, _, body = section.partition("\n")
        endpoints = [token for token in CODE.findall(heading) if token.endswith(".lean")]
        root = ("CCDN." + endpoints[0].removesuffix(".lean").replace("/", ".")
                if endpoints else "CCDN")
        if root not in modules:
            problems.append(f"docs/overview.md, section '{heading}': endpoint {root} not found")
            continue
        closure = import_closure([root], modules)
        files = [paths_of[name] for name in closure]
        for token in CODE.findall(body):
            if token.endswith(".lean"):
                cited += 1
                name = "CCDN." + token.removesuffix(".lean").replace("/", ".")
                if name not in modules:
                    problems.append(f"docs/overview.md, section '{heading}': {token} does not "
                                    "exist")
                elif name not in closure:
                    problems.append(f"docs/overview.md, section '{heading}': {token} is not "
                                    f"imported by {root}")
            elif re.fullmatch(r"[A-Z][A-Za-z]*/", token):
                if not (LIBRARY / token).is_dir():
                    problems.append(f"docs/overview.md: directory CCDN/{token} does not exist")
            elif looks_like_declaration(token):
                cited += 1
                if not decls.declares(files, token):
                    problems.append(f"docs/overview.md, section '{heading}': {token} is not "
                                    f"declared in the import closure of {root}")
    return cited


def main() -> int:
    argparse.ArgumentParser(description=__doc__.splitlines()[0]).parse_args()
    decls = Declarations()
    problems: list[str] = []
    for document in DOCUMENTS:
        check_links(document, decls, problems)
    cited = check_overview(decls, problems)
    if problems:
        print("Documentation check failed:")
        print("\n".join(f"  {problem}" for problem in problems))
        return 1
    print(f"Documentation: links in {len(DOCUMENTS)} Markdown files resolve; the {cited} modules "
          "and declarations cited in docs/overview.md lie in their sections' import closures.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
