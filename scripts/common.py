"""Helpers shared by the repository scripts (Python 3.12 or later)."""
from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

if sys.version_info < (3, 12):
    raise SystemExit("The repository scripts need Python 3.12 or later.")

import tomllib  # noqa: E402  (after the version check, which gives a clearer message)

ROOT = Path(__file__).resolve().parents[1]
LIBRARY = ROOT / "CCDN"
AUDIT = ROOT / "docs" / "completion-audit.json"

# The directory tiers of `CCDN/` (scripts/check-layers.py enforces them). Foundation modules
# import only Mathlib, the vendored libraries and each other; topic directories hold the proof
# routes; side-result directories are imported by no other directory.
FOUNDATION = ("ForMathlib", "Algebra", "Analysis", "Height", "Hilbert")
SIDE_RESULT = ("Counterexample", "Paper")

# `[public] [meta] import [all] Module`, as accepted by the Lean 4 module system.
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\s-]+)", re.M)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(path: Path) -> str:
    """The repository-relative spelling of `path`."""
    return path.relative_to(ROOT).as_posix()


def module_name(path: Path, src_dir: Path = ROOT) -> str:
    return ".".join(path.relative_to(src_dir).with_suffix("").parts)


def library_module_paths() -> list[Path]:
    """Every module of the `CCDN` library below `CCDN/`, sorted (the root `CCDN.lean` excluded)."""
    return sorted(LIBRARY.rglob("*.lean"))


def lakefile() -> dict:
    return tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))


def lean_libraries() -> list[tuple[str, Path]]:
    """The `(name, source directory)` of every `lean_lib` declared in lakefile.toml."""
    return [(lib["name"], ROOT / lib.get("srcDir", "."))
            for lib in lakefile().get("lean_lib", [])]


def vendor_libraries() -> list[tuple[str, Path]]:
    """The `lean_lib`s whose sources live below `vendor/`."""
    vendor = ROOT / "vendor"
    return [(name, src) for name, src in lean_libraries() if src.is_relative_to(vendor)]


def project_modules() -> dict[str, Path]:
    """Map every module of every `lean_lib` in lakefile.toml to its source file."""
    modules: dict[str, Path] = {}
    for name, src in lean_libraries():
        root_file = src / f"{name}.lean"
        if root_file.exists():
            modules[name] = root_file
        directory = src / name
        if directory.is_dir():
            for path in sorted(directory.rglob("*.lean")):
                modules[module_name(path, src)] = path
    return modules


def imports(path: Path) -> list[str]:
    """The modules imported by the Lean source at `path`."""
    return IMPORT.findall(path.read_text(encoding="utf-8"))


def import_closure(roots: list[str], modules: dict[str, Path]) -> set[str]:
    """The project modules reachable from `roots` (external imports such as Mathlib are skipped)."""
    seen: set[str] = set()
    stack = [root for root in roots if root in modules]
    while stack:
        name = stack.pop()
        if name in seen:
            continue
        seen.add(name)
        stack.extend(dep for dep in imports(modules[name]) if dep in modules)
    return seen


DECLARATION = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|nonrec|unsafe|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\s+"
    r"([^\s(:{\[]+)"
)
SCOPE_OPEN = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|public|private)\s+)*(section|namespace|mutual)\b"
    r"\s*(\S*)"
)
SCOPE_END = re.compile(r"^end\b")


def strip_comments(text: str) -> str:
    """Blank out Lean comments (including docstrings), keeping line breaks."""
    out = []
    index, depth = 0, 0
    while index < len(text):
        if text.startswith("/-", index):
            depth += 1
            out.append("  ")
            index += 2
        elif depth and text.startswith("-/", index):
            depth -= 1
            out.append("  ")
            index += 2
        elif not depth and text.startswith("--", index):
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
            out.append(" " * (end - index))
            index = end
        else:
            character = text[index]
            out.append(character if not depth or character == "\n" else " ")
            index += 1
    return "".join(out)


def declarations(path: Path) -> dict[str, int]:
    """Map the fully qualified name of each declaration in a Lean file to its line number.

    A lightweight textual parser: it tracks `namespace`/`section`/`mutual`/`end` and skips
    comments, which is enough for this repository's sources and Mathlib's.
    """
    found: dict[str, int] = {}
    scopes: list[str | None] = []
    lines = strip_comments(path.read_text(encoding="utf-8")).split("\n")
    for number, line in enumerate(lines, 1):
        if match := SCOPE_OPEN.match(line):
            scopes.append(match.group(2) if match.group(1) == "namespace" else None)
        elif SCOPE_END.match(line):
            if scopes:
                scopes.pop()
        elif match := DECLARATION.match(line):
            name = match.group(1)
            if name.startswith("_root_."):
                full = name.removeprefix("_root_.")
            else:
                full = ".".join([scope for scope in scopes if scope] + [name])
            found.setdefault(full, number)
    return found
