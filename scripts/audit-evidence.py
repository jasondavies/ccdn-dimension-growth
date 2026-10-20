#!/usr/bin/env python3
"""Check or refresh the evidence locations recorded in docs/completion-audit.json.

Each evidence entry names a Lean declaration together with the file, line, keyword and
SHA-256 of the file that contains it. `--check` (the default) fails when any entry is stale;
`--update` rewrites the locations and hashes from the current sources. Declarations are
found textually, by their final name components, so renaming a declaration still needs its
`declaration` field edited by hand.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "docs" / "completion-audit.json"
SEARCH_ROOTS = [ROOT / "CCDN", ROOT / "vendor"]
KEYWORDS = "theorem|lemma|def|abbrev|structure|class|instance|inductive"
DECLARATION = re.compile(
    rf"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public|nonrec|unsafe)\s+)*"
    rf"({KEYWORDS})\s+([^\s(:{{\[]+)",
    re.M,
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def index_sources() -> dict[str, list[tuple[str, int, str]]]:
    """Map each declared (possibly dotted) name to its (file, line, keyword) sites."""
    sites: dict[str, list[tuple[str, int, str]]] = {}
    for search_root in SEARCH_ROOTS:
        for path in sorted(search_root.rglob("*.lean")):
            if ".lake" in path.parts:
                continue
            text = path.read_text(encoding="utf-8")
            for match in DECLARATION.finditer(text):
                line = text.count("\n", 0, match.start()) + 1
                relative = str(path.relative_to(ROOT))
                sites.setdefault(match.group(2), []).append((relative, line, match.group(1)))
    return sites


def locate(entry: dict, sites: dict) -> tuple[str, int, str] | None:
    """Find the site of an evidence declaration, preferring the recorded file."""
    if not entry["file"].startswith(("CCDN/", "vendor/")):
        return None  # external evidence (Mathlib) is pinned by revision, not relocated
    components = entry["declaration"].split(".")
    for start in range(len(components)):
        candidates = sites.get(".".join(components[start:]), [])
        if not candidates:
            continue
        preferred = [site for site in candidates if site[0] == entry["file"]]
        if preferred:
            return min(preferred, key=lambda site: abs(site[1] - entry["line"]))
        if len(candidates) == 1:
            return candidates[0]
        raise SystemExit(f"{entry['id']}: ambiguous declaration {entry['declaration']}")
    raise SystemExit(f"{entry['id']}: declaration {entry['declaration']} not found")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--update", action="store_true", help="rewrite stale entries")
    update = parser.parse_args().update

    audit = json.loads(AUDIT.read_text(encoding="utf-8"))
    sites = index_sources()
    stale = []
    for entry in audit["evidence"]:
        path = ROOT / entry["file"]
        site = locate(entry, sites)
        if site is None:
            if not path.exists():
                stale.append(f"{entry['id']}: missing external file {entry['file']}")
            elif sha256(path) != entry["sha256"]:
                stale.append(f"{entry['id']}: hash of {entry['file']} changed")
            continue
        file, line, kind = site
        current = {"file": file, "line": line, "kind": kind, "sha256": sha256(ROOT / file)}
        changed = {key: value for key, value in current.items() if entry[key] != value}
        if changed:
            stale.append(f"{entry['id']} {entry['declaration']}: {sorted(changed)}")
            entry.update(current)
    for item in audit["follow_up_files"]:
        path = ROOT / item["file"]
        if not path.exists():
            raise SystemExit(f"follow-up file {item['file']} no longer exists")
        if sha256(path) != item["sha256"]:
            stale.append(f"follow-up file {item['file']}: hash changed")
            item["sha256"] = sha256(path)

    if update:
        AUDIT.write_text(json.dumps(audit, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"Updated {len(stale)} stale audit entries.")
        return 0
    if stale:
        print("Stale completion-audit evidence (run scripts/audit-evidence.py --update):")
        print("\n".join(f"  {line}" for line in stale))
        return 1
    print(f"Audit evidence current: {len(audit['evidence'])} declarations.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
