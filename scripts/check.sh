#!/usr/bin/env bash
# Run every repository check; CI runs this script on each push and pull request.
# The Python checks need Python 3.12 or later and print one line each when they pass.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/check-lean-sources.py
python3 scripts/normalize-imports.py --check
python3 scripts/check-layers.py
python3 scripts/check-provenance.py
python3 scripts/audit-evidence.py
python3 scripts/check-docs.py
python3 scripts/check-consistency.py
python3 scripts/update-root.py --check
python3 scripts/update-docs.py --check

# Builds the library, Challenge, Solution and Axioms. Elaborating Axioms runs the axiom audit,
# so a disallowed axiom fails the build, and Lake prints (or, for a cached build, replays) its
# summary and the axioms of the compared theorems; a separate `lake env lean Axioms.lean` is
# not needed.
lake build
