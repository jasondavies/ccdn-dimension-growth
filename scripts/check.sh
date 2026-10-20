#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-lean-sources.py
python3 scripts/check-provenance.py
python3 scripts/audit-evidence.py
lake build
lake env lean Axioms.lean
