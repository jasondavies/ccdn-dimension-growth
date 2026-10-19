#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_sources.py
lake build
lake env lean Axioms.lean
