#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"

if grep -RInE '^[[:space:]]*(sorry|admit)([[:space:]]|$)' \
    --include='*.lean' DGBOZK.lean DGBOZK; then
  echo 'Unfinished Lean proof found.' >&2
  exit 1
fi

if grep -RInE '^[[:space:]]*(axiom|constant|opaque)[[:space:]]' \
    --include='*.lean' DGBOZK.lean DGBOZK; then
  echo 'Project-level axiom-like declaration found.' >&2
  exit 1
fi

python3 scripts/check_identities.py

if grep -q '^import DGBOZK.Resonance' DGBOZK.lean; then
  echo 'Legacy resonance module must not be in the cleaned-manuscript target.' >&2
  exit 1
fi

lake build --wfail
lake env lean DGBOZK/Audit.lean
