#!/usr/bin/env bash
# One-shot setup for a fresh Codespace / clean machine.
# Safe to re-run: every step is idempotent.
set -euo pipefail

echo "==> [1/4] Installing elan (the Lean version manager)"
if ! command -v elan >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"
grep -q '.elan/bin' "$HOME/.bashrc" 2>/dev/null || \
  echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$HOME/.bashrc"

echo "==> [2/4] Installing the Lean toolchain pinned in lean-toolchain"
elan toolchain install "$(cat lean-toolchain)"
lean --version

echo "==> [3/4] Downloading prebuilt Mathlib (this is the big one, ~5 GB)"
lake exe cache get

echo "==> [4/4] Building DGBOZK"
lake build

echo
echo "Setup complete. Now run the honesty check:"
echo "    lake env lean DGBOZK/Audit.lean"
