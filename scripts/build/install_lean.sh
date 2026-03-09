#!/usr/bin/env bash
set -euo pipefail

if command -v lake >/dev/null 2>&1; then
  echo "lake already installed: $(command -v lake)"
  lake --version || true
  exit 0
fi

if [ -x "$HOME/.elan/bin/lake" ]; then
  export PATH="$HOME/.elan/bin:$PATH"
  echo "lake found in ~/.elan/bin"
  lake --version || true
  exit 0
fi

echo "[install-lean] attempting elan bootstrap install..."
if command -v curl >/dev/null 2>&1; then
  if curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y; then
    export PATH="$HOME/.elan/bin:$PATH"
    if command -v lake >/dev/null 2>&1; then
      echo "[install-lean] installed via elan"
      lake --version || true
      exit 0
    fi
  else
    echo "[install-lean] elan bootstrap download failed"
  fi
fi

echo "[install-lean] unable to install Lean/Lake automatically in this environment."
echo "[install-lean] Please install elan manually, then ensure '~/.elan/bin' is on PATH."
exit 127
