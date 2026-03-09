#!/usr/bin/env bash
set -euo pipefail

# Optional override for air-gapped environments.
# Example:
#   LEAN_ELAN_INIT_URL=file:///workspace/cache/elan-init.sh scripts/build/install_lean.sh
ELAN_INIT_URL="${LEAN_ELAN_INIT_URL:-https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh}"

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

# Try distro package first (works in some CI images without GitHub access).
if command -v apt-get >/dev/null 2>&1; then
  echo "[install-lean] attempting apt install of elan..."
  if apt-get update && apt-get install -y elan; then
    if command -v elan >/dev/null 2>&1; then
      elan toolchain install "$(cat lean-toolchain)" || true
      if [ -x "$HOME/.elan/bin/lake" ]; then
        export PATH="$HOME/.elan/bin:$PATH"
      fi
      if command -v lake >/dev/null 2>&1; then
        lake --version || true
        exit 0
      fi
    fi
  else
    echo "[install-lean] apt path failed (likely network/proxy restriction)"
  fi
fi

echo "[install-lean] attempting elan bootstrap install from: $ELAN_INIT_URL"
if command -v curl >/dev/null 2>&1; then
  if curl -fsSL "$ELAN_INIT_URL" | sh -s -- -y; then
    export PATH="$HOME/.elan/bin:$PATH"
    if command -v lake >/dev/null 2>&1; then
      echo "[install-lean] installed via elan bootstrap"
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
    echo "[install-lean] elan bootstrap download/install failed"
    echo "[install-lean] elan bootstrap download failed"
  fi
fi

echo "[install-lean] unable to install Lean/Lake automatically in this environment."
echo "[install-lean] this environment is blocking outbound package downloads (HTTP 403 via proxy)."
echo "[install-lean] workaround: provide a reachable mirror/local file via LEAN_ELAN_INIT_URL."
echo "[install-lean] Please install elan manually, then ensure '~/.elan/bin' is on PATH."
exit 127
