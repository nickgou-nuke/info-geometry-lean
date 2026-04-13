#!/usr/bin/env bash
set -euo pipefail

# Example bootstrap for DGX Spark autonomous prover stack
# - OpenClaw + NemoClaw runtime
# - Hermes local learnable skills/memory
# - Locked Lean diagnostics (no unlocked builds)

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

INSTALL_OPENCLAW="${INSTALL_OPENCLAW:-1}"
INSTALL_NEMOCLAW="${INSTALL_NEMOCLAW:-1}"
RUN_LOCKED_BUILD="${RUN_LOCKED_BUILD:-1}"

log() { printf "\n[%s] %s\n" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$*"; }
need_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "Missing required command: $1" >&2
    exit 1
  }
}

need_cmd bash
need_cmd curl
need_cmd git

log "Preparing Hermes learnable lanes"
mkdir -p quarantine/hermes_skills quarantine/hermes_memory logs
[ -f quarantine/hermes_memory/MEMORY.md ] || printf "# Hermes Memory\n" > quarantine/hermes_memory/MEMORY.md
[ -f quarantine/hermes_memory/README.md ] || printf "Local Hermes memory lane.\n" > quarantine/hermes_memory/README.md

if [ "$INSTALL_OPENCLAW" = "1" ] && ! command -v openclaw >/dev/null 2>&1; then
  log "Installing OpenClaw"
  curl -fsSL https://openclaw.ai/install.sh | bash
fi

if command -v openclaw >/dev/null 2>&1; then
  log "OpenClaw diagnostics"
  openclaw --version || true
  openclaw doctor || true
  openclaw gateway status || true
else
  log "OpenClaw not found (set INSTALL_OPENCLAW=1 to install automatically)"
fi

if [ "$INSTALL_NEMOCLAW" = "1" ] && ! command -v nemoclaw >/dev/null 2>&1; then
  log "Installing NemoClaw"
  curl -fsSL https://www.nvidia.com/nemoclaw.sh | bash
fi

if command -v nemoclaw >/dev/null 2>&1; then
  log "NemoClaw diagnostics"
  nemoclaw --help >/dev/null || true
  nemoclaw my-assistant status || true
else
  log "NemoClaw not found (set INSTALL_NEMOCLAW=1 to install automatically)"
fi

if [ "$RUN_LOCKED_BUILD" = "1" ]; then
  need_cmd python3
  log "Running locked Lean diagnostics"
  python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
    InfoGeometry.Canonical.ProjectorEquivariance \
    InfoGeometry.Dynamics.UnruhKMS \
    InfoGeometry.Canonical.ModularSuperchargeClosure \
    | tee "logs/dgx_spark_locked_build_$(date -u +%Y%m%dT%H%M%SZ).log"
fi

log "Bootstrap complete"
