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
RUN_ID="$(date -u +%Y%m%dT%H%M%SZ)"
BUILD_LOG_PATH="logs/dgx_spark_locked_build_${RUN_ID}.log"
RUNTIME_LOCK_PATH="logs/hermes_runtime_lock_${RUN_ID}.json"
BUILD_STATUS="skipped"
BUILD_EXIT_CODE=0
LOCKED_MODULES="InfoGeometry.Canonical.ProjectorEquivariance,InfoGeometry.Dynamics.UnruhKMS,InfoGeometry.Canonical.ModularSuperchargeClosure"

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
  if python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
      InfoGeometry.Canonical.ProjectorEquivariance \
      InfoGeometry.Dynamics.UnruhKMS \
      InfoGeometry.Canonical.ModularSuperchargeClosure \
      | tee "$BUILD_LOG_PATH"; then
    BUILD_STATUS="success"
  else
    BUILD_STATUS="failure"
    BUILD_EXIT_CODE=$?
  fi
fi

log "Collecting runtime lock manifest"
OPENCLAW_VERSION="$(openclaw --version 2>/dev/null | head -n1 || true)"
NEMOCLAW_VERSION="$(nemoclaw --version 2>/dev/null | head -n1 || true)"
LEAN_VERSION="$(lean --version 2>/dev/null | head -n1 || true)"
LAKE_VERSION="$(lake --version 2>/dev/null | head -n1 || true)"
PYTHON_VERSION="$(python3 --version 2>/dev/null | head -n1 || true)"
DOCKER_VERSION="$(docker --version 2>/dev/null | head -n1 || true)"
OLLAMA_VERSION="$(ollama --version 2>/dev/null | head -n1 || true)"
GIT_HEAD="$(git rev-parse HEAD 2>/dev/null || true)"
GIT_BRANCH="$(git rev-parse --abbrev-ref HEAD 2>/dev/null || true)"

HERMES_BASE_URL="$(awk '/base_url:/{gsub(/"/, "", $2); print $2; exit}' tools/infra/hermes_config.yaml 2>/dev/null || true)"
HERMES_MODEL="$(awk '/default:/{gsub(/"/, "", $2); print $2; exit}' tools/infra/hermes_config.yaml 2>/dev/null || true)"
DISCOVERY_BASE_URL="$(awk '/discovery_engine:/{f=1;next}/logic_engine:/{f=0}f&&/base_url:/{gsub(/"/, "", $2); print $2; exit}' nemoclaw_config.yaml 2>/dev/null || true)"
DISCOVERY_MODEL="$(awk '/discovery_engine:/{f=1;next}/logic_engine:/{f=0}f&&/model:/{gsub(/"/, "", $2); print $2; exit}' nemoclaw_config.yaml 2>/dev/null || true)"
LOGIC_BASE_URL="$(awk '/logic_engine:/{f=1;next}/code_engine:/{f=0}f&&/base_url:/{gsub(/"/, "", $2); print $2; exit}' nemoclaw_config.yaml 2>/dev/null || true)"
LOGIC_MODEL="$(awk '/logic_engine:/{f=1;next}/code_engine:/{f=0}f&&/model:/{gsub(/"/, "", $2); print $2; exit}' nemoclaw_config.yaml 2>/dev/null || true)"
NEMOCLAW_RESOLVE_BASE_URL="${NEMOCLAW_RESOLVE_BASE_URL:-${LEANSTRAL_BASE_URL:-${HERMES_BASE_URL:-http://127.0.0.1:18889/v1}}}"
LEANSTRAL_BASE_URL="${LEANSTRAL_BASE_URL:-${LOGIC_BASE_URL:-${NEMOCLAW_RESOLVE_BASE_URL}}}"

NEMOCLAW_MODEL_RESOLUTION_ENV="$(mktemp)"
if python3 tools/infra/resolve_startup_model_ids.py \
  --base-url "${NEMOCLAW_RESOLVE_BASE_URL}" \
  --archon-config ".archon/config.yaml" \
  --nemoclaw-config "nemoclaw_config.yaml" \
  --format env > "$NEMOCLAW_MODEL_RESOLUTION_ENV" 2>/tmp/nemoclaw_model_resolution.log; then
  # shellcheck disable=SC1090
  set -a
  source "$NEMOCLAW_MODEL_RESOLUTION_ENV"
  set +a
  if [[ -n "${NEMOCLAW_LOGIC_ENGINE_MODEL:-}" ]]; then
    LOGIC_MODEL="${NEMOCLAW_LOGIC_ENGINE_MODEL}"
  fi
  if [[ -n "${NEMOCLAW_DISCOVERY_ENGINE_MODEL:-}" ]]; then
    DISCOVERY_MODEL="${NEMOCLAW_DISCOVERY_ENGINE_MODEL}"
  fi
  if [[ -n "${NEMOCLAW_PLANNER_ENGINE_MODEL:-}" ]]; then
    export NEMOCLAW_PLANNER_ENGINE_MODEL
  fi
fi
rm -f "$NEMOCLAW_MODEL_RESOLUTION_ENV"

export RUN_ID RUNTIME_LOCK_PATH ROOT_DIR BUILD_STATUS BUILD_EXIT_CODE BUILD_LOG_PATH LOCKED_MODULES
export OPENCLAW_VERSION NEMOCLAW_VERSION LEAN_VERSION LAKE_VERSION PYTHON_VERSION DOCKER_VERSION OLLAMA_VERSION GIT_HEAD GIT_BRANCH
export HERMES_BASE_URL HERMES_MODEL DISCOVERY_BASE_URL DISCOVERY_MODEL LOGIC_BASE_URL LOGIC_MODEL

python3 - <<'PY'
import json
import os
from datetime import datetime, timezone
from fnmatch import fnmatch


def env(name: str) -> str:
    return os.environ.get(name, "")


def collect_nemoclaw_lane_models() -> dict[str, str]:
    out: dict[str, str] = {}
    for key, value in os.environ.items():
        if fnmatch(key, "NEMOCLAW_LANE_*_MODEL"):
            lane = key[len("NEMOCLAW_LANE_") : -len("_MODEL")].lower()
            out[lane] = value
    return out


modules = [m.strip() for m in env("LOCKED_MODULES").split(",") if m.strip()]

payload = {
    "schema": "hermes_runtime_lock.v1",
    "generated_at_utc": datetime.now(timezone.utc).isoformat(),
    "run_id": env("RUN_ID"),
    "workspace_root": env("ROOT_DIR"),
    "git": {
        "branch": env("GIT_BRANCH"),
        "head": env("GIT_HEAD"),
    },
    "versions": {
        "openclaw": env("OPENCLAW_VERSION"),
        "nemoclaw": env("NEMOCLAW_VERSION"),
        "lean": env("LEAN_VERSION"),
        "lake": env("LAKE_VERSION"),
        "python": env("PYTHON_VERSION"),
        "docker": env("DOCKER_VERSION"),
        "ollama": env("OLLAMA_VERSION"),
    },
    "model_endpoints": {
        "hermes": {"base_url": env("HERMES_BASE_URL"), "model": env("HERMES_MODEL")},
        "discovery_engine": {"base_url": env("DISCOVERY_BASE_URL"), "model": env("DISCOVERY_MODEL")},
        "logic_engine": {"base_url": env("LOGIC_BASE_URL"), "model": env("LOGIC_MODEL")},
    },
    "resolved_lane_models": {
        "archon": {"leanstral": env("ARCHON_LEANSTRAL_MODEL")},
        "nemoclaw": collect_nemoclaw_lane_models(),
    },
    "locked_build": {
        "status": env("BUILD_STATUS"),
        "exit_code": int(env("BUILD_EXIT_CODE") or "0"),
        "modules": modules,
        "log_path": env("BUILD_LOG_PATH"),
    },
}

out_path = env("RUNTIME_LOCK_PATH")
with open(out_path, "w", encoding="utf-8") as f:
    json.dump(payload, f, indent=2, sort_keys=True)
    f.write("\n")
PY

log "Wrote runtime lock manifest: $RUNTIME_LOCK_PATH"

if [ "$BUILD_EXIT_CODE" -ne 0 ]; then
  log "Locked build failed; see $BUILD_LOG_PATH and $RUNTIME_LOCK_PATH"
  exit "$BUILD_EXIT_CODE"
fi

log "Bootstrap complete"
