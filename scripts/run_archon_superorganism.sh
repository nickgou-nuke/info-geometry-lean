#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

usage() {
  cat <<'EOF'
Usage: ./scripts/run_archon_superorganism.sh [--iterations N] [--parallel N] [--project PATH] [--dashboard]

Start Archon on the bee-hive orchestration graph.
Defaults:
  iterations=1
  parallel=4
  project=$ROOT_DIR
  dashboard enabled when --dashboard is passed

Environment:
  LEANSTRAL_BASE_URL  Override default Leanstral endpoint (default: http://127.0.0.1:18889/v1)
  OPENROUTER_PI_MODEL Override the pi assistant OpenRouter model (example: openrouter/qwen/qwen3-coder:free).
  If unset, model comes from .archon/config.yaml or the resolver output.
  OPENROUTER_API_KEY  Required when Pi or Hermes use OpenRouter; set via env or .archon/.env.
  ARCHON_SKIP_CLAUDE_PREFLIGHT=1 to skip the preflight API key check
  ARCHON_SKIP_TITLE_GENERATION=1 to skip Claude title generation calls (recommended for local PI-only loops)
  DATABASE_URL  Override Archon DB path (defaults to sqlite:////tmp/archon-workflow-<user>.db)
EOF
}

ITERATIONS=1
PARALLEL=4
PROJECT="."
DASHBOARD_FLAG="--no-dashboard"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --iterations)
      ITERATIONS="${2:?missing --iterations value}"
      shift 2
      ;;
    --parallel)
      PARALLEL="${2:?missing --parallel value}"
      shift 2
      ;;
    --project)
      PROJECT="${2:?missing --project value}"
      shift 2
      ;;
    --dashboard)
      DASHBOARD_FLAG=""
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "Unknown argument: $1" >&2
      usage
      exit 1
      ;;
  esac
done

if ! command -v archon >/dev/null 2>&1; then
  echo "ERROR: archon command not found. Install Archon or ensure it is in PATH." >&2
  exit 1
fi

ARCHON_STARTUP_ARCHON_CONFIG="${ARCHON_STARTUP_ARCHON_CONFIG:-.archon/config.yaml}"
ARCHON_STARTUP_NEMOCLAW_CONFIG="${ARCHON_STARTUP_NEMOCLAW_CONFIG:-nemoclaw_config.yaml}"
export DATABASE_URL="${DATABASE_URL:-sqlite:////tmp/archon-workflow-${USER:-user}.db}"
OPENROUTER_PI_MODEL="${OPENROUTER_PI_MODEL:-}"
export OPENROUTER_PI_MODEL

if [[ ! -f .archon/PROGRESS.md ]]; then
  echo "WARN: .archon/PROGRESS.md missing; Archon may fail policy checks." >&2
fi

export ARCHON_SKIP_CLAUDE_PREFLIGHT="${ARCHON_SKIP_CLAUDE_PREFLIGHT:-true}"
LEANSTRAL_BASE_URL="${LEANSTRAL_BASE_URL:-http://127.0.0.1:18889/v1}"
export LEANSTRAL_BASE_URL

MODEL_KEYS=(
  ARCHON_LEANSTRAL_MODEL
  NEMOCLAW_PLANNER_ENGINE_MODEL
  NEMOCLAW_LOGIC_ENGINE_MODEL
  NEMOCLAW_DISCOVERY_ENGINE_MODEL
  NEMOCLAW_LANE_PLANNER_ENGINE_MODEL
  NEMOCLAW_LANE_LOGIC_ENGINE_MODEL
  NEMOCLAW_LANE_DISCOVERY_ENGINE_MODEL
  NEMOCLAW_LANE_ARCHON_LEANSTRAL_MODEL
)

set_default_model_id_values() {
  : "${ARCHON_LEANSTRAL_MODEL:=leanstral-gguf}"
  : "${NEMOCLAW_PLANNER_ENGINE_MODEL:=leanstral-gguf}"
  : "${NEMOCLAW_LOGIC_ENGINE_MODEL:=leanstral-gguf}"
  : "${NEMOCLAW_DISCOVERY_ENGINE_MODEL:=leanstral-gguf}"
  : "${NEMOCLAW_LANE_PLANNER_ENGINE_MODEL:=$NEMOCLAW_PLANNER_ENGINE_MODEL}"
  : "${NEMOCLAW_LANE_LOGIC_ENGINE_MODEL:=$NEMOCLAW_LOGIC_ENGINE_MODEL}"
  : "${NEMOCLAW_LANE_DISCOVERY_ENGINE_MODEL:=$NEMOCLAW_DISCOVERY_ENGINE_MODEL}"
  : "${NEMOCLAW_LANE_ARCHON_LEANSTRAL_MODEL:=$ARCHON_LEANSTRAL_MODEL}"
  export ARCHON_LEANSTRAL_MODEL
  export NEMOCLAW_PLANNER_ENGINE_MODEL
  export NEMOCLAW_LOGIC_ENGINE_MODEL
  export NEMOCLAW_DISCOVERY_ENGINE_MODEL
  export NEMOCLAW_LANE_PLANNER_ENGINE_MODEL
  export NEMOCLAW_LANE_LOGIC_ENGINE_MODEL
  export NEMOCLAW_LANE_DISCOVERY_ENGINE_MODEL
  export NEMOCLAW_LANE_ARCHON_LEANSTRAL_MODEL
}

export_model_env_keys() {
  for key in "${MODEL_KEYS[@]}"; do
    if [[ -n "${!key-}" ]]; then
      export "$key"
    fi
  done
  for key in $(compgen -A variable 'ARCHON_*_MODEL'); do
    export "$key"
  done
  for key in $(compgen -A variable 'NEMOCLAW_*_MODEL'); do
    export "$key"
  done
}

apply_config_fallback_models() {
  local fallback_file=$1
  if python3 tools/infra/resolve_startup_model_ids.py \
    --base-url "$LEANSTRAL_BASE_URL" \
    --archon-config "$ARCHON_STARTUP_ARCHON_CONFIG" \
    --nemoclaw-config "$ARCHON_STARTUP_NEMOCLAW_CONFIG" \
    --defaults-only \
    --format env > "$fallback_file" 2>/tmp/archon_model_defaults_resolution.log; then
    if apply_resolved_model_env_file "$fallback_file"; then
      set_default_model_id_values
      export_model_env_keys
      echo "Resolved startup model IDs from local startup defaults:"
      cat "$fallback_file"
      return 0
    fi
  fi
  return 1
}

apply_resolved_model_env_file() {
  local source_file=$1
  local line key raw value unquoted
  local saw_valid=1

  while IFS= read -r line; do
    if [[ "$line" =~ ^[[:space:]]*$ || "$line" =~ ^[[:space:]]*# ]]; then
      continue
    fi
    if [[ "$line" =~ ^([A-Za-z_][A-Za-z0-9_]*)=(.*)$ ]]; then
      key="${BASH_REMATCH[1]}"
      raw="${BASH_REMATCH[2]}"
      unquoted="$raw"
      if [[ ${#unquoted} -ge 2 ]]; then
        if [[ "${unquoted:0:1}" == "'" && "${unquoted: -1}" == "'" ]]; then
          unquoted="${unquoted:1:-1}"
        elif [[ "${unquoted:0:1}" == "\"" && "${unquoted: -1}" == "\"" ]]; then
          unquoted="${unquoted:1:-1}"
        fi
      fi
      if [[ -n "$key" ]]; then
        export "$key"="$unquoted"
        saw_valid=0
      fi
    fi
  done < "$source_file"

  return "$saw_valid"
}

MODEL_RESOLUTION_ENV="$(mktemp)"
  if python3 tools/infra/resolve_startup_model_ids.py \
  --base-url "$LEANSTRAL_BASE_URL" \
  --archon-config "$ARCHON_STARTUP_ARCHON_CONFIG" \
  --nemoclaw-config "$ARCHON_STARTUP_NEMOCLAW_CONFIG" \
  --format env > "$MODEL_RESOLUTION_ENV" 2>/tmp/archon_model_resolution.log; then
  if apply_resolved_model_env_file "$MODEL_RESOLUTION_ENV"; then
    set_default_model_id_values
    export_model_env_keys
    echo "Resolved startup model IDs:"
    cat "$MODEL_RESOLUTION_ENV"
  else
    echo "WARN: model alias resolution output was not usable (see /tmp/archon_model_resolution.log). Falling back to raw configured model IDs." >&2
    if ! apply_config_fallback_models "$MODEL_RESOLUTION_ENV"; then
      echo "WARN: startup default model resolution failed. Falling back to hardcoded defaults." >&2
      set_default_model_id_values
    fi
  fi
else
  echo "WARN: model alias resolution failed (see /tmp/archon_model_resolution.log). Falling back to raw configured model IDs." >&2
  if ! apply_config_fallback_models "$MODEL_RESOLUTION_ENV"; then
    echo "WARN: startup default model resolution failed. Falling back to hardcoded defaults." >&2
    set_default_model_id_values
    export_model_env_keys
  fi
fi
export_model_env_keys
if [[ -n "${OPENROUTER_PI_MODEL}" ]]; then
  export ARCHON_PI_MODEL="$OPENROUTER_PI_MODEL"
fi
export_model_env_keys
rm -f "$MODEL_RESOLUTION_ENV"

echo "Checking Leanstral endpoint (${LEANSTRAL_BASE_URL})..."
if python3 tools/infra/check_resident_model_endpoint.py \
  --base-url "$LEANSTRAL_BASE_URL" \
  --expected-model "${ARCHON_LEANSTRAL_MODEL}" \
  --timeout 5 \
  --json-out /tmp/archon_leanstral_probe.json \
  >/tmp/archon_leanstral_probe.log 2>&1; then
  echo "Leanstral endpoint OK."
else
  echo "WARN: Leanstral health check failed. Review /tmp/archon_leanstral_probe.log and /tmp/archon_leanstral_probe.json."
fi

# Avoid Claude title-generation fallback during local orchestration loops.
export ARCHON_SKIP_TITLE_GENERATION="${ARCHON_SKIP_TITLE_GENERATION:-true}"

echo "Starting Archon:"
echo "  project: $PROJECT"
echo "  iterations: $ITERATIONS"
echo "  parallel: $PARALLEL"
echo "  dashboard: $([[ -n "$DASHBOARD_FLAG" ]] && echo no || echo yes)"

exec archon loop \
  --max-iterations "$ITERATIONS" \
  --max-parallel "$PARALLEL" \
  $DASHBOARD_FLAG \
  "$PROJECT"
