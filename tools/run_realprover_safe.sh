#!/usr/bin/env bash
# run_realprover_safe.sh - deterministic REAL-Prover entrypoint for repo agents.

set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="${REPO_ROOT:-$(cd -- "$SCRIPT_DIR/.." && pwd)}"

REALPROVER_ROOT="${REALPROVER_ROOT:-$REPO_ROOT/external_refs/REAL-Prover}"
REALPROVER_DIR="${REALPROVER_DIR:-$REALPROVER_ROOT/Realprover}"
REALPROVER_PYTHON="${REALPROVER_PYTHON:-$REPO_ROOT/.venv-py312/bin/python}"

export REALPROVER_MODEL_PATH="${REALPROVER_MODEL_PATH:-/home/goutev/models/frenzymath/REAL-Prover-model}"
export REALPROVER_LEANSEARCH_URL="${REALPROVER_LEANSEARCH_URL:-http://127.0.0.1:18080/retrieve_premises}"
export REALPROVER_LEAN_TEST_PATH="${REALPROVER_LEAN_TEST_PATH:-$REPO_ROOT}"
export REALPROVER_INTERACTIVE_PATH="${REALPROVER_INTERACTIVE_PATH:-$REPO_ROOT/external_refs/interactive}"
export REALPROVER_LEAN_ENV_PATH="${REALPROVER_LEAN_ENV_PATH:-$HOME/.elan/bin}"
readonly REALPROVER_EXPECTED_TOOLCHAIN="leanprover/lean4:v4.28.0"

usage() {
  cat <<'EOF'
Usage:
  tools/run_realprover_safe.sh health
  tools/run_realprover_safe.sh run path/to/config.toml

Modes:
  health  Verify local REAL-Prover source, model, LeanSearch URL config, and execution deps.
  run     Run REAL-Prover experiment.run with the supplied TOML config.

Environment:
  REALPROVER_ROOT              REAL-Prover checkout path; default repo/external_refs/REAL-Prover.
  REALPROVER_PYTHON            Python runtime; default repo/.venv-py312/bin/python.
  REALPROVER_MODEL_PATH        HF model snapshot path; default FrenzyMath/REAL-Prover local mirror.
  REALPROVER_LEANSEARCH_URL    LeanSearch-PS endpoint; default http://127.0.0.1:18080/retrieve_premises.
  REALPROVER_LEAN_TEST_PATH    Lean workspace; default repo root, pinned to Lean 4.28.0.
  REALPROVER_INTERACTIVE_PATH  interactive submodule; default external_refs/interactive.
  REALPROVER_LEAN_ENV_PATH     elan bin path; default ~/.elan/bin.
  REALPROVER_EXPECTED_TOOLCHAIN is intentionally fixed by this wrapper to leanprover/lean4:v4.28.0.
EOF
}

require_file() {
  local path="$1"
  local label="$2"
  if [[ ! -f "$path" ]]; then
    printf 'Error: %s not found at %s\n' "$label" "$path" >&2
    exit 1
  fi
}

require_dir() {
  local path="$1"
  local label="$2"
  if [[ ! -d "$path" ]]; then
    printf 'Error: %s not found at %s\n' "$label" "$path" >&2
    exit 1
  fi
}

read_toolchain() {
  local path="$1"
  sed -n '1p' "$path"
}

require_toolchain() {
  local path="$1"
  local label="$2"
  local actual
  actual="$(read_toolchain "$path/lean-toolchain")"
  if [[ "$actual" != "$REALPROVER_EXPECTED_TOOLCHAIN" ]]; then
    printf 'Error: %s toolchain is %s, expected %s\n' \
      "$label" "$actual" "$REALPROVER_EXPECTED_TOOLCHAIN" >&2
    exit 1
  fi
}

health() {
  require_file "$REALPROVER_PYTHON" "REAL-Prover Python"
  require_dir "$REALPROVER_DIR" "REAL-Prover package"
  require_dir "$REALPROVER_MODEL_PATH" "REAL-Prover model"
  require_file "$REALPROVER_MODEL_PATH/config.json" "REAL-Prover model config"
  require_file "$REALPROVER_MODEL_PATH/model.safetensors.index.json" "REAL-Prover model weights index"
  require_dir "$REALPROVER_LEAN_TEST_PATH" "REAL-Prover Lean workspace"
  require_file "$REALPROVER_LEAN_TEST_PATH/lean-toolchain" "REAL-Prover Lean workspace toolchain"
  require_dir "$REALPROVER_INTERACTIVE_PATH" "REAL-Prover interactive dependency"
  require_file "$REALPROVER_INTERACTIVE_PATH/lean-toolchain" "REAL-Prover interactive toolchain"
  require_dir "$REALPROVER_LEAN_ENV_PATH" "Lean environment bin"
  require_toolchain "$REALPROVER_LEAN_TEST_PATH" "REAL-Prover Lean workspace"
  require_toolchain "$REALPROVER_INTERACTIVE_PATH" "REAL-Prover interactive dependency"

  (
    cd "$REALPROVER_DIR"
    "$REALPROVER_PYTHON" -c '
import importlib.util
import sys
from pathlib import Path
import conf.config as c

mods = ["torch", "transformers", "vllm", "requests"]
missing = [m for m in mods if importlib.util.find_spec(m) is None]
if missing:
    raise SystemExit(f"missing Python modules: {missing}")

lean_search = c.API_CONFIG["lean_search"]
print("realprover_safe=ok")
print(f"python={Path(sys.executable)}")
print(f"realprover_root={c.REALPROVER_ROOT}")
print(f"prover_model_path={c.PROVER_MODEL_PATH}")
print(f"lean_search={lean_search}")
print(f"lean_test_path={c.LEAN_TEST_PATH}")
print(f"interactive_path={c.interactive_path}")
print(f"lean_env_path={c.LEAN_ENV_PATH}")
print("expected_toolchain=leanprover/lean4:v4.28.0")
'
  )
}

run_experiment() {
  if [[ $# -ne 1 ]]; then
    printf 'Error: run mode requires exactly one TOML config path.\n' >&2
    exit 2
  fi
  local config_path="$1"
  require_file "$config_path" "REAL-Prover experiment config"
  health >/dev/null
  cd "$REALPROVER_DIR"
  exec "$REALPROVER_PYTHON" -m experiment.run "$config_path"
}

if [[ $# -eq 0 ]]; then
  usage >&2
  exit 2
fi

case "$1" in
  -h|--help|help)
    usage
    ;;
  health)
    shift
    if [[ $# -ne 0 ]]; then
      printf 'Error: health mode does not accept arguments.\n' >&2
      exit 2
    fi
    health
    ;;
  run)
    shift
    run_experiment "$@"
    ;;
  *)
    printf 'Error: unknown mode %s\n' "$1" >&2
    usage >&2
    exit 2
    ;;
esac
