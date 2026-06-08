#!/usr/bin/env bash
# run_leansearch_safe.sh - local-first LeanSearch wrapper for repo agents.
#
# The reliable in-repo lane is `tools/infra/leansearch_local.py`, backed by
# `artifacts/leansearch_local/records.jsonl`. The legacy REAL-Prover HTTP server
# is still available, but only through the explicit `server` subcommand.

set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="${REPO_ROOT:-$(cd -- "$SCRIPT_DIR/.." && pwd)}"

LOCAL_PY="${LEANSEARCH_LOCAL_PY:-$REPO_ROOT/tools/infra/leansearch_local.py}"
DECLS_PATH="${LEANSEARCH_DECLS:-$REPO_ROOT/artifacts/dag/index/decls.jsonl}"
TYPES_PATH="${LEANSEARCH_TYPES:-$REPO_ROOT/artifacts/dag/index/types.jsonl}"
RECORDS_PATH="${LEANSEARCH_RECORDS:-$REPO_ROOT/artifacts/leansearch_local/records.jsonl}"

LEANSEARCH_DEVICE="${LEANSEARCH_DEVICE:-cuda}"
LEANSEARCH_MAX_LENGTH="${LEANSEARCH_MAX_LENGTH:-1024}"
LEANSEARCH_MAX_NUM="${LEANSEARCH_MAX_NUM:-8}"
LEANSEARCH_THREADED="${LEANSEARCH_THREADED:-0}"
LEANSEARCH_MAX_QUERY_CHARS="${LEANSEARCH_MAX_QUERY_CHARS:-8000}"
LEANSEARCH_DEFAULT_NUM="${LEANSEARCH_DEFAULT_NUM:-5}"
LEANSEARCH_HOST="${LEANSEARCH_HOST:-0.0.0.0}"

choose_python() {
  if [[ -n "${LEANSEARCH_PYTHON_BIN:-}" ]]; then
    printf '%s\n' "$LEANSEARCH_PYTHON_BIN"
    return
  fi
  if [[ -x "$REPO_ROOT/.venv-py312/bin/python" ]]; then
    printf '%s\n' "$REPO_ROOT/.venv-py312/bin/python"
    return
  fi
  if command -v python3 >/dev/null 2>&1; then
    command -v python3
    return
  fi
  printf 'Error: no Python interpreter found. Set LEANSEARCH_PYTHON_BIN.\n' >&2
  exit 1
}

PYTHON_BIN="$(choose_python)"

usage() {
  cat <<'EOF'
Usage:
  tools/run_leansearch_safe.sh search "query" [--top-k N] [--out path]
  tools/run_leansearch_safe.sh "query"
  tools/run_leansearch_safe.sh build
  tools/run_leansearch_safe.sh build-source --source-root PATH --out records.jsonl
  tools/run_leansearch_safe.sh health
  tools/run_leansearch_safe.sh server [server.py args...]

Modes:
  search  Query the deterministic local LeanSearch records. Default mode.
  build   Rebuild local records from DAG artifacts.
  build-source
          Build navigation-only records directly from Lean source roots.
  health  Check local wrapper inputs.
  server  Start the legacy REAL-Prover LeanSearch server explicitly.

Environment:
  LEANSEARCH_RECORDS     Local records JSONL path.
  LEANSEARCH_DECLS       DAG declarations JSONL path for build.
  LEANSEARCH_TYPES       DAG types JSONL path for build.
  LEANSEARCH_PYTHON_BIN  Python interpreter override.
EOF
}

require_file() {
  local path="$1"
  local label="$2"
  if [[ ! -f "$path" ]]; then
    printf 'Error: %s not found at %s\n' "$label" "$path" >&2
    return 1
  fi
}

run_local_search() {
  require_file "$LOCAL_PY" "local LeanSearch script"
  require_file "$RECORDS_PATH" "local LeanSearch records"
  exec "$PYTHON_BIN" "$LOCAL_PY" search "$@" --records "$RECORDS_PATH"
}

run_local_build() {
  require_file "$LOCAL_PY" "local LeanSearch script"
  require_file "$DECLS_PATH" "DAG declarations"
  require_file "$TYPES_PATH" "DAG types"
  exec "$PYTHON_BIN" "$LOCAL_PY" build \
    --decls "$DECLS_PATH" \
    --types "$TYPES_PATH" \
    --out "$RECORDS_PATH" \
    "$@"
}

run_source_build() {
  require_file "$LOCAL_PY" "local LeanSearch script"
  exec "$PYTHON_BIN" "$LOCAL_PY" build-source "$@"
}

run_health() {
  require_file "$LOCAL_PY" "local LeanSearch script"
  require_file "$RECORDS_PATH" "local LeanSearch records"
  require_file "$DECLS_PATH" "DAG declarations"
  require_file "$TYPES_PATH" "DAG types"
  printf 'leansearch_safe=ok\n'
  printf 'python=%s\n' "$PYTHON_BIN"
  printf 'local_py=%s\n' "$LOCAL_PY"
  printf 'records=%s\n' "$RECORDS_PATH"
  printf 'decls=%s\n' "$DECLS_PATH"
  printf 'types=%s\n' "$TYPES_PATH"
}

run_server() {
  export LEANSEARCH_DEVICE
  export LEANSEARCH_MAX_LENGTH
  export LEANSEARCH_MAX_NUM
  export LEANSEARCH_THREADED
  export LEANSEARCH_MAX_QUERY_CHARS
  export LEANSEARCH_DEFAULT_NUM
  export LEANSEARCH_HOST

  local real_root="${LEANSEARCH_REAL_PROVER_ROOT:-$REPO_ROOT/external_refs/REAL-Prover}"
  local server_py="${LEANSEARCH_SERVER_PY:-$real_root/LeanSearch-PS-inference/server.py}"
  local server_python="${LEANSEARCH_SERVER_PYTHON:-}"
  if [[ -z "$server_python" ]]; then
    if [[ -x "$REPO_ROOT/.venv-py312/bin/python" ]]; then
      server_python="$REPO_ROOT/.venv-py312/bin/python"
    else
      server_python="$real_root/.venv/bin/python"
    fi
  fi

  require_file "$server_python" "REAL-Prover Python binary"
  require_file "$server_py" "REAL-Prover LeanSearch server"

  printf '%s\n' '--------------------------------------------------------'
  printf '%s\n' 'Starting LeanSearch Inference Server (Hardened Profile)'
  printf '%s\n' '--------------------------------------------------------'
  printf 'Host:       %s\n' "$LEANSEARCH_HOST"
  printf 'Python:     %s\n' "$server_python"
  printf 'Device:     %s\n' "$LEANSEARCH_DEVICE"
  printf 'Max Length: %s\n' "$LEANSEARCH_MAX_LENGTH"
  printf 'Max Num:    %s\n' "$LEANSEARCH_MAX_NUM"
  printf 'Threaded:   %s\n' "$LEANSEARCH_THREADED"
  printf '%s\n' '--------------------------------------------------------'

  exec "$server_python" "$server_py" "$@"
}

if [[ $# -eq 0 ]]; then
  usage >&2
  exit 2
fi

case "$1" in
  -h|--help|help)
    usage
    ;;
  search|local)
    shift
    if [[ $# -eq 0 ]]; then
      printf 'Error: search mode requires a query.\n' >&2
      exit 2
    fi
    run_local_search "$@"
    ;;
  build|build-local)
    shift
    run_local_build "$@"
    ;;
  build-source|source-build)
    shift
    if [[ $# -eq 0 ]]; then
      printf 'Error: build-source mode requires --source-root PATH.\n' >&2
      exit 2
    fi
    run_source_build "$@"
    ;;
  health)
    shift
    if [[ $# -ne 0 ]]; then
      printf 'Error: health mode does not accept arguments.\n' >&2
      exit 2
    fi
    run_health
    ;;
  server|serve)
    shift
    run_server "$@"
    ;;
  *)
    query="$*"
    run_local_search "$query" --top-k "$LEANSEARCH_DEFAULT_NUM"
    ;;
esac
