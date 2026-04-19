#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage:
  tools/infra/run_gemini_guarded.sh --check
  tools/infra/run_gemini_guarded.sh --reason "operator request" -- gemini <args...>

Policy:
  Agents must not call gemini directly. This wrapper enforces the repo-local
  irregular-dreaming guard before one explicit Gemini CLI invocation and records
  usage only after the Gemini command succeeds.
USAGE
}

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
GUARD="${REPO_ROOT}/tools/infra/gemini_cli_guard.py"
GUARD_STATE="${GEMINI_GUARD_STATE:-}"
PYTHON_BIN="${PYTHON_BIN:-python3}"
read -r -a PYTHON_CMD <<< "${PYTHON_BIN}"
REASON="explicit operator request"
OPERATOR="${USER:-operator}"
CHECK_ONLY=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --check)
      CHECK_ONLY=1
      shift
      ;;
    --reason)
      if [[ $# -lt 2 ]]; then
        echo "missing value for --reason" >&2
        usage >&2
        exit 64
      fi
      REASON="$2"
      shift 2
      ;;
    --operator)
      if [[ $# -lt 2 ]]; then
        echo "missing value for --operator" >&2
        usage >&2
        exit 64
      fi
      OPERATOR="$2"
      shift 2
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    --)
      shift
      break
      ;;
    *)
      break
      ;;
  esac
done

if [[ "${CHECK_ONLY}" == "1" ]]; then
  if [[ -n "${GUARD_STATE}" ]]; then
    exec "${PYTHON_CMD[@]}" "${GUARD}" --state "${GUARD_STATE}" --check --json
  fi
  exec "${PYTHON_CMD[@]}" "${GUARD}" --check --json
fi

if [[ $# -eq 0 ]]; then
  echo "missing Gemini command; use -- gemini <args...>" >&2
  usage >&2
  exit 64
fi

if [[ "$1" != "gemini" ]]; then
  echo "refusing to run non-gemini command through Gemini guard: $1" >&2
  exit 64
fi

if [[ -n "${GUARD_STATE}" ]]; then
  "${PYTHON_CMD[@]}" "${GUARD}" --state "${GUARD_STATE}" --check --json >/dev/null
else
  "${PYTHON_CMD[@]}" "${GUARD}" --check --json >/dev/null
fi
"$@"
if [[ -n "${GUARD_STATE}" ]]; then
  "${PYTHON_CMD[@]}" "${GUARD}" --state "${GUARD_STATE}" --reason "${REASON}" --operator "${OPERATOR}" --json >/dev/null
else
  "${PYTHON_CMD[@]}" "${GUARD}" --reason "${REASON}" --operator "${OPERATOR}" --json >/dev/null
fi
