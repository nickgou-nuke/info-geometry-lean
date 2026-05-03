#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage:
  tools/infra/run_gemini_guarded.sh --check
  tools/infra/run_gemini_guarded.sh --reason "operator request" -- gemini <args...>
  tools/infra/run_gemini_guarded.sh --loop-burst --reason "bounded Socratic loop" -- gemini <args...>

Policy:
  Agents must not call gemini directly. This wrapper enforces the repo-local
  guard before explicit Gemini CLI invocation and records usage only after the
  Gemini command succeeds.

Special mode:
  --loop-burst is for bounded operator-requested multi-round Gemini sessions
  (for example Socratic Gemini→Codex→Gemini loops). It skips the irregular
  inter-call interval for that explicit bounded loop, but still records usage
  and keeps the daily limit.
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
LOOP_BURST=0
MIN_INTERVAL_SECONDS="${GEMINI_GUARD_MIN_INTERVAL_SECONDS:-}"
MAX_CALLS_PER_DAY="${GEMINI_GUARD_MAX_CALLS_PER_DAY:-}"
JITTER_SECONDS="${GEMINI_GUARD_JITTER_SECONDS:-}"

build_guard_args() {
  local -a guard_args=()
  if [[ -n "${GUARD_STATE}" ]]; then
    guard_args+=(--state "${GUARD_STATE}")
  fi
  if [[ -n "${MIN_INTERVAL_SECONDS}" ]]; then
    guard_args+=(--min-interval-seconds "${MIN_INTERVAL_SECONDS}")
  fi
  if [[ -n "${MAX_CALLS_PER_DAY}" ]]; then
    guard_args+=(--max-calls-per-day "${MAX_CALLS_PER_DAY}")
  fi
  if [[ -n "${JITTER_SECONDS}" ]]; then
    guard_args+=(--jitter-seconds "${JITTER_SECONDS}")
  fi
  if [[ ${#guard_args[@]} -gt 0 ]]; then
    printf '%s\n' "${guard_args[@]}"
  fi
}

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
    --loop-burst)
      LOOP_BURST=1
      shift
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

if [[ "${LOOP_BURST}" == "1" ]]; then
  MIN_INTERVAL_SECONDS=0
  JITTER_SECONDS=0
fi

mapfile -t GUARD_ARGS < <(build_guard_args)
if [[ "${LOOP_BURST}" == "1" ]]; then
  GUARD_ARGS+=(--allow-burst)
fi

if [[ "${CHECK_ONLY}" == "1" ]]; then
  exec "${PYTHON_CMD[@]}" "${GUARD}" "${GUARD_ARGS[@]}" --check --json
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

"${PYTHON_CMD[@]}" "${GUARD}" "${GUARD_ARGS[@]}" --check --json >/dev/null
"$@"
"${PYTHON_CMD[@]}" "${GUARD}" "${GUARD_ARGS[@]}" --reason "${REASON}" --operator "${OPERATOR}" --json >/dev/null
