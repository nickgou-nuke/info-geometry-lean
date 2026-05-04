#!/usr/bin/env bash
set -euo pipefail

# Bootstrap sandbox wrappers for Python/Lean/Lake toolchains.
# Usage:
#   source tools/infra/bootstrap_env.sh
#   # or (CI):
#   source tools/infra/bootstrap_env.sh --ci

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"
sandbox_dir="${repo_root}/tools/infra/sandbox-bin"
ci_mode="${1:-}"

resolve_command() {
  local cmd="$1"
  local original_path="${PATH:-}"
  local filtered_path=""
  local sep=""
  local p

  IFS=':' read -r -a _path_entries <<<"${original_path}"
  for p in "${_path_entries[@]}"; do
    [[ -z "${p}" ]] && continue
    if [[ "${p}" != "${sandbox_dir}" ]]; then
      filtered_path="${filtered_path}${sep}${p}"
      sep=":"
    fi
  done

  local candidate=""
  candidate="$(PATH="${filtered_path}" command -v "${cmd}" 2>/dev/null || true)"
  if [[ -n "${candidate}" && ( ! "${candidate}" == */* || -x "${candidate}" ) ]]; then
    echo "${candidate}"
    return 0
  fi

  candidate="$(command -v "${cmd}" 2>/dev/null || true)"
  if [[ -n "${candidate}" && "${candidate}" != "${sandbox_dir}/${cmd}" && ( ! "${candidate}" == */* || -x "${candidate}" ) ]]; then
    echo "${candidate}"
    return 0
  fi

  return 1
}

host_python="$(resolve_command python3)"
if [[ -z "${host_python:-}" ]]; then
  host_python="$(resolve_command python)"
fi
host_lean="$(resolve_command lean)"
if [[ -z "${host_lean:-}" ]]; then
  host_lean="lean"
fi
host_lake="$(resolve_command lake)"
if [[ -z "${host_lake:-}" ]]; then
  host_lake="lake"
fi

if [[ ! -d "${sandbox_dir}" ]]; then
  echo "[sandbox-bootstrap] missing directory: ${sandbox_dir}" >&2
  return 2 2>/dev/null || exit 2
fi

chmod +x \
  "${sandbox_dir}/python" \
  "${sandbox_dir}/python3" \
  "${sandbox_dir}/lean" \
  "${sandbox_dir}/lean4" \
  "${sandbox_dir}/lake"

if [[ ":${PATH}:" != *":${sandbox_dir}:"* ]]; then
  export PATH="${sandbox_dir}:${PATH}"
fi

export BWRAP_PYTHON_WRAPPER_MODE="${BWRAP_PYTHON_WRAPPER_MODE:-sandbox}"
export BWRAP_LEAN_WRAPPER_MODE="${BWRAP_LEAN_WRAPPER_MODE:-sandbox}"
export BWRAP_LAKE_WRAPPER_MODE="${BWRAP_LAKE_WRAPPER_MODE:-sandbox}"
export BWRAP_PYTHON_BIN="${BWRAP_PYTHON_BIN:-${host_python:-python3}}"
export BWRAP_LEAN_BIN="${BWRAP_LEAN_BIN:-${host_lean:-lean}}"
export BWRAP_LAKE_BIN="${BWRAP_LAKE_BIN:-${host_lake:-lake}}"
export BWRAP_REQUIRE_SANDBOX="${BWRAP_REQUIRE_SANDBOX:-0}"

echo "[sandbox-bootstrap] enabled ${sandbox_dir} in PATH"
echo "[sandbox-bootstrap] mode: python=${BWRAP_PYTHON_WRAPPER_MODE}, lean=${BWRAP_LEAN_WRAPPER_MODE}, lake=${BWRAP_LAKE_WRAPPER_MODE}"
echo "[sandbox-bootstrap] BWRAP_REQUIRE_SANDBOX=${BWRAP_REQUIRE_SANDBOX}"

if [[ "${ci_mode}" == "--ci" && -n "${GITHUB_PATH:-}" ]]; then
  echo "${sandbox_dir}" >> "${GITHUB_PATH}"
  {
    echo "BWRAP_PYTHON_WRAPPER_MODE=${BWRAP_PYTHON_WRAPPER_MODE}"
    echo "BWRAP_LEAN_WRAPPER_MODE=${BWRAP_LEAN_WRAPPER_MODE}"
    echo "BWRAP_LAKE_WRAPPER_MODE=${BWRAP_LAKE_WRAPPER_MODE}"
    echo "BWRAP_PYTHON_BIN=${BWRAP_PYTHON_BIN}"
    echo "BWRAP_LEAN_BIN=${BWRAP_LEAN_BIN}"
    echo "BWRAP_LAKE_BIN=${BWRAP_LAKE_BIN}"
    echo "BWRAP_REQUIRE_SANDBOX=${BWRAP_REQUIRE_SANDBOX}"
  } >> "${GITHUB_ENV}"
fi
