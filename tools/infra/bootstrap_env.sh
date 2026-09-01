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

# The root Lake package records Atlas as a local external reference for local
# research workflows. Clean CI checkouts do not carry that checkout, so hydrate
# its audited revision before Lake reads the package configuration. GIFT is now
# a small vendored compatibility package in the repository itself; only hydrate
# a historical external checkout when that local package is absent.
if [[ "${ci_mode}" == "--ci" ]]; then
  mkdir -p "${repo_root}/external_refs"

  if [[ ! -d "${repo_root}/external_refs/atlas-lean/.git" ]]; then
    echo "[sandbox-bootstrap] hydrating pinned Atlas external dependency"
    git clone --no-checkout https://github.com/facebookresearch/atlas-lean.git \
      "${repo_root}/external_refs/atlas-lean"
    git -C "${repo_root}/external_refs/atlas-lean" checkout \
      34ffed396f376454c1a9b297f3fd74c5c801fb50
  fi

  if [[ ! -f "${repo_root}/external_refs/gift-framework-core/lakefile.lean" ]]; then
    echo "[sandbox-bootstrap] vendored GIFT package missing; attempting historical hydration"
    rm -rf "${repo_root}/external_refs/gift-framework-core"
    git clone --no-checkout https://github.com/gift-framework/core.git \
      "${repo_root}/external_refs/gift-framework-core"
    git -C "${repo_root}/external_refs/gift-framework-core" fetch origin \
      e6f3c3ac2140c2324fb2ae029c32233e73aa5e92 || true
    git -C "${repo_root}/external_refs/gift-framework-core" checkout \
      e6f3c3ac2140c2324fb2ae029c32233e73aa5e92
  fi
fi

# GitHub's hosted image does not necessarily ship bubblewrap. The CI policy
# prefers the sandbox when it is available and already permits direct fallback
# when the host kernel disallows it, so install the userspace binary when
# possible rather than treating its absence as a policy violation.
if [[ "${ci_mode}" == "--ci" ]] && ! command -v bwrap >/dev/null 2>&1; then
  echo "[sandbox-bootstrap] installing bubblewrap for CI preflight"
  sudo apt-get update -qq
  sudo apt-get install -y -qq bubblewrap
fi

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
