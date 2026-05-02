#!/usr/bin/env bash
set -euo pipefail

# bwrap_preflight.sh
# Detects whether bubblewrap sandboxing is viable. If not, runs the command
# directly (fallback mode) unless --require-sandbox is set.
#
# Usage:
#   tools/infra/bwrap_preflight.sh -- bash -n tools/infra/hive_with_env.sh
#   tools/infra/bwrap_preflight.sh --require-sandbox -- <cmd...>

REQUIRE_SANDBOX=0
if [[ "${1:-}" == "--require-sandbox" ]]; then
  REQUIRE_SANDBOX=1
  shift
fi

if [[ "${1:-}" == "--" ]]; then
  shift
fi

if [[ $# -eq 0 ]]; then
  echo "usage: $0 [--require-sandbox] -- <command...>" >&2
  exit 2
fi

warn() { echo "[bwrap-preflight] $*" >&2; }

can_use_bwrap() {
  if ! command -v bwrap >/dev/null 2>&1; then
    warn "bwrap binary not found"
    return 1
  fi

  # Kernel user namespace checks (best-effort)
  if [[ -r /proc/sys/kernel/unprivileged_userns_clone ]]; then
    local v
    v=$(cat /proc/sys/kernel/unprivileged_userns_clone 2>/dev/null || echo "")
    if [[ "$v" != "1" ]]; then
      warn "kernel.unprivileged_userns_clone=$v (expected 1)"
      return 1
    fi
  fi

  if [[ -r /proc/sys/user/max_user_namespaces ]]; then
    local n
    n=$(cat /proc/sys/user/max_user_namespaces 2>/dev/null || echo "0")
    if [[ "$n" == "0" ]]; then
      warn "user.max_user_namespaces=0"
      return 1
    fi
  fi

  # Functional probe
  if ! bwrap --unshare-pid --ro-bind /usr /usr --ro-bind /bin /bin --ro-bind /lib /lib --ro-bind /lib64 /lib64 --dev /dev --proc /proc /bin/true >/dev/null 2>&1; then
    warn "bwrap functional probe failed (Operation not permitted / policy / seccomp?)"
    return 1
  fi

  return 0
}

if can_use_bwrap; then
  warn "sandbox mode: enabled"
  exec bwrap --unshare-pid --ro-bind /usr /usr --ro-bind /bin /bin --ro-bind /lib /lib --ro-bind /lib64 /lib64 --dev /dev --proc /proc --ro-bind "$(pwd)" "$(pwd)" --chdir "$(pwd)" "$@"
else
  if [[ "$REQUIRE_SANDBOX" -eq 1 ]]; then
    warn "sandbox required but unavailable"
    exit 3
  fi
  warn "sandbox mode: unavailable, falling back to direct execution"
  exec "$@"
fi
