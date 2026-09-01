#!/usr/bin/env bash
set -euo pipefail

# bwrap_preflight.sh
# Detects whether bubblewrap sandboxing is viable. If not, runs the command
# directly (fallback mode) unless --require-sandbox is set.
#
# Usage:
#   tools/infra/bwrap_preflight.sh -- bash -n tools/infra/hive_with_env.sh
#   tools/infra/bwrap_preflight.sh --require-sandbox -- <cmd...>
#   tools/infra/bwrap_preflight.sh --hint
#   tools/infra/bwrap_preflight.sh --hint -- bash -n tools/infra/hive_with_env.sh
#   tools/infra/bwrap_preflight.sh --hint-json
#   tools/infra/bwrap_preflight.sh --hint-json -- bash -n tools/infra/hive_with_env.sh

REQUIRE_SANDBOX=0
HINT_ONLY=0
HINT_JSON=0
HINT_EVAL_NO_CMD=0
BWRAP_FAILURE_REASON=""
BWRAP_REMEDIATION_POLICY_COMMAND=""
BWRAP_REMEDIATION_DEBUG_ENV=""
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

while [[ $# -gt 0 ]]; do
  case "${1:-}" in
    --require-sandbox)
      REQUIRE_SANDBOX=1
      shift
      ;;
    --hint)
      HINT_ONLY=1
      shift
      ;;
    --hint-json)
      HINT_JSON=1
      HINT_ONLY=1
      shift
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

if [[ $# -eq 0 ]]; then
  if [[ "$HINT_ONLY" -eq 0 ]]; then
    echo "usage: $0 [--require-sandbox] [--hint|--hint-json] -- <command...>" >&2
    exit 2
  fi
  HINT_EVAL_NO_CMD=1
fi

warn() { echo "[bwrap-preflight] $*" >&2; }
print_hint() {
  local reason="$1"
  warn "hint: bwrap preflight diagnostics"
  warn "  require-sandbox: $REQUIRE_SANDBOX"
  warn "  hint: $reason"
  warn "  BWRAP_EXTRA_ARGS: ${BWRAP_EXTRA_ARGS:-<unset>}"
  warn "  fallback: enabled by default unless --require-sandbox is used"
  if [[ -n "${KERNEL_APPARMOR_RESTRICT_USERNS:-}" ]]; then
    warn "  kernel.apparmor_restrict_unprivileged_userns=${KERNEL_APPARMOR_RESTRICT_USERNS}"
    if [[ "$KERNEL_APPARMOR_RESTRICT_USERNS" == "1" ]]; then
      warn "  host note: unprivileged user namespaces are restricted by AppArmor by policy"
      warn "  temporary admin workaround: sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0"
    fi
  fi
  warn "  op examples: BWRAP_EXTRA_ARGS='--share-net' for temporary local-loopback tests"
  warn "  op examples: BWRAP_EXTRA_ARGS='--bind /proc /proc' for controlled mount tuning"
  warn "  policy note: configure sandbox to allow loopback when RTM_NEWADDR is denied"
  warn "  policy example: <sandbox policy command> --allow-loopback"
}

set_host_remediation() {
  local reason="$1"
  case "$reason" in
    apparmor_userns)
      BWRAP_REMEDIATION_POLICY_COMMAND="Kernel/AppArmor policy: temporary admin command required"
      BWRAP_REMEDIATION_DEBUG_ENV="sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0"
      ;;
    uid_map_permission_denied)
      BWRAP_REMEDIATION_POLICY_COMMAND="Kernel/AppArmor policy and/or user-namespace privileges are required"
      BWRAP_REMEDIATION_DEBUG_ENV="BWRAP_EXTRA_ARGS='--share-net'"
      ;;
    loopback_restriction)
      BWRAP_REMEDIATION_POLICY_COMMAND="nemoclaw policy-add --allow-loopback"
      BWRAP_REMEDIATION_DEBUG_ENV="BWRAP_EXTRA_ARGS='--share-net'"
      ;;
    *)
      BWRAP_REMEDIATION_POLICY_COMMAND=""
      BWRAP_REMEDIATION_DEBUG_ENV=""
      ;;
  esac
}

json_escape() {
  local input="${1:-}"
  input="${input//\\/\\\\}"
  input="${input//\"/\\\"}"
  input="${input//$'\n'/\\n}"
  input="${input//$'\r'/}"
  input="${input//$'\t'/\\t}"
  printf '%s' "$input"
}

print_hint_json() {
  local sandbox_ready="$1"
  local fallback_active="$2"
  local sandbox_ready_val="false"
  local fallback_active_val="false"
  local reason_field='null'
  local policy_field='null'
  local debug_field='null'

  if [[ "$sandbox_ready" -eq 1 ]]; then
    sandbox_ready_val="true"
  fi
  if [[ "$fallback_active" -eq 1 ]]; then
    fallback_active_val="true"
  fi
  if [[ -n "$BWRAP_FAILURE_REASON" ]]; then
    reason_field="\"$(json_escape "$BWRAP_FAILURE_REASON")\""
  fi
  if [[ -n "$BWRAP_REMEDIATION_POLICY_COMMAND" ]]; then
    policy_field="\"$(json_escape "$BWRAP_REMEDIATION_POLICY_COMMAND")\""
  fi
  if [[ -n "$BWRAP_REMEDIATION_DEBUG_ENV" ]]; then
    debug_field="\"$(json_escape "$BWRAP_REMEDIATION_DEBUG_ENV")\""
  fi

  cat <<EOF
{
  "sandbox_ready": ${sandbox_ready_val},
  "failure_reason": ${reason_field},
  "fallback_active": ${fallback_active_val},
  "remediation": {
    "policy_command": ${policy_field},
    "debug_env": ${debug_field}
  }
}
EOF
}

net_warning() {
  warn "detected sandbox network/loopback limitation (kernel/AppArmor policy may block RTM_NEWADDR)"
  warn "recommended OpenShell/NemoClaw action: allow loopback networking in sandbox policy"
  warn "example: <sandbox policy command> policy-add --allow-loopback"
  warn "quick temporary test workaround: BWRAP_EXTRA_ARGS=\"--share-net\" (or --loopback if supported)"
  if [[ -n "${KERNEL_APPARMOR_RESTRICT_USERNS:-}" && "$KERNEL_APPARMOR_RESTRICT_USERNS" == "1" ]]; then
    warn "temporary host workaround: sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0"
  fi
}

collect_bwrap_args() {
  local -n _dest="$1"
  _dest=()
  if [[ -n "${BWRAP_EXTRA_ARGS:-}" ]]; then
    # shellcheck disable=SC2206
    _dest=(${BWRAP_EXTRA_ARGS})
  fi
}

probe_temp_file() {
  local probe_file=""
  local dir_candidates=(
    "${TMPDIR:-}"
    "/tmp"
    "/var/tmp"
    "/dev/shm"
    "${REPO_ROOT}"
    "${PWD}"
    "${HOME}"
  )
  local dir
  for dir in "${dir_candidates[@]}"; do
    [[ -z "${dir}" ]] && continue
    [[ -d "${dir}" && -w "${dir}" ]] || continue
    probe_file="$(mktemp -p "${dir}" bwrap-preflight.XXXXXX 2>/dev/null || true)"
    if [[ -n "${probe_file}" ]]; then
      printf '%s\n' "${probe_file}"
      return 0
    fi
  done
  printf '%s\n' "/tmp/bwrap-preflight.err"
}

classify_bwrap_failure() {
  local msg="$1"
  if [[ "$msg" == *"RTM_NEWADDR"* ]] \
    || [[ "$msg" == *"loopback"* ]] \
    || [[ "$msg" == *"Network is down"* ]] \
    || [[ "$msg" == *"Network unreachable"* ]] \
    || [[ "$msg" == *"cannot access network"* ]]; then
    echo "loopback_restriction"
    return 0
  fi
  if [[ "$msg" == *"setting up uid map: Permission denied"* ]] \
    || [[ "$msg" == *"uid map"* ]] \
    || [[ "$msg" == *"unshare: Operation not permitted"* ]] \
    || [[ "$msg" == *"setns: Operation not permitted"* ]]; then
    echo "uid_map_permission_denied"
    return 0
  fi
  if [[ "$msg" == *"apparmor"* ]] \
    || [[ "$msg" == *"AppArmor"* ]] \
    || [[ "$msg" == *"kernel.apparmor_restrict_unprivileged_userns"* ]]; then
    echo "apparmor_userns"
    return 0
  fi
  echo ""
  return 1
}

can_use_bwrap() {
  local -a extra_args
  local probe_err
  local msg
  local -a ro_bind_args=()
  local dir
  local home_elan="${HOME}/.elan"
  local home_choo="${HOME}/.choo"
  collect_bwrap_args extra_args

  if ! command -v bwrap >/dev/null 2>&1; then
    warn "bwrap binary not found"
    BWRAP_FAILURE_REASON="bwrap_not_found"
    BWRAP_REMEDIATION_POLICY_COMMAND=""
    BWRAP_REMEDIATION_DEBUG_ENV=""
    return 1
  fi

  if [[ -r /proc/sys/kernel/unprivileged_userns_clone ]]; then
    local v
    v=$(cat /proc/sys/kernel/unprivileged_userns_clone 2>/dev/null || echo "")
    if [[ "$v" != "1" ]]; then
      warn "kernel.unprivileged_userns_clone=$v (expected 1)"
      BWRAP_FAILURE_REASON="user_namespace_disabled"
      BWRAP_REMEDIATION_POLICY_COMMAND=""
      BWRAP_REMEDIATION_DEBUG_ENV=""
      return 1
    fi
  fi

  if [[ -r /proc/sys/user/max_user_namespaces ]]; then
    local n
    n=$(cat /proc/sys/user/max_user_namespaces 2>/dev/null || echo "0")
    if [[ "$n" == "0" ]]; then
      warn "user.max_user_namespaces=0"
      BWRAP_FAILURE_REASON="max_user_namespaces_zero"
      BWRAP_REMEDIATION_POLICY_COMMAND=""
      BWRAP_REMEDIATION_DEBUG_ENV=""
      return 1
    fi
  fi

  KERNEL_APPARMOR_RESTRICT_USERNS=""
  if [[ -r /proc/sys/kernel/apparmor_restrict_unprivileged_userns ]]; then
    KERNEL_APPARMOR_RESTRICT_USERNS=$(cat /proc/sys/kernel/apparmor_restrict_unprivileged_userns 2>/dev/null || echo "")
  fi

  ro_bind_args=(--ro-bind /usr /usr --ro-bind /lib /lib)
  for dir in /bin /sbin /lib64 /usr/lib64 /lib32 /usr/lib32; do
    [[ -d "${dir}" ]] && ro_bind_args+=(--ro-bind "${dir}" "${dir}")
  done
  [[ -d /tmp ]] && ro_bind_args+=(--tmpfs /tmp)
  [[ -d "${home_elan}" ]] && ro_bind_args+=(--ro-bind "${home_elan}" "${home_elan}")
  [[ -d "${home_choo}" ]] && ro_bind_args+=(--ro-bind "${home_choo}" "${home_choo}")
  [[ -d "${HOME}" ]] && ro_bind_args+=(--ro-bind "${HOME}" "${HOME}")
  [[ -e /etc/localtime ]] && ro_bind_args+=(--ro-bind /etc/localtime /etc/localtime)
  [[ -e /etc/timezone ]] && ro_bind_args+=(--ro-bind /etc/timezone /etc/timezone)

  probe_err="$(probe_temp_file)"
  : > "${probe_err}" 2>/dev/null || { probe_err="/dev/null"; }
  if ! bwrap --unshare-pid "${extra_args[@]}" \
      "${ro_bind_args[@]}" \
      --dev /dev \
      --proc /proc \
      /usr/bin/true \
      >/dev/null 2>"$probe_err"; then
    msg="$(tr -d '\n\r' < "$probe_err")"
    rm -f "$probe_err"

    if [[ -n "$KERNEL_APPARMOR_RESTRICT_USERNS" && "$KERNEL_APPARMOR_RESTRICT_USERNS" == "1" ]]; then
      BWRAP_FAILURE_REASON="apparmor_userns"
      set_host_remediation "$BWRAP_FAILURE_REASON"
      warn "apparent AppArmor user-namespace restriction detected: kernel.apparmor_restrict_unprivileged_userns=1"
      return 2
    fi

    if [[ -n "$msg" ]]; then
      local failure_class
      failure_class="$(classify_bwrap_failure "$msg")"
      if [[ -z "$failure_class" ]]; then
        BWRAP_FAILURE_REASON="sandbox_probe_failure"
        BWRAP_REMEDIATION_POLICY_COMMAND=""
        BWRAP_REMEDIATION_DEBUG_ENV=""
        warn "bwrap functional probe failed (Operation not permitted / policy / seccomp?)"
        warn "$msg"
        return 1
      fi
      BWRAP_FAILURE_REASON="$failure_class"
      set_host_remediation "$failure_class"
      warn "bwrap failure class: $failure_class"
      warn "bwrap network-related probe failed: $msg"
      warn "fallback: running without sandbox"
      return 2
    fi

    warn "bwrap functional probe failed (operation returned no diagnostics)"
    BWRAP_FAILURE_REASON="sandbox_probe_failure"
    BWRAP_REMEDIATION_POLICY_COMMAND=""
    BWRAP_REMEDIATION_DEBUG_ENV=""
    return 1
  fi
  rm -f "$probe_err"

  return 0
}

if [[ "$HINT_EVAL_NO_CMD" -eq 1 ]]; then
  if can_use_bwrap; then
    if [[ "$HINT_JSON" -eq 1 ]]; then
      print_hint_json 1 0
    else
      print_hint "sandbox probe: available"
    fi
    exit 0
  else
    status=$?
    fallback_active=1
    if [[ "$REQUIRE_SANDBOX" -eq 1 ]]; then
      fallback_active=0
    fi
    if [[ "$HINT_JSON" -eq 1 ]]; then
      print_hint_json 0 "$fallback_active"
      exit 2
    fi
    case "$status" in
      2)
        print_hint "sandbox probe: network/loopback restricted; direct fallback available"
        ;;
      *)
        print_hint "sandbox probe: unavailable; direct fallback available"
        ;;
    esac
    exit 2
  fi
fi

if can_use_bwrap; then
  if [[ "$HINT_ONLY" -eq 1 ]]; then
    if [[ "$HINT_JSON" -eq 1 ]]; then
      print_hint_json 1 0
      if [[ $# -eq 0 ]]; then
        exit 0
      fi
    else
      print_hint "sandbox probe: available"
    fi
  fi
  warn "sandbox mode: enabled"
  collect_bwrap_args bwrap_args
  bwrap_args_exec=(--ro-bind /usr /usr --ro-bind /lib /lib)
  for dir in /bin /sbin /lib64 /usr/lib64 /lib32 /usr/lib32; do
    [[ -d "${dir}" ]] && bwrap_args_exec+=("--ro-bind" "${dir}" "${dir}")
  done
  bwrap_args_exec+=(--tmpfs /tmp)
  [[ -d "${HOME}" ]] && bwrap_args_exec+=(--ro-bind "${HOME}" "${HOME}")
  [[ -d "${HOME}/.elan" ]] && bwrap_args_exec+=(--ro-bind "${HOME}/.elan" "${HOME}/.elan")
  [[ -d "${HOME}/.choo" ]] && bwrap_args_exec+=(--ro-bind "${HOME}/.choo" "${HOME}/.choo")
  [[ -e /etc/localtime ]] && bwrap_args_exec+=(--ro-bind /etc/localtime /etc/localtime)
  [[ -e /etc/timezone ]] && bwrap_args_exec+=(--ro-bind /etc/timezone /etc/timezone)
  exec bwrap --unshare-pid "${bwrap_args[@]}" \
    "${bwrap_args_exec[@]}" \
    --dev /dev \
    --proc /proc \
    --bind "$(pwd)" "$(pwd)" \
    --chdir "$(pwd)" \
    "$@"
else
  status=$?
  fallback_active=1
  if [[ "$REQUIRE_SANDBOX" -eq 1 ]]; then
    fallback_active=0
  fi
  if [[ "$status" -eq 2 ]]; then
    if [[ "$HINT_ONLY" -eq 1 ]]; then
      if [[ "$HINT_JSON" -eq 1 ]]; then
        print_hint_json 0 "$fallback_active"
      else
        print_hint "sandbox probe: network/loopback restricted"
      fi
    fi
    net_warning
  elif [[ "$HINT_ONLY" -eq 1 ]]; then
    if [[ "$HINT_JSON" -eq 1 ]]; then
      print_hint_json 0 "$fallback_active"
    else
      print_hint "sandbox probe: unavailable"
    fi
  fi
  if [[ "$REQUIRE_SANDBOX" -eq 1 ]]; then
    warn "sandbox required but unavailable"
    exit 3
  fi
  warn "sandbox mode: unavailable, falling back to direct execution"
  exec "$@"
fi
