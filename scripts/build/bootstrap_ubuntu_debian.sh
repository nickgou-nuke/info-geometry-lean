#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/build/bootstrap_ubuntu_debian.sh [options]

End-to-end bootstrap for Ubuntu/Debian:
- installs system prerequisites (apt)
- installs Lean via elan/lake
- installs Lake dependencies and mathlib cache
- creates .venv and installs repo Python tooling
- runs core Lean builds and strict check

Options:
  --with-infra         Install scientific Python deps and run full infra refresh pipeline
  --skip-apt           Skip apt-get install/update steps
  --skip-strict-check  Skip 'lake script run strictCheck'
  --dry-run            Print commands without executing
  -h, --help           Show this help
EOF
}

log() {
  printf '[bootstrap] %s\n' "$*"
}

run_cmd() {
  log "$*"
  if [[ "$DRY_RUN" -eq 1 ]]; then
    return 0
  fi
  "$@"
}

run_shell() {
  log "$*"
  if [[ "$DRY_RUN" -eq 1 ]]; then
    return 0
  fi
  bash -lc "$*"
}

ensure_debian_family() {
  if [[ ! -r /etc/os-release ]]; then
    echo "error: cannot read /etc/os-release to detect distro" >&2
    exit 1
  fi

  # shellcheck disable=SC1091
  . /etc/os-release

  case "${ID:-}" in
    ubuntu|debian)
      return 0
      ;;
  esac

  if [[ "${ID_LIKE:-}" == *debian* ]]; then
    return 0
  fi

  echo "error: this script is tailored for Ubuntu/Debian (detected: ${ID:-unknown})" >&2
  exit 1
}

SKIP_APT=0
SKIP_STRICT_CHECK=0
WITH_INFRA=0
DRY_RUN=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --with-infra)
      WITH_INFRA=1
      ;;
    --skip-apt)
      SKIP_APT=1
      ;;
    --skip-strict-check)
      SKIP_STRICT_CHECK=1
      ;;
    --dry-run)
      DRY_RUN=1
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown option: $1" >&2
      usage
      exit 1
      ;;
  esac
  shift
done

ensure_debian_family

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$REPO_ROOT"

log "Repository root: $REPO_ROOT"

APT_PREFIX=()
if [[ "$SKIP_APT" -eq 0 ]]; then
  if ! command -v apt-get >/dev/null 2>&1; then
    echo "error: apt-get not found; use --skip-apt if prerequisites are already installed" >&2
    exit 1
  fi

  if [[ "${EUID:-$(id -u)}" -ne 0 ]]; then
    if command -v sudo >/dev/null 2>&1; then
      APT_PREFIX=(sudo)
    else
      echo "error: apt requires root or sudo; install deps manually or run as root" >&2
      exit 1
    fi
  fi

  BASE_PACKAGES=(
    ca-certificates
    curl
    git
    python3
    python3-pip
    python3-venv
    ripgrep
  )

  run_cmd "${APT_PREFIX[@]}" apt-get update
  run_cmd "${APT_PREFIX[@]}" apt-get install -y "${BASE_PACKAGES[@]}"

  if [[ "$WITH_INFRA" -eq 1 ]]; then
    run_cmd "${APT_PREFIX[@]}" apt-get install -y graphviz
  fi
else
  log "Skipping apt dependency install"
fi

if ! command -v lake >/dev/null 2>&1 && [[ ! -x "$HOME/.elan/bin/lake" ]]; then
  run_shell "curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y"
fi

export PATH="$HOME/.elan/bin:$PATH"

if ! command -v lake >/dev/null 2>&1; then
  echo "error: lake not found after elan bootstrap" >&2
  exit 1
fi

if command -v elan >/dev/null 2>&1; then
  TOOLCHAIN="$(tr -d '[:space:]' < lean-toolchain)"
  if [[ -n "$TOOLCHAIN" ]]; then
    run_cmd elan toolchain install "$TOOLCHAIN"
  fi
fi

run_cmd lake --version
run_cmd lake update

log "Attempting mathlib cache download"
if [[ "$DRY_RUN" -eq 1 ]]; then
  log "lake exe cache get"
else
  if ! lake exe cache get; then
    log "Warning: 'lake exe cache get' failed; continuing with source build"
  fi
fi

run_cmd python3 -m venv .venv
VENV_PY="$REPO_ROOT/.venv/bin/python"

if [[ "$DRY_RUN" -eq 0 && ! -x "$VENV_PY" ]]; then
  echo "error: expected virtualenv python at $VENV_PY" >&2
  exit 1
fi

run_cmd "$VENV_PY" -m pip install --upgrade pip
run_cmd "$VENV_PY" -m pip install -e .

if [[ "$WITH_INFRA" -eq 1 ]]; then
  run_cmd "$VENV_PY" -m pip install networkx matplotlib numpy scipy
fi

export PATH="$REPO_ROOT/.venv/bin:$PATH"

run_cmd "$VENV_PY" tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.All
run_cmd "$VENV_PY" tools/infra/run_locked_lake_build.py InfoGeometry.All
run_cmd "$VENV_PY" tools/infra/run_locked_lake_build.py InfoGeometry.Audit

if [[ "$SKIP_STRICT_CHECK" -eq 0 ]]; then
  run_cmd lake script run strictCheck
else
  log "Skipping strictCheck"
fi

if [[ "$WITH_INFRA" -eq 1 ]]; then
  run_cmd "$VENV_PY" tools/infra/refresh_decl_graph.py
  run_cmd "$VENV_PY" tools/infra/refresh_blueprint_tags.py
  run_cmd "$VENV_PY" tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
  run_cmd "$VENV_PY" tools/infra/generate_theorem_surface_index.py
  run_cmd "$VENV_PY" tools/infra/generate_source_sink_compression.py
  run_cmd "$VENV_PY" tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json
  run_cmd "$VENV_PY" tools/infra/check_bipartite_bleed.py
  run_cmd "$VENV_PY" tools/infra/generate_structural_dedup.py
  run_cmd "$VENV_PY" tools/infra/generate_structural_fibers.py
  run_cmd "$VENV_PY" tools/infra/generate_semantic_quotient.py
  run_cmd "$VENV_PY" tools/infra/generate_projection_coloring.py
  run_cmd "$VENV_PY" tools/infra/select_openclaw_target.py
  run_cmd "$VENV_PY" tools/infra/canonical_policy_lint.py
  run_cmd "$VENV_PY" tools/infra/generate_replacement_frontier.py
  run_cmd "$VENV_PY" tools/theorem_significance.py
  run_cmd "$VENV_PY" tools/infra/causal_cone_spectrum.py
  run_cmd "$VENV_PY" tools/infra/apex_defect_profile.py
  run_cmd "$VENV_PY" tools/infra/graph_hodge_spectrum.py
  run_cmd "$VENV_PY" tools/infra/check_representation_depth.py
  run_cmd "$VENV_PY" tools/infra/generate_representation_depth_graph.py
fi

log "Bootstrap complete"
log "In a new shell, activate the environment with: source .venv/bin/activate"