#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
ARCHON_ROOT="$REPO_ROOT/tools/archon"

export INFO_GEOMETRY_RUNTIME_DIR="${INFO_GEOMETRY_RUNTIME_DIR:-$REPO_ROOT/.runtime}"
export ARCHON_HOME="${ARCHON_HOME:-$INFO_GEOMETRY_RUNTIME_DIR/archon-home}"
export PI_RUNTIME_HOME="${PI_RUNTIME_HOME:-$INFO_GEOMETRY_RUNTIME_DIR/pi-home}"
mkdir -p "$ARCHON_HOME" "$PI_RUNTIME_HOME"

if [ -z "${DEEPSEEK_API_KEY:-}" ] && [ -f "$REPO_ROOT/.DEEPSEEK_API_KEY" ]; then
  # shellcheck source=/dev/null
  source "$REPO_ROOT/.DEEPSEEK_API_KEY"
fi

cd "$ARCHON_ROOT"
exec env HOME="$PI_RUNTIME_HOME" \
  bun run cli workflow run agent-orchestrator-definite-sequence \
  --cwd "$REPO_ROOT" \
  "$@"
