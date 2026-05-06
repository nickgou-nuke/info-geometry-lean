#!/usr/bin/env bash
set -euo pipefail

# Compatibility wrapper: the resident planner lane has moved from Qwen to
# Leanstral. Keep this path so existing systemd units or operator muscle memory
# do not silently launch the old model. Override LEANSTRAL_* variables as needed.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec "$SCRIPT_DIR/leanstral_vllm_service.sh" "$@"
