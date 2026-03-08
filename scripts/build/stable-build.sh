#!/usr/bin/env bash
set -euo pipefail

# Backward-compatible canonical entrypoint now generalized to full-project default.
exec "$(dirname "$0")/stable-canonical.sh" "$@"
