#!/usr/bin/env bash
set -euo pipefail

# Backward-compatible canonical entrypoint using the incremental stable wrapper.
# Pass an explicit target (or --all-default-targets through the underlying
# wrapper) when a release-style umbrella build is required.
exec "$(dirname "$0")/stable-canonical.sh" "$@"
