#!/usr/bin/env bash
set -euo pipefail
exec "$(cd "$(dirname "$0")" && pwd)/with_arango_env.sh" -- antigravity "$@"
