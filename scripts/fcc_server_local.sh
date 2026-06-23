#!/usr/bin/env bash
set -euo pipefail

export HOST="${FCC_HOST:-127.0.0.1}"
export FCC_OPEN_BROWSER="${FCC_OPEN_BROWSER:-false}"

if [ "${FCC_ALLOW_OPENROUTER_ENV:-0}" != "1" ]; then
  unset OPENROUTER_API_KEY
fi

exec fcc-server "$@"
