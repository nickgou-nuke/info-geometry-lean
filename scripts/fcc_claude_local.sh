#!/usr/bin/env bash
set -euo pipefail

export HOST="${FCC_HOST:-127.0.0.1}"
export FCC_OPEN_BROWSER="${FCC_OPEN_BROWSER:-false}"

if [ "${FCC_ALLOW_OPENROUTER_ENV:-0}" != "1" ]; then
  unset OPENROUTER_API_KEY
fi

default_model="${FCC_CLAUDE_MODEL:-anthropic/nvidia_nim/nvidia/nemotron-3-nano-30b-a3b}"
has_model_arg=0
for arg in "$@"; do
  if [ "$arg" = "--model" ]; then
    has_model_arg=1
    break
  fi
done

if [ "$has_model_arg" -eq 1 ]; then
  exec fcc-claude "$@"
fi

exec fcc-claude --model "$default_model" "$@"
