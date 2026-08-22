#!/usr/bin/env bash
set -euo pipefail

# Source this file before running frenzymath Archon to route fallback LLM calls
# to OpenRouter (OpenAI-compatible endpoint).
# Usage:
#   source /home/goutev/repos/info-geometry-lean/tools/infra/archon_openrouter_env.sh
#   archon loop /path/to/project --stage autoformalize --max-iterations 5 --no-dashboard

if [[ -z "${OPENROUTER_API_KEY:-}" ]]; then
  echo "OPENROUTER_API_KEY is not set. Export it first." >&2
  return 1 2>/dev/null || exit 1
fi

export ARCHON_SKIP_CLAUDE_PREFLIGHT=1
export ARCHON_LLM_BASE_URL="https://openrouter.ai/api/v1"
export ARCHON_LLM_API_KEY="${OPENROUTER_API_KEY}"
export ARCHON_LLM_MODEL="${ARCHON_LLM_MODEL:-openrouter/stealth/ox-alpha}"
export OPENAI_BASE_URL="https://openrouter.ai/api/v1"
export OPENAI_API_KEY="${OPENROUTER_API_KEY}"

# Optional OpenRouter headers
if [[ -n "${OPENROUTER_HTTP_REFERER:-}" ]]; then
  export OR_SITE_URL="${OPENROUTER_HTTP_REFERER}"
fi
if [[ -n "${OPENROUTER_X_TITLE:-}" ]]; then
  export OR_APP_NAME="${OPENROUTER_X_TITLE}"
fi

echo "Archon fallback configured: ${ARCHON_LLM_BASE_URL} model=${ARCHON_LLM_MODEL}"