#!/usr/bin/env bash
set -euo pipefail

PINNED_COMMIT="b2af3f63d20a29e1a0ebfbceec048b0f59668b49"
REPO_URL="https://github.com/Alishahryar1/free-claude-code.git"
PYTHON_VERSION="${FCC_PINNED_PYTHON_VERSION:-3.14.0}"
DEFAULT_MODEL="${FCC_MODEL:-open_router/openrouter/free}"

DRY_RUN=0
WRITE_CONFIG=1
FORCE_CONFIG=0

usage() {
  cat <<'USAGE'
Usage: scripts/install_free_claude_code_pinned.sh [options]

Install Free Claude Code from a reviewed, pinned Git commit.

Options:
  --dry-run        Print commands without executing them.
  --no-config      Install only; do not create ~/.fcc/.env.
  --force-config   Replace ~/.fcc/.env with the safe pinned template.
  --help           Show this help text.

Environment:
  FCC_MODEL                    Default MODEL for the generated config.
  FCC_PINNED_PYTHON_VERSION    Python version uv should install. Default: 3.14.0.
  FCC_ENV_FILE                 Override the config file path. Default: ~/.fcc/.env.

This wrapper intentionally does not install or update Claude Code, Codex, npm,
or uv. Install those separately if they are missing.
USAGE
}

quote_arg() {
  printf "%q" "$1"
}

run() {
  printf "+"
  for arg in "$@"; do
    printf " "
    quote_arg "$arg"
  done
  printf "\n"
  if [ "$DRY_RUN" -eq 0 ]; then
    "$@"
  fi
}

fail() {
  printf "error: %s\n" "$*" >&2
  exit 1
}

need_command() {
  command -v "$1" >/dev/null 2>&1 || fail "$1 is required on PATH"
}

token() {
  python3 - <<'PY'
import secrets

print("fcc-" + secrets.token_urlsafe(24))
PY
}

write_safe_config() {
  local env_file="${FCC_ENV_FILE:-$HOME/.fcc/.env}"
  local env_dir
  env_dir="$(dirname "$env_file")"

  if [ -e "$env_file" ] && [ "$FORCE_CONFIG" -eq 0 ]; then
    printf "Config already exists at %s; leaving it untouched.\n" "$env_file"
    return 0
  fi

  local auth_token
  if [ "$DRY_RUN" -eq 0 ]; then
    auth_token="$(token)"
  else
    auth_token="fcc-dry-run-token"
  fi

  printf "+ install -m 700 -d "
  quote_arg "$env_dir"
  printf "\n"
  if [ "$DRY_RUN" -eq 0 ]; then
    install -m 700 -d "$env_dir"
  fi

  printf "+ write pinned safe FCC config to "
  quote_arg "$env_file"
  printf "\n"
  if [ "$DRY_RUN" -eq 0 ]; then
    umask 077
    local tmp
    tmp="${env_file}.tmp.$$"
    cat >"$tmp" <<EOF
# Created by scripts/install_free_claude_code_pinned.sh
# Upstream: ${REPO_URL}
# Commit: ${PINNED_COMMIT}

HOST="127.0.0.1"
PORT=8082
ANTHROPIC_AUTH_TOKEN="${auth_token}"
FCC_OPEN_BROWSER=false

# Default route. Set OPENROUTER_API_KEY or change MODEL to a local provider,
# for example MODEL="ollama/llama3.1" with a running Ollama server.
MODEL="${DEFAULT_MODEL}"
MODEL_OPUS=
MODEL_SONNET=
MODEL_HAIKU=

OPENROUTER_API_KEY=""
GEMINI_API_KEY=""
DEEPSEEK_API_KEY=""
MISTRAL_API_KEY=""
CODESTRAL_API_KEY=""
GROQ_API_KEY=""
CEREBRAS_API_KEY=""
NVIDIA_NIM_API_KEY=""
KIMI_API_KEY=""
WAFER_API_KEY=""
OPENCODE_API_KEY=""
ZAI_API_KEY=""
FIREWORKS_API_KEY=""

LM_STUDIO_BASE_URL="http://localhost:1234/v1"
LLAMACPP_BASE_URL="http://localhost:8080/v1"
OLLAMA_BASE_URL="http://localhost:11434"

MESSAGING_PLATFORM="none"
VOICE_NOTE_ENABLED=false

ENABLE_MODEL_THINKING=true
PROVIDER_RATE_LIMIT=1
PROVIDER_RATE_WINDOW=3
PROVIDER_MAX_CONCURRENCY=3
HTTP_READ_TIMEOUT=300
HTTP_WRITE_TIMEOUT=60
HTTP_CONNECT_TIMEOUT=60

# Keep outbound web tools off unless explicitly needed.
ENABLE_WEB_SERVER_TOOLS=false
WEB_FETCH_ALLOWED_SCHEMES=http,https
WEB_FETCH_ALLOW_PRIVATE_NETWORKS=false

# Keep raw content logging off. Structured trace logs may still contain prompt
# snapshots in FCC itself, so treat ~/.fcc/logs as sensitive.
DEBUG_PLATFORM_EDITS=false
DEBUG_SUBAGENT_STACK=false
LOG_RAW_API_PAYLOADS=false
LOG_RAW_SSE_EVENTS=false
LOG_API_ERROR_TRACEBACKS=false
LOG_RAW_MESSAGING_CONTENT=false
LOG_RAW_CLI_DIAGNOSTICS=false
LOG_MESSAGING_ERROR_DETAILS=false
EOF
    mv "$tmp" "$env_file"
    chmod 600 "$env_file"
  fi
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --dry-run)
      DRY_RUN=1
      ;;
    --no-config)
      WRITE_CONFIG=0
      ;;
    --force-config)
      FORCE_CONFIG=1
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      usage >&2
      fail "unknown option: $1"
      ;;
  esac
  shift
done

need_command uv
need_command python3
need_command claude
need_command codex

SPEC="free-claude-code @ git+${REPO_URL}@${PINNED_COMMIT}"

run uv python install "$PYTHON_VERSION"
run uv tool install --force "$SPEC"

if [ "$WRITE_CONFIG" -eq 1 ]; then
  write_safe_config
fi

cat <<EOF

Free Claude Code is pinned to:
  ${PINNED_COMMIT}

Start the proxy:
  scripts/fcc_server_local.sh

Then launch clients through the proxy:
  scripts/fcc_claude_local.sh
  scripts/fcc_codex_local.sh

For Claude MCP delegation through Codex, change the codex MCP command to
scripts/fcc_codex_local.sh only after the FCC server is running.
EOF
