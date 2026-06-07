#!/usr/bin/env bash
# Google AI Mode search — browser-harness-only lane.
# Usage: ./scripts/google-ai-search.sh "query string"
#   Does not use aiClaw. It attaches to the browser-harness/Chromium CDP lane
#   and records observations into the agent message ledger.

set -euo pipefail

QUERY="$*"
if [ -z "$QUERY" ]; then
    echo "Usage: $0 <search query>"
    echo "  Searches Google AI Mode via browser-harness"
    exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

echo "🔍 Google AI Mode Search"
echo "═══════════════════════════"
echo "Query: $QUERY"
echo ""

PROMPT="Search Google for: $QUERY. Summarize the top results."
TIMEOUT="${GOOGLE_AI_TIMEOUT_SECONDS:-${GOOGLE_AI_SEARCH_TIMEOUT:-150}}"

if [ -z "${BU_CDP_WS:-}" ]; then
    detected_ws="$(python3 -c "import json, urllib.request; print(json.load(urllib.request.urlopen('http://127.0.0.1:9222/json/version', timeout=2)).get('webSocketDebuggerUrl',''))" 2>/dev/null || true)"
    if [ -n "$detected_ws" ]; then
        export BU_CDP_WS="$detected_ws"
        echo "  Detected Chromium CDP websocket: $BU_CDP_WS"
    fi
fi

echo "  Using browser-harness Google AI lane."
prompt_file="$(mktemp /tmp/google_ai_prompt.XXXXXX.txt)"
result_file="$(mktemp /tmp/google_ai_result.XXXXXX.json)"
printf '%s' "$PROMPT" > "$prompt_file"

if GOOGLE_AI_PROMPT_FILE="$prompt_file" \
   GOOGLE_AI_RESULT_JSON="$result_file" \
   GOOGLE_AI_TIMEOUT_SECONDS="$TIMEOUT" \
   browser-harness -c "exec(open('$PROJECT_DIR/tools/infra/google_ai_driver.py').read())"; then
    python3 "$PROJECT_DIR/tools/infra/agent_message_ledger.py" \
        --source-tool "google-ai-search.sh" \
        --source-file "scripts/google-ai-search.sh" \
        --channel "google_ai_browser_harness_lane" \
        --provider "browser-harness" \
        --model "google_ai" \
        --platform "google_ai" \
        --prompt-file "$prompt_file" \
        --response-file "$result_file" \
        --success true >/dev/null || true
    cat "$result_file"
    rm -f "$prompt_file" "$result_file"
    exit 0
fi

python3 "$PROJECT_DIR/tools/infra/agent_message_ledger.py" \
    --source-tool "google-ai-search.sh" \
    --source-file "scripts/google-ai-search.sh" \
    --channel "google_ai_browser_harness_lane" \
    --provider "browser-harness" \
    --model "google_ai" \
    --platform "google_ai" \
    --prompt-file "$prompt_file" \
    --response-file "$result_file" \
    --success false >/dev/null || true

rm -f "$prompt_file" "$result_file"
echo "  Google AI browser-harness lane failed."
echo "  Browser-harness requires a live CDP browser session. Set BU_CDP_WS if auto-detection misses the browser."
exit 2
