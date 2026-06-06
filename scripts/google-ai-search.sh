#!/usr/bin/env bash
# Google AI Mode search — uses the queued aiClaw adapter or opens a browser URL
# Usage: ./scripts/google-ai-search.sh "query string"
#   Uses the repo queue before browser automation. It does not post through the
#   legacy port-1956 WebSocket bridge.

set -euo pipefail

QUERY="$*"
if [ -z "$QUERY" ]; then
    echo "Usage: $0 <search query>"
    echo "  Searches Google AI Mode via aiClaw bridge or API fallback"
    exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

echo "🔍 Google AI Mode Search"
echo "═══════════════════════════"
echo "Query: $QUERY"
echo ""

PLATFORM="${AICLAW_GOOGLE_PLATFORM:-gemini}"
PROMPT="Search Google for: $QUERY. Summarize the top results."

echo "  Trying queued aiClaw platform: $PLATFORM"
if python3 "$PROJECT_DIR/tools/infra/aiclaw_chat.py" ask \
    --platform "$PLATFORM" \
    --wait \
    --json \
    --quiet \
    --prompt "$PROMPT"; then
    exit 0
fi

echo "  Queued aiClaw route unavailable. Opening Google AI Mode in browser..."
    # Open Google AI Mode search in Chrome
    encoded=$(python3 -c "import urllib.parse; print(urllib.parse.quote('''$QUERY'''))")
    google_url="https://www.google.com/search?q=${encoded}&udm=50"

    if command -v google-chrome-stable &>/dev/null; then
        google-chrome-stable "$google_url" &>/dev/null &
        echo "  Opened in Chrome: $google_url"
    elif command -v xdg-open &>/dev/null; then
        xdg-open "$google_url" &>/dev/null &
        echo "  Opened in browser: $google_url"
    else
        echo "  URL: $google_url"
    fi
    echo ""
    echo "  To capture results automatically, configure aiClaw for platform '$PLATFORM' and re-run."
