#!/usr/bin/env bash
# Google AI Mode search — uses aiClaw bridge or direct API
# Usage: ./scripts/google-ai-search.sh "query string"
#   Uses Google AI Mode (udm=50) via browser if bridge is active,
#   falls back to API-based search.

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

# Try via bridge first (aiClaw/Gemini)
if ss -tnp 2>/dev/null | grep -q "1956.*ESTAB.*chrome"; then
    echo "  Bridge connected — sending to browser AI..."
    timeout 15 node -e "
    const WebSocket = require('ws');
    const ws = new WebSocket('ws://localhost:1956');
    ws.on('open', () => {
        ws.send(JSON.stringify({
            action: 'send_message',
            message: 'Search Google for: $QUERY. Summarize the top results.',
            source: 'PI_AGENT_GOOGLE_SEARCH'
        }));
    });
    ws.on('message', (data) => {
        const msg = JSON.parse(data.toString());
        if (msg.text) process.stdout.write(msg.text);
        if (msg.status === 'done') { console.log(); ws.close(); }
    });
    setTimeout(() => process.exit(0), 12000);
    " 2>&1
else
    echo "  Bridge not active. Opening Google AI Mode in browser..."
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
    echo "  To capture results: ensure aiClaw bridge is active, then re-run"
fi
