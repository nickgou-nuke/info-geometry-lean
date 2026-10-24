#!/usr/bin/env bash
# Google AI Mode search — browser-harness-only lane (token-free OAuth/browser session).
# Usage:
#   ./scripts/google-ai-search.sh [--drunken-professor|-d | --socratic|-s | --mathlib|-m | --raw|-r] "query or stream"
#   Does not use aiClaw. Attaches to the browser-harness v0.1.13+ Chromium CDP lane
#   and records observations into the agent message ledger.

set -euo pipefail

MODE="${GOOGLE_AI_PROMPT_MODE:-default}"
ARGS=()
while [[ $# -gt 0 ]]; do
    case "$1" in
        -d|--drunken-professor|--drunk-professor)
            MODE="drunken-professor"
            shift
            ;;
        -s|--socratic)
            MODE="socratic"
            shift
            ;;
        -m|--mathlib)
            MODE="mathlib"
            shift
            ;;
        -r|--raw)
            MODE="raw"
            shift
            ;;
        --mode)
            MODE="${2:-default}"
            shift 2
            ;;
        -h|--help)
            echo "Usage: $0 [--drunken-professor|-d | --socratic|-s | --mathlib|-m | --raw|-r] <query>"
            echo "Modes:"
            echo "  default            Standard Google AI Mode search + synthesis"
            echo "  drunken-professor  De-conflate hazy/superimposed physics streams into exact math carriers + Lean 4 owner theorems"
            echo "  socratic           Adversarial Socratic audit of mathematical claims, counterexamples, and exact hypotheses"
            echo "  mathlib            Locate exact Lean 4 / Mathlib 4 declarations, imports, and algebraic carriers"
            echo "  raw                Send the query verbatim without wrapper instructions"
            exit 0
            ;;
        *)
            ARGS+=("$1")
            shift
            ;;
    esac
done

QUERY="${ARGS[*]:-}"
if [ -z "$QUERY" ]; then
    echo "Usage: $0 [--drunken-professor|-d | --socratic|-s | --mathlib|-m | --raw|-r] <search query>"
    echo "  Searches Google AI Mode via browser-harness"
    exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

echo "🔍 Google AI Mode Search (mode: $MODE)"
echo "═══════════════════════════"
echo "Query: $QUERY"
echo ""

case "$MODE" in
    drunken-professor|drunk-professor)
        PROMPT="The drunken professor confabulated hazy, raw, mix-up entangled ideas:

\"\"\"
$QUERY
\"\"\"

Extract the stream of pure mathematical consciousness from these random thoughts:
1. Ignore the physics prose and translate the physics concepts into their exact mathematical equivalents.
2. Extract the archetypes in the raw stream and order them properly in a causal poset (algebraic carrier -> noncommutative generators/projectors -> bimodule/sandwich flows -> trace/norm invariants).
3. Do NOT use scalar, diagonal, or commuting toys: stay strictly within noncommutative matrix/operator algebra and geometry (or non-associative Cayley-Dickson / Zorn vector-matrix algebra).
4. Regenerate a stream of canonical math in native Mathlib in Lean 4 with genuine lemmas and theorems with full constructive proofs only (zero wrappers, zero witnesses, zero assumed projector hypotheses), citing the exact primary mathematical literature."
        ;;
    socratic)
        PROMPT="Perform a rigorous Socratic mathematical audit of the following claim or query:

\"\"\"
$QUERY
\"\"\"

1. Separate what is an exact algebraic identity from what requires extra hypotheses (associativity, commutativity, invertibility, characteristic != 2, star-ring involution).
2. Give explicit minimal counterexamples to any over-generalized claim.
3. State the exact theorem and carrier where the statement holds without wrappers or vacuous assumptions, plus the relevant canonical references."
        ;;
    mathlib)
        PROMPT="Search Google and Mathlib 4 documentation for: $QUERY.
Identify the exact Lean 4 / Mathlib 4 module imports, typeclasses, declaration names, and constructive proof patterns."
        ;;
    raw)
        PROMPT="$QUERY"
        ;;
    *)
        PROMPT="Search Google for: $QUERY. Summarize the top mathematical and primary-literature results with exact equations and citations."
        ;;
esac

TIMEOUT="${GOOGLE_AI_TIMEOUT_SECONDS:-${GOOGLE_AI_SEARCH_TIMEOUT:-150}}"
export BH_NO_TAB_MARKER="${BH_NO_TAB_MARKER:-1}"

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
   GOOGLE_AI_DRIVER_FILE="$PROJECT_DIR/tools/infra/google_ai_driver.py" \
   GOOGLE_AI_TIMEOUT_SECONDS="$TIMEOUT" \
   browser-harness <<'PY'
import os
exec(open(os.environ["GOOGLE_AI_DRIVER_FILE"], encoding="utf-8").read())
PY
then
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
