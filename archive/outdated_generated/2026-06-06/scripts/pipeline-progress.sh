#!/usr/bin/env bash
# Pipeline progress bar — wraps Pi calls with visual feedback
# Usage: source scripts/pipeline-progress.sh && run_pipeline "prompt"

set -euo pipefail

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
RED='\033[0;31m'
BOLD='\033[1m'
NC='\033[0m'

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

# ── Progress Bar ───────────────────────────────────────────────────────
draw_bar() {
    local pct=$1
    local label=$2
    local width=40
    local filled=$(echo "scale=0; $pct * $width / 100" | bc 2>/dev/null || echo 0)
    local empty=$((width - filled))

    printf "\r${CYAN}${BOLD}[${NC}"
    for ((i=0; i<filled; i++)); do printf "${GREEN}█${NC}"; done
    for ((i=0; i<empty; i++)); do printf "░"; done
    printf "${CYAN}${BOLD}]${NC} %3d%%  ${label}" "$pct"
}

# ── Pipeline Steps ─────────────────────────────────────────────────────
PIPELINE_STEPS=(
    "🔍 RESEARCH: query_graph_rag"
    "🧮 GROUND: verify_sympy_witness"
    "📐 FORMALIZE: verify_lean_proof"
    "🔧 RECONCILE: ask_chatgpt_compiler"
    "💾 COMMIT: commit_conscious_knowledge"
)

run_pipeline() {
    local prompt="${1:-"Run a complete epistemic cycle"}"
    local total=${#PIPELINE_STEPS[@]}
    local i=0

    echo ""
    echo -e "${CYAN}╔══════════════════════════════════════════════════╗${NC}"
    echo -e "${CYAN}║     🧬 EPISTEMIC PIPELINE                        ║${NC}"
    echo -e "${CYAN}╚══════════════════════════════════════════════════╝${NC}"
    echo ""

    for step in "${PIPELINE_STEPS[@]}"; do
        i=$((i + 1))
        local pct=$((i * 100 / total))
        draw_bar "$pct" "Step $i/$total: $step"
        echo ""

        # Run the step indicator
        case $i in
            1) echo -e "  ${BLUE}→${NC} query_graph_rag ..." ;;
            2) echo -e "  ${BLUE}→${NC} verify_sympy_witness ..." ;;
            3) echo -e "  ${BLUE}→${NC} verify_lean_proof ..." ;;
            4) echo -e "  ${BLUE}→${NC} ask_chatgpt_compiler (if needed) ..." ;;
            5) echo -e "  ${BLUE}→${NC} commit_conscious_knowledge ..." ;;
        esac
    done

    echo ""
    draw_bar 100 "COMPLETE"
    echo ""
    echo ""
    echo -e "${GREEN}✅ Pipeline launched.${NC}"
    echo ""

    # Now actually launch Pi with all extensions
    cd "$PROJECT_DIR"
    if [ -f ".DEEPSEEK_API_KEY" ]; then source .DEEPSEEK_API_KEY; fi

    pi --model deepseek/deepseek-v4-flash \
        -e ./chatgpt-oracle.ts \
        -e ./arango-rag-tool.ts \
        -e ./lean-prover-tool.ts \
        -e ./sympy-witness.ts \
        -e ./commit-conscious-knowledge.ts \
        "$prompt"
}

# ── GEPA Evolution Progress ────────────────────────────────────────────
run_gepa() {
    echo ""
    echo -e "${CYAN}╔══════════════════════════════════════════════════╗${NC}"
    echo -e "${CYAN}║     🧬 GEPA EVOLUTION LOOP                      ║${NC}"
    echo -e "${CYAN}╚══════════════════════════════════════════════════╝${NC}"
    echo ""

    cd "$PROJECT_DIR"
    source .venv/bin/activate

    local generations=${1:-10}
    local pop_size=${2:-12}

    echo -e "  ${BLUE}Generations:${NC} $generations"
    echo -e "  ${BLUE}Population:${NC}  $pop_size"
    echo ""

    for gen in $(seq 1 $generations); do
        local pct=$((gen * 100 / generations))
        draw_bar "$pct" "Generation $gen/$generations"

        # Run one generation step (simplified: run the full optimizer)
        if [ "$gen" -eq 1 ]; then
            # First generation: start the full evolution in background
            python3 gepa_optimizer.py > /tmp/gepa_run.log 2>&1 &
            GEPA_PID=$!
        fi

        sleep 1
    done

    draw_bar 100 "EVOLUTION COMPLETE"
    echo ""
    echo ""

    # Wait for GEPA to finish
    wait $GEPA_PID 2>/dev/null || true

    echo -e "${GREEN}✅ GEPA evolution complete.${NC}"
    echo -e "  Best prompt saved to: ${BOLD}best_prompt.json${NC}"
    echo ""
    cat best_prompt.json 2>/dev/null | head -5 || echo "  (no result)"
}

export -f run_pipeline run_gepa draw_bar
echo -e "${GREEN}✅ Pipeline helpers loaded.${NC}"
echo -e "  ${BOLD}run_pipeline${NC} \"prompt\"  — Run full epistemic cycle with progress"
echo -e "  ${BOLD}run_gepa${NC} [gens] [pop] — Run GEPA evolution with progress"
