#!/usr/bin/env bash
set -euo pipefail

# ═══════════════════════════════════════════════════════════════════════
# Neuro-Symbolic Agentic System Launcher
# ═══════════════════════════════════════════════════════════════════════
# Launches Pi with all six extensions loaded simultaneously:
#   1. chatgpt-oracle.ts       - Expert consultant for complex bugs
#   2. arango-rag-tool.ts      - Graph-RAG knowledge retrieval
#   3. lean-prover-tool.ts     - Lean 4 theorem prover
#   4. sympy-witness.ts        - SymPy algebraic witness
#   5. commit-conscious-knowledge.ts - Knowledge persistence
#   6. agent-orchestrator.ts   - Concrete Researcher/SymPy/Lean/Critic queue runner
#
# Usage:
#   ./run.sh [prompt]
#
# Example:
#   ./run.sh "Research FFT algorithms and prove a theorem"
#
# Prerequisites:
#   - Node.js >= 18, npm
#   - Pi installed globally
#   - DEEPSEEK_API_KEY exported (or in .DEEPSEEK_API_KEY file)
#   - Optional: isolated aiClaw ArangoDB running on AICLAW_ARANGO_URL
#   - Optional: Python 3 + sympy for algebraic witnesses
#   - Optional: Lean 4 for theorem proving
# ═══════════════════════════════════════════════════════════════════════

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

echo -e "${CYAN}"
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║     🧬 NEURO-SYMBOLIC AGENTIC SYSTEM LAUNCHER              ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo -e "${NC}"

# ── Load API Key ──────────────────────────────────────────────────────
if [ -z "${DEEPSEEK_API_KEY:-}" ]; then
  if [ -f ".DEEPSEEK_API_KEY" ]; then
    source .DEEPSEEK_API_KEY
    echo -e "${GREEN}✓${NC} Loaded API key from .DEEPSEEK_API_KEY"
  else
    echo -e "${YELLOW}⚠${NC} No DEEPSEEK_API_KEY set. Export it or create .DEEPSEEK_API_KEY with:"
    echo '  export DEEPSEEK_API_KEY="sk-your-key-here"'
    echo ""
  fi
else
  echo -e "${GREEN}✓${NC} DEEPSEEK_API_KEY is set"
fi

# Pi auto-detects provider from model prefix (deepseek/...)
# No need to set OPENAI_BASE_URL manually

# Keep agent runtime state inside the repository workspace by default. This
# avoids sandbox failures from Pi writing ~/.pi and Archon writing ~/.archon.
export INFO_GEOMETRY_RUNTIME_DIR="${INFO_GEOMETRY_RUNTIME_DIR:-$SCRIPT_DIR/.runtime}"
export PI_RUNTIME_HOME="${PI_RUNTIME_HOME:-$INFO_GEOMETRY_RUNTIME_DIR/pi-home}"
export ARCHON_HOME="${ARCHON_HOME:-$INFO_GEOMETRY_RUNTIME_DIR/archon-home}"
mkdir -p "$PI_RUNTIME_HOME" "$ARCHON_HOME"
echo -e "${GREEN}✓${NC} Runtime state: $INFO_GEOMETRY_RUNTIME_DIR"
echo -e "  ${GREEN}✓${NC} Pi HOME: $PI_RUNTIME_HOME"
echo -e "  ${GREEN}✓${NC} Archon HOME: $ARCHON_HOME"

# Keep the aiClaw proof-memory brain separate from the repo DAG ArangoDB.
export AICLAW_ARANGO_URL="${AICLAW_ARANGO_URL:-http://127.0.0.1:8540}"
export AICLAW_ARANGO_DB="${AICLAW_ARANGO_DB:-aiclaw_auto_rag}"
export AICLAW_KNOWLEDGE_BASE="${AICLAW_KNOWLEDGE_BASE:-$SCRIPT_DIR/knowledge_base.json}"

# ── Check Dependencies ────────────────────────────────────────────────
echo ""
echo -e "${BLUE}── Checking dependencies ──────────────────────────${NC}"

# Check Node.js
if command -v node &>/dev/null; then
  echo -e "${GREEN}✓${NC} Node.js $(node -v)"
else
  echo -e "${YELLOW}✗${NC} Node.js not found"
fi

# Check Pi
if command -v pi &>/dev/null; then
  echo -e "${GREEN}✓${NC} Pi $(pi --version 2>/dev/null || echo 'installed')"
else
  echo -e "${YELLOW}✗${NC} Pi not found in PATH"
  echo "  Install: npm install -g @earendil-works/pi-coding-agent"
  exit 1
fi

# Check Python / SymPy (prefer local venv)
PYTHON_BIN="python3"
if [ -f ".venv/bin/python3" ]; then
  PYTHON_BIN=".venv/bin/python3"
  echo -e "${GREEN}✓${NC} Python virtual env: .venv"
elif [ -f ".venv/bin/python" ]; then
  PYTHON_BIN=".venv/bin/python"
  echo -e "${GREEN}✓${NC} Python virtual env: .venv"
fi

if $PYTHON_BIN -c "import sympy" &>/dev/null 2>&1; then
  echo -e "${GREEN}✓${NC} $($PYTHON_BIN --version | head -1) + SymPy $($PYTHON_BIN -c 'import sympy; print(sympy.__version__)')"
else
  echo -e "${YELLOW}⚠${NC} Python 3 found but sympy not installed in venv"
  echo "  Run: source .venv/bin/activate \&\& pip install sympy"
fi

# Check Lean 4
if command -v lean &>/dev/null; then
  LEAN_VER=$(lean --version 2>/dev/null | head -1)
  echo -e "${GREEN}✓${NC} $LEAN_VER"
  # Check if mathlib project is available
  if [ -d "$SCRIPT_DIR/.lake/packages/mathlib" ]; then
    echo -e "  ${GREEN}✓${NC} mathlib v4.28.1 project ready (6.9GB package cache)"
  else
    echo -e "  ${YELLOW}⚠${NC} mathlib project not found — plain Lean code only"
  fi
else
  echo -e "${YELLOW}⚠${NC} Lean 4 not found (optional — for formal verification)"
  echo "  Install: https://leanprover.github.io/"
fi

# Check ArangoDB
if command -v arangod &>/dev/null; then
  echo -e "${GREEN}✓${NC} ArangoDB available"
  echo -e "  ${GREEN}✓${NC} aiClaw proof brain: ${AICLAW_ARANGO_URL}/${AICLAW_ARANGO_DB}"
else
  echo -e "${YELLOW}⚠${NC} ArangoDB not found (optional - uses file fallback)"
  echo -e "  ${YELLOW}⚠${NC} aiClaw proof brain configured as ${AICLAW_ARANGO_URL}/${AICLAW_ARANGO_DB}"
fi

# Check npm dependencies
if [ -d "node_modules" ]; then
  echo -e "${GREEN}✓${NC} npm dependencies installed"
else
  echo -e "${YELLOW}⚠${NC} Running npm install..."
  npm install
fi

# ── Verify Extension Files ────────────────────────────────────────────
echo ""
echo -e "${BLUE}── Checking extensions ─────────────────────────────${NC}"

EXTENSIONS=(
  "chatgpt-oracle.ts"
  "arango-rag-tool.ts"
  "lean-prover-tool.ts"
  "sympy-witness.ts"
  "commit-conscious-knowledge.ts"
  "agent-orchestrator.ts"
)

EXT_ARGS=()
for ext in "${EXTENSIONS[@]}"; do
  if [ -f "$ext" ]; then
    echo -e "${GREEN}✓${NC} $ext"
    EXT_ARGS+=("-e" "./$ext")
  else
    echo -e "${YELLOW}✗${NC} $ext not found!"
  fi
done

# ── Build Extension Arguments ────────────────────────────────────────
echo ""
EXT_COUNT=$((${#EXT_ARGS[@]} / 2))
echo -e "${BLUE}── Launching Pi with ${EXT_COUNT} extensions ───────────────${NC}"
echo ""

# Default prompt if none provided
DEFAULT_PROMPT="Research the local knowledge mesh using query_graph_rag for Fast Fourier Transforms.
STEP 1 (Grounding): Write a Python SymPy script to compute the algebraic state of the consensus matrix and verify the witness using verify_sympy_witness.
STEP 2 (Formalizing): Using the validated SymPy logic as your absolute grounding truth, translate the mathematical core into a Lean 4 theorem and check it via verify_lean_proof.
STEP 3 (Reconciliation): If the Lean compiler fails, execute ask_chatgpt_compiler passing the Lean code, the trace error, AND the successful SymPy witness so the Oracle can bridge the languages.
STEP 4 (Queue): For repeatable work, persist the paired files with queue_add_theorem and execute the concrete workers with queue_run_next.
STEP 5 (Commit): Once both structures align flawlessly, permanently write the multimodal pair to the database via commit_conscious_knowledge."

PROMPT="${*:-$DEFAULT_PROMPT}"

# ── Launch Pi ─────────────────────────────────────────────────────────
echo -e "${CYAN}╔══════════════════════════════════════════════════════════════╗${NC}"
echo -e "${CYAN}║                    🚀 LAUNCHING AGENT                        ║${NC}"
echo -e "${CYAN}╚══════════════════════════════════════════════════════════════╝${NC}"
echo ""

set -x
env HOME="$PI_RUNTIME_HOME" \
  pi --model deepseek/deepseek-v4-flash \
     "${EXT_ARGS[@]}" \
     "$PROMPT"
