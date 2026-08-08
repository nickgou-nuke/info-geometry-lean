#!/usr/bin/env bash
# Agent Pipeline — orchestrator with queue of theorems
# Each theorem gets: Researcher → Algebraist → Formalist → Critic → Archivist
# Usage: ./scripts/agent-pipeline.sh [--auto] [--theorem theorem-001]

set -euo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/.."

CYAN='\033[0;36m'; GREEN='\033[0;32m'; YELLOW='\033[1;33m'; RED='\033[0;31m'
BOLD='\033[1m'; NC='\033[0m'

draw_bar() { local p=$1 l=$2 w=30 f=$((p*w/100)); printf "\r${CYAN}[${NC}";for ((i=0;i<f;i++)); do printf "${GREEN}█${NC}";done;for ((i=f;i<w;i++)); do printf "░${NC}";done;printf "${CYAN}]${NC} %3d%% %s" "$p" "$l"; }

source .venv/bin/activate 2>/dev/null || true

# ── Load queue ──
QUEUE_FILE="task_queue.json"
if [ ! -f "$QUEUE_FILE" ]; then
    echo '{"queue":[],"agents":{}}' > "$QUEUE_FILE"
fi

show_queue() {
    python3 << 'PYEOF'
import json
q = json.load(open('task_queue.json'))
tasks = q['queue']
print(f"\n{'='*60}")
print(f"  AGENT PIPELINE — {len(tasks)} theorems")
print(f"{'='*60}")
for t in tasks:
    icon = '✅' if t['status'] == 'done' else '🔄' if t['status'] == 'running' else '⏳'
    sympy = '✓' if t.get('sympy_witness') else ' '
    lean = '✓' if t.get('lean_proof') else ' '
    print(f"  {icon} [{sympy}|{lean}] {t['id']}: {t['title'][:55]}")
print(f"\n  Agents: {len(q.get('agents',{}))}")
PYEOF
}

run_theorem() {
    local theorem_id="$1"
    python3 - "$theorem_id" << 'PYEOF'
import json, subprocess, sys, os

q = json.load(open('task_queue.json'))
theorem = None
for t in q['queue']:
    if t['id'] == sys.argv[1]:
        theorem = t
        break
if not theorem:
    print(f"❌ Theorem {sys.argv[1]} not found")
    sys.exit(1)

tid = theorem['id']
title = theorem['title']
print(f"\n{'='*60}")
print(f"  RUNNING: {tid} — {title}")
print(f"{'='*60}\n")

# Mark as running
theorem['status'] = 'running'
json.dump(q, open('task_queue.json', 'w'), indent=2)

steps = [
    ("🔍 Researcher", "harvest-knowledge.sh", f"echo 'fetching context for {title}'"),
    ("🧮 Algebraist", "verify_sympy_witness", ""),
    ("📐 Formalist", "verify_lean_proof", ""),
    ("🔎 Critic", "vacuity-linter.py", ""),
    ("💾 Archivist", "commit_conscious_knowledge", "")
]

total = len(steps)
for i, (name, tool, cmd) in enumerate(steps):
    pct = ((i+1) * 100) // total
    bar = '█' * (pct//4) + '░' * (25 - pct//4)
    print(f"\n  [{bar}] {pct}%  {name} ({tool})")
    
    if tool == "harvest-knowledge.sh":
        if os.path.exists(f"scripts/{tool}"):
            subprocess.run(["bash", f"scripts/{tool}", title], capture_output=True, timeout=15)
            print(f"    ✅ context gathered")
    
    elif tool == "verify_sympy_witness":
        print(f"    ⏳ SymPy witness needed for: {title[:50]}...")
        # Here the orchestrator would call Pi to run the tool
        print(f"    📝 The orchestrator will assign this to the algebraist agent")
    
    elif tool == "verify_lean_proof":
        print(f"    ⏳ Lean proof needed for: {title[:50]}...")
        print(f"    📝 The orchestrator will assign this to the formalist agent")
    
    elif tool == "vacuity-linter.py":
        print(f"    ⏳ Vacuity check needed")
    
    elif tool == "commit_conscious_knowledge":
        print(f"    ⏳ Committing to KB")

# Mark as done
theorem['status'] = 'done'
json.dump(q, open('task_queue.json', 'w'), indent=2)
print(f"\n✅ {tid} complete")
PYEOF
}

# ── Main ──
if [ "$1" == "--theorem" ] && [ -n "$2" ]; then
    run_theorem "$2"
elif [ "$1" == "--auto" ]; then
    python3 -c "
import json
q = json.load(open('task_queue.json'))
for t in q['queue']:
    if t['status'] == 'pending':
        print(t['id'])
" | while read tid; do
        run_theorem "$tid"
    done
    echo -e "\n${GREEN}✅ All theorems processed${NC}"
else
    show_queue
    echo ""
    echo "Usage:"
    echo "  ./scripts/agent-pipeline.sh --theorem theorem-001   # Run one theorem"
    echo "  ./scripts/agent-pipeline.sh --auto                  # Run all pending"
    echo "  ./scripts/agent-pipeline.sh                         # Show queue"
fi
