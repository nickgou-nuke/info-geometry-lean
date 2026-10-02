#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$REPO_ROOT"

echo "=== 1. Verifying SymPy CAS Certificate ==="
/home/goutev/.hermes/hermes-agent/venv/bin/python .agents/sandbox_connes_hodge/CAS/cas_connes_hodge_certificate.py

echo "=== 2. Running Token Scan & Declaration Fidelity Audits ==="
python3 .agents/sandbox_connes_hodge/audit/run_audit.py

echo "=== 3. Compiling Sandbox Lean 4 File under Build Lock ==="
python3 .agents/sandbox_connes_hodge/audit/audit_timing.py

echo "=== 4. Checking Unified Diff ==="
diff -u lean/DAG/ConnesHodgeBridge.lean .agents/sandbox_connes_hodge/lean/DAG/ConnesHodgeBridge.lean > .agents/sandbox_connes_hodge/diffs/connes_hodge_bridge.diff || true
echo "Diff generated at .agents/sandbox_connes_hodge/diffs/connes_hodge_bridge.diff"

echo "=== All Sandbox Verifications PASSED ==="
