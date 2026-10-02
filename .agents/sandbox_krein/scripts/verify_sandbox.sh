#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$REPO_ROOT"

echo "=== 1. Verifying SymPy CAS Certificate ==="
/home/goutev/.hermes/hermes-agent/venv/bin/python .agents/sandbox_krein/CAS/cas_krein_attention_certificate.py

echo "=== 2. Running Token Scan & Declaration Fidelity Audits ==="
python3 .agents/sandbox_krein/audit/run_audit.py

echo "=== 3. Compiling Sandbox Lean 4 File under Build Lock ==="
python3 .agents/sandbox_krein/audit/audit_timing.py

echo "=== 4. Checking Unified Diff ==="
diff -u lean/InfoGeometry/LLM/KreinAttentionEnergy.lean .agents/sandbox_krein/lean/InfoGeometry/LLM/KreinAttentionEnergy.lean > .agents/sandbox_krein/diffs/krein_attention_energy.diff || true
echo "Diff generated at .agents/sandbox_krein/diffs/krein_attention_energy.diff"

echo "=== All Sandbox Verifications PASSED ==="
