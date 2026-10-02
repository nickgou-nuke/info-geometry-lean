#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$REPO_ROOT"

echo "=== 1. Verifying SymPy CAS Certificate ==="
/home/goutev/.hermes/hermes-agent/venv/bin/python .agents/sandbox_correlator/CAS/cas_field_correlator_certificate.py

echo "=== 2. Running Token Scan & Declaration Fidelity Audits ==="
python3 .agents/sandbox_correlator/audit/run_audit.py

echo "=== 3. Compiling Sandbox Lean 4 File under Build Lock ==="
python3 .agents/sandbox_correlator/audit/audit_timing.py

echo "=== 4. Checking Unified Diff ==="
diff -u lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean .agents/sandbox_correlator/lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean > .agents/sandbox_correlator/diffs/field_correlator_projection.diff || true
echo "Diff generated at .agents/sandbox_correlator/diffs/field_correlator_projection.diff"

echo "=== All Sandbox Verifications PASSED ==="
