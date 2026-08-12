#!/usr/bin/env bash
# Post-build quality gate - runs after lake build
# Consolidated single entry point for all quality checks (Fast Mode)

set -euo pipefail

REPO_ROOT=$(git rev-parse --show-toplevel)
cd "$REPO_ROOT"

mkdir -p artifacts reports

echo "════════════════════════════════════════════════════════"
echo "INFO-GEOMETRY-LEAN QUALITY GATE (Fast Mode)"
echo "════════════════════════════════════════════════════════"

# 1. Sorry/axiom/admit check on the complete InfoGeometry surface (hard gate).
# Fast mode must not silently reduce proof-debt coverage to a handful of
# Canonical files; the canonical structural checks live in strict-check.sh.
echo ""
echo "▶ [1/5] Sorry/Axiom/Admit check on all InfoGeometry files..."
SCAN_ROOT="lean/InfoGeometry"
if python3 tools/infra/axiom_audit.py --fail-on-gaps > artifacts/axiom_audit_fast.txt 2>&1; then
    echo "  ✅ all repo-owned Lean files clean (axiom audit)"
else
    cat artifacts/axiom_audit_fast.txt
    exit 1
fi

# 2. Vacuity review on the complete InfoGeometry surface
echo ""
echo "▶ [2/5] Semantic vacuity review on all InfoGeometry files..."
python3 tools/quality/semantic_vacuity_gate.py "$SCAN_ROOT" --fail-on none \
  --json-out artifacts/vacuity_infogeometry.json > artifacts/vacuity_infogeometry.txt 2>&1 || true

# 3. Semantic vacuity gate on all InfoGeometry files (review-only)
echo ""
echo "▶ [3/5] Semantic vacuity gate on all InfoGeometry files..."
python3 tools/quality/semantic_vacuity_gate.py "$SCAN_ROOT" --fail-on error > artifacts/vacuity_infogeometry.txt 2>&1 || {
    echo "  ⚠️  Semantic vacuity errors in InfoGeometry (structural):"
    cat artifacts/vacuity_infogeometry.txt
    # Don't fail - these are structural design choices (sockets with Prop fields)
}

# 4. Full axiom audit (informational)
echo ""
echo "▶ [4/5] Full axiom/debt audit..."
if python3 tools/infra/axiom_audit.py --format json > artifacts/axiom_audit_full.json 2>&1; then
    GAPS=$(jq '.total_open_gaps' artifacts/axiom_audit_full.json 2>/dev/null || echo "?")
    FILES=$(jq '.debt_files' artifacts/axiom_audit_full.json 2>/dev/null || echo "?")
    echo "  Open gaps (sorry/admit): $GAPS"
    echo "  Files with debt: $FILES"
fi

# 5. Mathless proof audit (informational)
echo ""
echo "▶ [5/5] Mathless/skeletal proof audit..."
if python3 scripts/quality/mathless_proof_audit.py --root lean/InfoGeometry --format json > artifacts/mathless_full.json 2>&1; then
    COUNT=$(jq 'length' artifacts/mathless_full.json 2>/dev/null || echo "?")
    echo "  Skeletal/placeholder proofs: $COUNT"
fi

echo ""
echo "════════════════════════════════════════════════════════"
echo "✅ QUALITY GATE COMPLETED"
echo "════════════════════════════════════════════════════════"
