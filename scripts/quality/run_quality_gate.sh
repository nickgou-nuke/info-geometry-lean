#!/usr/bin/env bash
# Consolidated Quality Gate Runner
# Runs all quality audits from a single entry point

set -euo pipefail

REPO_ROOT=$(git rev-parse --show-toplevel)
cd "$REPO_ROOT"

echo "═══════════════════════════════════════════════════════════════"
echo "INFO-GEOMETRY-LEAN CONSOLIDATED QUALITY GATE"
echo "═══════════════════════════════════════════════════════════════"
echo ""
echo "Running full codebase quality sweep..."
echo ""

mkdir -p artifacts reports

# Track failures
FAIL=0

# 1. AXIOM / SORRY / ADMIT AUDIT
echo "▶ [1/6] Axiom/Debt Audit (sorry, admit, axiom)"
if python3 tools/infra/axiom_audit.py --format json > artifacts/axiom_audit_full.json 2>&1; then
    GAPS=$(jq '.total_open_gaps' artifacts/axiom_audit_full.json 2>/dev/null || echo 0)
    DEBT_FILES=$(jq '.debt_files' artifacts/axiom_audit_full.json 2>/dev/null || echo 0)
    echo "  ✅ Open gaps (sorry/admit): $GAPS"
    echo "  ✅ Files with debt: $DEBT_FILES"
    if [ "$GAPS" -gt 0 ]; then
        echo "  ⚠️  $GAPS open gaps detected"
    fi
else
    echo "  ❌ Audit failed"
    FAIL=1
fi

# 2. PAULI PROTOCOL SEAL AUDIT
echo ""
echo "▶ [2/6] Pauli Protocol Seal Audit (I-XII)"
if python3 tools/quality/pauli_seal_audit.py --root lean/InfoGeometry --json-out reports/pauli-seal-audit.json > artifacts/pauli_audit_full.txt 2>&1; then
    VIOLATIONS=$(jq '.findingCount' reports/pauli-seal-audit.json 2>/dev/null || echo 0)
    HARD=$(jq '.hardFindingCount // 0' reports/pauli-seal-audit.json 2>/dev/null || echo 0)
    echo "  ✅ Pauli review findings in all InfoGeometry modules: $VIOLATIONS (hard: $HARD)"
    if [ "$VIOLATIONS" -gt 0 ]; then
        echo "  ⚠️  $VIOLATIONS violations detected"
    fi
else
    echo "  ❌ Audit failed"
    FAIL=1
fi

# 3. SEMANTIC VACUITY GATE
echo ""
echo "▶ [3/6] Semantic Vacuity Gate"
if python3 tools/quality/semantic_vacuity_gate.py lean --top 50 --fail-on none > artifacts/vacuity_full.txt 2>&1; then
    FINDINGS=$(grep "semantic_vacuity:" artifacts/vacuity_full.txt | awk '{print $2}' || echo 0)
    ERRORS=$(grep "error:" artifacts/vacuity_full.txt | awk '{print $2}' || echo 0)
    echo "  ✅ Findings: $FINDINGS"
    echo "  ✅ Errors (witness/carrier cheats): $ERRORS"
else
    echo "  ❌ Gate failed"
    FAIL=1
fi

# 4. MATHLESS PROOF AUDIT
echo ""
echo "▶ [4/6] Mathless / Skeletal Proof Audit"
set +e
python3 scripts/quality/mathless_proof_audit.py --root lean/InfoGeometry --format json > artifacts/mathless_full.json 2>&1
MATHLESS_STATUS=$?
set -e
SKELETAL=$(jq 'length' artifacts/mathless_full.json 2>/dev/null || echo 0)
if [ "$MATHLESS_STATUS" -eq 0 ]; then
    echo "  ✅ Skeletal/placeholder review findings: $SKELETAL"
else
    echo "  ⚠️  Skeletal/placeholder review findings: $SKELETAL (review-only; kernel debt is gate [1])"
fi

# 5. VACUITY LINTER (Honesty Score)
echo ""
echo "▶ [5/6] Vacuity Linter (Honesty/Vacuity Score)"
# The linter accepts one source file at a time.  Stream the complete
# InfoGeometry surface so the all-subfolder policy does not hit argv limits.
find lean/InfoGeometry -type f -name '*.lean' -print0 \
  | while IFS= read -r -d '' file; do
      python3 tools/scripts/vacuity-linter.py "$file" --json || true
    done > artifacts/vacuity_linter_all.jsonl 2>&1

# 6. THEORY AUDIT
echo ""
echo "▶ [6/6] Theory Audit (Namespaces, Imports, Structure)"
if bash scripts/quality/audit_theory.sh > artifacts/theory_audit.txt 2>&1; then
    echo "  ✅ Theory audit passed"
else
    echo "  ⚠️  Theory audit warnings (see artifacts/theory_audit.txt)"
fi

echo ""
echo "═══════════════════════════════════════════════════════════════"
echo "CONSOLIDATED QUALITY GATE SUMMARY"
echo "═══════════════════════════════════════════════════════════════"
echo ""
if [ -f artifacts/axiom_audit_full.json ]; then
    GAPS=$(jq '.total_open_gaps' artifacts/axiom_audit_full.json 2>/dev/null || echo "?")
    echo "  📋 Open gaps (sorry/admit): $GAPS"
fi
if [ -f reports/pauli-seal-audit.json ]; then
    VIOLATIONS=$(jq '.findingCount' reports/pauli-seal-audit.json 2>/dev/null || echo "?")
    HARD=$(jq '.hardFindingCount // 0' reports/pauli-seal-audit.json 2>/dev/null || echo 0)
    echo "  ⚛️  Pauli review findings: $VIOLATIONS (hard: $HARD)"
fi
if [ -f artifacts/vacuity_full.txt ]; then
    FINDINGS=$(grep "semantic_vacuity:" artifacts/vacuity_full.txt | awk '{print $2}' || echo "?")
    ERRORS=$(grep "error:" artifacts/vacuity_full.txt | awk '{print $2}' || echo "?")
    echo "  🕳️  Vacuity findings: $FINDINGS (errors: $ERRORS)"
fi
if [ -f artifacts/mathless_full.json ]; then
    SKELETAL=$(jq 'length' artifacts/mathless_full.json 2>/dev/null || echo "?")
    echo "  💀 Skeletal review findings: $SKELETAL"
fi
echo ""
if [ $FAIL -eq 0 ]; then
    echo "✅ QUALITY GATE PASSED"
    exit 0
else
    echo "❌ QUALITY GATE FAILED"
    exit 1
fi
