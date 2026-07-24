#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

echo "═══════════════════════════════════════════════════════"
echo "POST-BUILD QUALITY GATE (Full Codebase Sweep)"
echo "═══════════════════════════════════════════════════════"

FAILED=0

# 1. Lake build check
echo "▶ 1/6: Lake build check"
if lake build; then
    echo "  ✅ Lake build passed"
else
    echo "  ❌ Lake build failed"
    FAILED=1
fi

# 2. Axiom & Sorry Sweep
echo ""
echo "▶ 2/6: Axiom / Sorry / Admit audit (Full Codebase)"
if python3 tools/infra/axiom_audit.py > /dev/null 2>&1; then
    GAPS=$(python3 -c "import json; print(json.load(open('artifacts/axiom_audit_report.json')).get('total_open_gaps', 0))" 2>/dev/null || echo 0)
    DEBT_FILES=$(python3 -c "import json; print(json.load(open('artifacts/axiom_audit_report.json')).get('debt_files', 0))" 2>/dev/null || echo 0)
    echo "  Total open gaps (sorry/admit): $GAPS"
    echo "  Files containing debt: $DEBT_FILES"
    if [ "${STRICT_ENFORCEMENT:-0}" = "1" ] && [ "$GAPS" -gt 0 ]; then
        echo "  ❌ Fail: STRICT_ENFORCEMENT=1 and open gaps exist."
        FAILED=1
    fi
else
    echo "  ❌ Failed to run axiom_audit"
    FAILED=1
fi

# 3. Pauli Protocol Seal Compliance (I-XII)
echo ""
echo "▶ 3/6: Pauli Protocol Seal Compliance Audit"
python3 tools/quality/pauli_seal_audit.py --root lean --json-out reports/pauli-seal-audit.json > artifacts/pauli_audit_full.txt 2>&1 || true

if [ -f reports/pauli-seal-audit.json ]; then
    VIOLATIONS=$(python3 -c "import json; print(json.load(open('reports/pauli-seal-audit.json')).get('findingCount', 0))" 2>/dev/null || echo 0)
    echo "  Total Pauli Protocol violations in total codebase: $VIOLATIONS"
    if [ "$VIOLATIONS" -gt 0 ]; then
        echo "  ⚠️  Pauli violations detected (see reports/pauli-seal-audit.json)"
        if [ "${STRICT_ENFORCEMENT:-0}" = "1" ]; then
            echo "  ❌ Fail: STRICT_ENFORCEMENT=1 and Pauli violations exist."
            FAILED=1
        fi
    fi
else
    echo "  ❌ Failed to run Pauli Seal audit (no output JSON created)"
    cat artifacts/pauli_audit_full.txt
    FAILED=1
fi

# 4. Semantic Vacuity & Witness Gate
echo ""
echo "▶ 4/6: Semantic Vacuity & Witness Gate (Linter)"
if python3 tools/quality/semantic_vacuity_gate.py lean --top 20 --fail-on none --json-out artifacts/vacuity_full.json > /dev/null 2>&1; then
    FINDINGS=$(python3 -c "import json; d=json.load(open('artifacts/vacuity_full.json')); print(len(d.get('findings', [])))" 2>/dev/null || echo 0)
    ERRORS=$(python3 -c "import json; d=json.load(open('artifacts/vacuity_full.json')); print(d.get('severity_counts', {}).get('error', 0))" 2>/dev/null || echo 0)
    echo "  Total semantic vacuity findings: $FINDINGS"
    echo "  Total vacuity errors (witness/carrier cheats): $ERRORS"
    if [ "${STRICT_ENFORCEMENT:-0}" = "1" ] && [ "$ERRORS" -gt 0 ]; then
        echo "  ❌ Fail: STRICT_ENFORCEMENT=1 and vacuity errors exist."
        FAILED=1
    fi
else
    echo "  ❌ Failed to run semantic vacuity gate"
    FAILED=1
fi

# 5. Mathless & Skeletal Proof Audit
echo ""
echo "▶ 5/6: Mathless & Skeletal Proof Audit"
python3 scripts/quality/mathless_proof_audit.py --root lean --format json > artifacts/mathless_full.json 2>&1 || true

if [ -f artifacts/mathless_full.json ]; then
    SKELETAL_COUNT=$(python3 -c "import json; print(len(json.load(open('artifacts/mathless_full.json'))))" 2>/dev/null || echo 0)
    echo "  Total skeletal/placeholder proofs: $SKELETAL_COUNT"
    if [ "${STRICT_ENFORCEMENT:-0}" = "1" ] && [ "$SKELETAL_COUNT" -gt 0 ]; then
        echo "  ❌ Fail: STRICT_ENFORCEMENT=1 and skeletal proofs exist."
        FAILED=1
    fi
else
    echo "  ❌ Failed to run mathless proof audit (no output JSON created)"
    FAILED=1
fi

# 6. Theory Audit (Structural/Namespace Checks)
echo ""
echo "▶ 6/6: Theory Audit (Structural/Namespace Checks)"
if bash scripts/quality/audit_theory.sh > artifacts/theory_audit.txt 2>&1; then
    echo "  ✅ Theory audit completed successfully (report saved to reports/theory_audit.md)"
else
    echo "  ⚠️  Theory audit encountered warnings (see artifacts/theory_audit.txt)"
fi

echo ""
echo "═══════════════════════════════════════════════════════"
echo "POST-BUILD GATE SUMMARY"
echo "═══════════════════════════════════════════════════════"

# Recompute summary from artifacts
MATHLESS_COUNT=$(python3 -c "import json; print(len([x for x in json.load(open('/tmp/mathless_full.json')) if x.get('category') in ('skeletal_proof','proof_hole')]))" 2>/dev/null || echo 0)
VACUITY_ERROR=$(jq '.error' /tmp/vacuity_full.json 2>/dev/null || echo 0)
AXIOM_GAPS=$(jq '.total_open_gaps' /tmp/axiom_full.json 2>/dev/null || echo 0)
BLOCKING=$(jq '.blocking_finding_count // 0' /tmp/content_full.json 2>/dev/null || echo 0)

echo "  Mathless skeletal/holes:      $(python3 -c "import json; print(len([x for x in json.load(open('/tmp/mathless_full.json')) if x.get('category') in ('skeletal_proof','proof_hole')])" 2>/dev/null || echo 0)"
echo "  Vacuity errors/warnings:      $(jq '.error' /tmp/vacuity_full.json 2>/dev/null || echo 0) / $(jq '.warning' /tmp/vacuity_full.json 2>/dev/null || echo 0)"
echo "  Axiom gaps/files:             $(jq '.total_open_gaps' /tmp/axiom_full.json 2>/dev/null || echo 0) / $(jq '.files_with_debt' /tmp/axiom_full.json 2>/dev/null || echo 0)"
echo "  Content blocking/holes/trivial: $(jq '.blocking_finding_count // 0' /tmp/content_full.json 2>/dev/null || echo 0) / $(jq '.category_counts["proof-hole"] // 0' /tmp/content_full.json 2>/dev/null || echo 0) / $(jq '.category_counts["trivial-theorem"] // 0' /tmp/content_full.json 2>/dev/null || echo 0)"
echo "═══════════════════════════════════════════════════════"

GATE_FAILED=0
if [ "$MATHLESS_COUNT" -gt 0 ]; then
    echo "❌ GATE FAILED: Mathless proofs/holes found ($MATHLESS_COUNT)"
    exit 1
fi
if [ "$VACUITY_ERROR" -gt 0 ]; then
    echo "❌ GATE FAILED: Vacuity errors found ($VACUITY_ERROR)"
    exit 1
fi
if [ "$AXIOM_GAPS" -gt 0 ]; then
    echo "❌ GATE FAILED: Axiom gaps found ($AXIOM_GAPS)"
    exit 1
fi
if [ "$BLOCKING" -gt 0 ]; then
    echo "❌ GATE FAILED: Content blocking findings ($BLOCKING)"
    exit 1
fi

echo "✅ GATE PASSED"
exit 0