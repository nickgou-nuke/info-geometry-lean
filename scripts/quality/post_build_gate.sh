#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

mkdir -p artifacts

echo "═══════════════════════════════════════════════════"
echo "  POST-BUILD QUALITY GATE"
echo "═══════════════════════════════════════════════════"
echo "Root: $ROOT"
echo "Time: $(date -u '+%Y-%m-%d %H:%M:%SZ')"
echo

# Track overall status
FAILED=0

run_check() {
    local name="$1"
    shift
    echo "▶ $name"
    if "$@"; then
        echo "  ✅ $name"
    else
        echo "  ❌ $name (exit code: $?)"
        FAILED=1
    fi
}

run_gate() {
    local name="$1"
    shift
    echo "▶ $name"
    if "$@"; then
        echo "  ✅ $name (no issues found)"
    else
        local exit_code=$?
        if [ $exit_code -eq 1 ]; then
            echo "  🚫 $name (gate found issues - exit code: $exit_code)"
        else
            echo "  ❌ $name (command failed with exit code: $exit_code)"
        fi
        FAILED=1
    fi
}

# 1. Locked root Lake build must pass
run_check "Locked Lake build" \
    python3 tools/infra/run_locked_lake_build.py \
      --wait-for-build-lock InfoGeometry.All

# 2. Every tracked Lean root is scanned; active source scope is strict.
  run_check "Tracked Lean Scope Audit" \
    python3 tools/quality/repo_lean_scope_audit.py --fail-on package

# 3. Quarantine contents stay visible but are not active proof sources.
run_check "Quarantined Lean Artifact Audit" \
    python3 tools/quality/repo_lean_quarantine_audit.py

# 4. Axiom & Debt Audit (sorry/axiom/admit count)
run_check "Axiom & Debt Audit" python3 tools/infra/axiom_audit.py --fail-on-gaps

# 4. Semantic vacuity audit (tracked all-subfolder review surface)
# This detector is heuristic; kernel truth and proof debt remain hard-gated by
# the build, axiom audit, and semantic-content audit below.
run_check "Semantic Vacuity Audit (review-only)" \
    python3 tools/quality/semantic_vacuity_gate.py --tracked lean --fail-on none

# 5. Semantic content audit (proof holes, trivial theorems)
run_gate "Semantic Content Audit" python3 tools/quality/semantic_content_audit.py --file-prefix lean --gate

# 6. Theory audit (sorry/admit/axiom counts)
run_check "Theory Audit" bash scripts/quality/audit_theory.sh

echo
echo "═══════════════════════════════════════════════════"
if [ $FAILED -eq 0 ]; then
    echo "  ✅ ALL CHECKS PASSED"
else
    echo "  ❌ SOME CHECKS FAILED / GATES FOUND ISSUES"
fi
echo "═══════════════════════════════════════════════════"

exit $FAILED
