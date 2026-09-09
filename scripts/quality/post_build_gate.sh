#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

mkdir -p artifacts

# Parse mode and flags
MODE="full"
BASE_REF=""

for arg in "$@"; do
    case "$arg" in
        --incremental|-i|incremental)
            MODE="incremental"
            ;;
        --base=*)
            BASE_REF="${arg#*=}"
            ;;
        *)
            ;;
    esac
done

echo "═══════════════════════════════════════════════════"
echo "  POST-BUILD QUALITY GATE ($MODE mode)"
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

if [ "$MODE" = "incremental" ]; then
    # Determine base ref for git diff
    if [ -z "$BASE_REF" ]; then
        if git rev-parse --verify @{upstream} >/dev/null 2>&1; then
            BASE_REF="$(git rev-parse --verify @{upstream})"
        elif git rev-parse --verify origin/main >/dev/null 2>&1; then
            BASE_REF="$(git merge-base HEAD origin/main 2>/dev/null || echo "origin/main")"
        else
            BASE_REF="HEAD~1"
        fi
    fi

    echo "▶ Incremental diff analysis against: $BASE_REF"
    CHANGED_FILES=$(git diff --name-only "$BASE_REF" HEAD 2>/dev/null || true)
    CHANGED_LEAN_FILES=$(echo "$CHANGED_FILES" | grep '^lean/.*\.lean$' || true)

    if [ -z "$CHANGED_LEAN_FILES" ]; then
        echo "  ℹ No Lean source files modified in range ($BASE_REF..HEAD)."
        echo "  ⏩ Skipping Lake build and Lean semantic audits."
    else
        echo "  Modified Lean files:"
        echo "$CHANGED_LEAN_FILES" | sed 's/^/    - /'

        # 1. Locked Lake build (incremental targets or umbrella if configuration/all changed)
        if echo "$CHANGED_FILES" | grep -qE '(lakefile|InfoGeometry/All\.lean|InfoGeometry/Canonical/All\.lean)'; then
            run_check "Locked Lake build (umbrella)" \
                python3 tools/infra/run_locked_lake_build.py \
                  --wait-for-build-lock InfoGeometry.All
        else
            TARGETS=$(echo "$CHANGED_LEAN_FILES" | sed -e 's|^lean/||' -e 's|\.lean$||' -e 's|/|.|g')
            run_check "Locked Lake build (incremental targets: $TARGETS)" \
                python3 tools/infra/run_locked_lake_build.py \
                  --wait-for-build-lock $TARGETS
        fi

        # 2. Incremental Axiom & Debt Audit
        run_check "Axiom & Debt Audit (incremental)" \
            python3 tools/infra/axiom_audit.py --fail-on-gaps $CHANGED_LEAN_FILES

        # 3. Incremental Semantic Content Audit
        run_gate "Semantic Content Audit (incremental)" \
            python3 tools/quality/semantic_content_audit.py --file-prefix lean --gate
    fi

    # Fast scope and quarantine audits
    run_check "Tracked Lean Scope Audit" \
        python3 tools/quality/repo_lean_scope_audit.py --fail-on authoritative

    run_check "Quarantined Lean Artifact Audit" \
        python3 tools/quality/repo_lean_quarantine_audit.py

else
    # FULL REGRESSION GATE
    # 1. Locked root Lake build must pass
    run_check "Locked Lake build" \
        python3 tools/infra/run_locked_lake_build.py \
          --wait-for-build-lock InfoGeometry.All

    # 2. Every tracked Lean root is scanned; active source scope is strict.
    run_check "Tracked Lean Scope Audit" \
        python3 tools/quality/repo_lean_scope_audit.py --fail-on authoritative

    # 3. Quarantine contents stay visible but are not active proof sources.
    run_check "Quarantined Lean Artifact Audit" \
        python3 tools/quality/repo_lean_quarantine_audit.py

    # 4. Axiom & Debt Audit (sorry/axiom/admit count)
    run_check "Axiom & Debt Audit" python3 tools/infra/axiom_audit.py --fail-on-gaps

    # 5. Semantic vacuity audit (tracked all-subfolder review surface)
    run_check "Semantic Vacuity Audit (review-only)" \
        python3 tools/quality/semantic_vacuity_gate.py --tracked lean --fail-on none

    # 6. Semantic content audit (proof holes, trivial theorems)
    run_gate "Semantic Content Audit" python3 tools/quality/semantic_content_audit.py --file-prefix lean --gate

    # 7. Theory audit (sorry/admit/axiom counts)
    run_check "Theory Audit" bash scripts/quality/audit_theory.sh
fi

echo
echo "═══════════════════════════════════════════════════"
if [ $FAILED -eq 0 ]; then
    echo "  ✅ ALL CHECKS PASSED"
else
    echo "  ❌ SOME CHECKS FAILED / GATES FOUND ISSUES"
fi
echo "═══════════════════════════════════════════════════"

exit $FAILED
