#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

mkdir -p artifacts

# Parse mode and flags
MODE="full"
BASE_REF=""
HEAD_REF="HEAD"
EXPLICIT_HEAD=false

for arg in "$@"; do
    case "$arg" in
        --incremental|-i|incremental)
            MODE="incremental"
            ;;
        --base=*)
            BASE_REF="${arg#*=}"
            ;;
        --head=*)
            HEAD_REF="${arg#*=}"
            EXPLICIT_HEAD=true
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
        if [ "$EXPLICIT_HEAD" = true ]; then
            echo "  ❌ --head requires an explicit --base; refusing an ambiguous diff range." >&2
            exit 2
        fi
        if git rev-parse --verify @{upstream} >/dev/null 2>&1; then
            BASE_REF="$(git rev-parse --verify @{upstream})"
        elif git rev-parse --verify origin/main >/dev/null 2>&1; then
            BASE_REF="$(git merge-base "$HEAD_REF" origin/main 2>/dev/null || echo "origin/main")"
        else
            BASE_REF="HEAD~1"
        fi
    fi

    if ! git rev-parse --verify "${BASE_REF}^{tree}" >/dev/null 2>&1; then
        echo "  ❌ Cannot resolve incremental base tree: $BASE_REF" >&2
        exit 2
    fi
    if ! git rev-parse --verify "${HEAD_REF}^{commit}" >/dev/null 2>&1; then
        echo "  ❌ Cannot resolve incremental target commit: $HEAD_REF" >&2
        exit 2
    fi

    echo "▶ Incremental diff analysis: $BASE_REF..$HEAD_REF"
    if ! CHANGED_FILES=$(git diff --name-only "$BASE_REF" "$HEAD_REF" 2>/dev/null); then
        echo "  ❌ Could not compute incremental diff range: $BASE_REF..$HEAD_REF" >&2
        exit 2
    fi
    DELETED_LEAN_FILES=$(git diff --diff-filter=D --name-only "$BASE_REF" "$HEAD_REF" -- 'lean/*.lean' 'lean/**/*.lean' || true)
    CHANGED_LEAN_FILES=$(grep '^lean/.*\.lean$' <<<"$CHANGED_FILES" | while IFS= read -r path; do
        if [ -f "$path" ]; then printf '%s\n' "$path"; fi
    done || true)
    ALL_CHANGED_LEAN_FILES=$(git diff --diff-filter=d --name-only "$BASE_REF" "$HEAD_REF" 2>/dev/null | grep -E '(^|/)[^/]+\.lean$' || true)
    BUILD_CONFIG_FILES=$(grep -E '^(lakefile\.lean|lake-manifest\.json|lean-toolchain|lib/InfoGeometryCore/lakefile\.lean|lib/InfoGeometryCore/lake-manifest\.json|lean/InfoGeometry\.lean|lean/InfoGeometry/All\.lean|lean/InfoGeometry/Canonical/All\.lean)$|^lib/InfoGeometryCore/.*\.lean$' <<<"$CHANGED_FILES" || true)
    UNSUPPORTED_PACKAGE_CONFIGS=$(grep -E '^(lean/lakefile\.lean|lean/lake-manifest\.json|lean/lean-toolchain|lean_sandbox/lakefile\.lean|lean_sandbox/lake-manifest\.json|lean_sandbox/lean-toolchain|proofs/lakefile\.(toml|lean)|proofs/lake-manifest\.json|proofs/lean-toolchain|verification/spinorial-core/lakefile\.lean|verification/spinorial-core/lake-manifest\.json|verification/spinorial-core/lean-toolchain)$' <<<"$CHANGED_FILES" || true)
    UNROUTED_LEAN_FILES=$(grep -Ev '^(lakefile\.lean|lean-toolchain|lean/InfoGeometry\.lean)$|^lean/(InfoGeometry|DAG|Agent|Docs|Socratic|Omega|VirasoroProject|PrimitiveSetsAboveX|SelfReference|scripts|Experimental)/.*\.lean$|^lib/InfoGeometryCore/.*\.lean$|^scratch/.*\.lean$' <<<"$ALL_CHANGED_LEAN_FILES" || true)

    if [ -n "$UNSUPPORTED_PACKAGE_CONFIGS" ]; then
        echo "  ❌ Nested Lake project configuration changed, but this root gate has no package-specific locked build route:" >&2
        sed 's/^/    - /' <<<"$UNSUPPORTED_PACKAGE_CONFIGS" >&2
        echo "  Run that package's dedicated build/CI gate before pushing; refusing to certify it as a root-package change." >&2
        exit 2
    fi
    if [ -n "$UNROUTED_LEAN_FILES" ]; then
        echo "  ❌ Lean source changes fall outside the package targets routed by this root gate:" >&2
        sed 's/^/    - /' <<<"$UNROUTED_LEAN_FILES" >&2
        echo "  Add an explicit locked build route or run the owning package's dedicated gate; refusing to skip compilation." >&2
        exit 2
    fi

    if [ -z "$CHANGED_LEAN_FILES" ] && [ -z "$DELETED_LEAN_FILES" ] && [ -z "$BUILD_CONFIG_FILES" ]; then
        echo "  ℹ No Lean source or build-configuration files modified in range ($BASE_REF..$HEAD_REF)."
        echo "  ⏩ Skipping Lake build and Lean semantic audits."
    else
        if [ -n "$CHANGED_LEAN_FILES" ]; then
            echo "  Modified Lean files:"
            sed 's/^/    - /' <<<"$CHANGED_LEAN_FILES"
        fi
        if [ -n "$DELETED_LEAN_FILES" ]; then
            echo "  Deleted Lean files (umbrella build required to detect dangling imports):"
            sed 's/^/    - /' <<<"$DELETED_LEAN_FILES"
        fi
        if [ -n "$BUILD_CONFIG_FILES" ]; then
            echo "  Modified build configuration / umbrella files:"
            sed 's/^/    - /' <<<"$BUILD_CONFIG_FILES"
        fi

        # 1. Locked Lake build (incremental targets or umbrella if configuration/all changed)
        if [ -n "$BUILD_CONFIG_FILES" ] || [ -n "$DELETED_LEAN_FILES" ]; then
            run_check "Locked Lake build (umbrella)" \
                python3 tools/infra/run_locked_lake_build.py \
                  --wait-for-build-lock InfoGeometry.All
        else
            TARGETS=$(grep -E '^lean/(InfoGeometry|DAG|Agent|Docs|Socratic|Omega|VirasoroProject|PrimitiveSetsAboveX|SelfReference|scripts|Experimental)/.*\.lean$' <<<"$CHANGED_LEAN_FILES" | sed -e 's|^lean/||' -e 's|\.lean$||' -e 's|/|.|g' || true)
            if [ -n "$TARGETS" ]; then
                run_check "Locked Lake build (incremental targets)" \
                    python3 tools/infra/run_locked_lake_build.py \
                      --wait-for-build-lock $TARGETS
            fi
        fi

        # 2. Incremental Axiom & Debt Audit
        if [ -n "$CHANGED_LEAN_FILES" ]; then
            run_check "Axiom & Debt Audit (incremental)" \
                python3 tools/infra/axiom_audit.py --fail-on-gaps $CHANGED_LEAN_FILES
        else
            echo "  ℹ No changed Lean source files for the incremental axiom/debt audit."
        fi

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

    # 5. Semantic vacuity audit over every tracked Lean source in the repository.
    # Error-level findings and incomplete source coverage block this gate;
    # warning-level heuristic findings remain visible for independent review.
    run_check "Semantic Vacuity Audit (repository-wide)" \
        python3 tools/quality/semantic_vacuity_gate.py --tracked . --fail-on error --fail-prefix lean/ \
          --json-out artifacts/vacuity_full.json

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
