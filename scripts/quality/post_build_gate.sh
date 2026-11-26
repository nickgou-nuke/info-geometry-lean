#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

mkdir -p artifacts

# Parse mode and flags
MODE="incremental"
BASE_REF=""
HEAD_REF="HEAD"
EXPLICIT_HEAD=false
CHANGED_ONLY="${POST_BUILD_GATE_CHANGED_ONLY:-0}"

for arg in "$@"; do
    case "$arg" in
        --incremental|-i|incremental)
            MODE="incremental"
            ;;
        --changed-only)
            MODE="incremental"
            CHANGED_ONLY="1"
            ;;
        --full|full)
            MODE="full"
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

ADDED_LAKEFILE_LEAN_TARGETS=""
ADDED_LAKEFILE_TEST_TARGETS=""
ADDED_SRC_LAKEFILE_TARGETS=""

classify_additive_lakefile_targets() {
    local cfg_file="$1"
    local src_prefix="$2"
    local diff_lines mod rel_path out_lean="" out_test=""
    diff_lines="$(git diff -U0 "$BASE_REF" "$HEAD_REF" -- "$cfg_file" 2>/dev/null | sed -n '/^@@/,$p' | grep -E '^[+-]' || true)"
    [ -n "$diff_lines" ] || return 1
    if grep -Eq '^-' <<<"$diff_lines"; then
        return 1
    fi
    if grep -Evq '^\+[[:space:]]*(\.(one|submodules|andSubmodules)[[:space:]]+`[A-Za-z0-9_.]+|`[A-Za-z0-9_.]+),?[[:space:]]*$' <<<"$diff_lines"; then
        return 1
    fi
    while IFS= read -r mod; do
        [ -n "$mod" ] || continue
        if [ "$mod" = "AuditNativeRun" ]; then
            continue
        fi
        rel_path="${mod//./\/}"
        if [ "$src_prefix" = "lean" ] && { [ -f "tests/${rel_path}.lean" ] || [ -d "tests/${rel_path}" ]; }; then
            out_test="${out_test:+$out_test }$mod"
        elif [ -f "${src_prefix}/${rel_path}.lean" ] || [ -d "${src_prefix}/${rel_path}" ]; then
            out_lean="${out_lean:+$out_lean }$mod"
        else
            return 1
        fi
    done < <(sed -E 's/^\+[[:space:]]*(\.(one|submodules|andSubmodules)[[:space:]]+)?`([A-Za-z0-9_.]+),?[[:space:]]*$/\3/' <<<"$diff_lines")
    if [ "$src_prefix" = "lean" ]; then
        ADDED_LAKEFILE_LEAN_TARGETS="$out_lean"
        ADDED_LAKEFILE_TEST_TARGETS="$out_test"
    else
        ADDED_SRC_LAKEFILE_TARGETS="$out_lean"
    fi
    return 0
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
    GRR_PURE_MATHLIB_RE='^lean/GRR/(GradedExp|GradedHom|ToddSeries)\.lean$'
    GRR_STACKS_LEAN_FILES=$(grep '^lean/GRR/.*\.lean$' <<<"$CHANGED_FILES" | grep -Ev "$GRR_PURE_MATHLIB_RE" | while IFS= read -r path; do
        if [ -f "$path" ]; then printf '%s\n' "$path"; fi
    done || true)
    CHANGED_LEAN_FILES=$(grep '^lean/.*\.lean$' <<<"$CHANGED_FILES" | { grep -Ev '^lean/GRR/.*\.lean$' || true; } | while IFS= read -r path; do
        if [ -f "$path" ]; then printf '%s\n' "$path"; fi
    done || true)
    GRR_PURE_LEAN_FILES=$(grep -E "$GRR_PURE_MATHLIB_RE" <<<"$CHANGED_FILES" | while IFS= read -r path; do
        if [ -f "$path" ]; then printf '%s\n' "$path"; fi
    done || true)
    if [ -n "$GRR_PURE_LEAN_FILES" ]; then
        CHANGED_LEAN_FILES="${CHANGED_LEAN_FILES:+$CHANGED_LEAN_FILES$'\n'}$GRR_PURE_LEAN_FILES"
    fi
    WILSON_CONTRIB_LEAN_FILES=$(grep -E '^contributions/(wilson|wilson-gaussian)/.*\.lean$' <<<"$CHANGED_FILES" | while IFS= read -r path; do
        if [ -f "$path" ]; then printf '%s\n' "$path"; fi
    done || true)
    DELETED_SRC_LEAN_FILES=$(git diff --diff-filter=D --name-only "$BASE_REF" "$HEAD_REF" -- 'src/*.lean' 'src/**/*.lean' || true)
    SRC_CHANGED_LEAN_FILES=$(grep '^src/.*\.lean$' <<<"$CHANGED_FILES" | while IFS= read -r path; do
        if [ -f "$path" ]; then printf '%s\n' "$path"; fi
    done || true)
    SRC_BUILD_CONFIG_FILES=$(grep '^lakefile\.src\.lean$' <<<"$CHANGED_FILES" || true)
    # `proofs/` is a root-package Lean library (`lean_lib proofs`), not a
    # nested Lake project. Route its changed modules explicitly instead of
    # treating every legacy proof edit as an unrouted source.
    DELETED_PROOFS_LEAN_FILES=$(git diff --diff-filter=D --name-only "$BASE_REF" "$HEAD_REF" -- 'proofs/*.lean' 'proofs/**/*.lean' || true)
    PROOFS_CHANGED_LEAN_FILES=$(grep '^proofs/.*\.lean$' <<<"$CHANGED_FILES" | while IFS= read -r path; do
        if [ -f "$path" ]; then printf '%s\n' "$path"; fi
    done || true)
    ALL_CHANGED_LEAN_FILES=$(git diff --diff-filter=d --name-only "$BASE_REF" "$HEAD_REF" 2>/dev/null | grep -E '(^|/)[^/]+\.lean$' || true)
    CHANGED_DISABLED_LEAN_FILES=$(git diff --diff-filter=d --name-only "$BASE_REF" "$HEAD_REF" 2>/dev/null | grep '\.lean\.disabled$' | while IFS= read -r path; do
        if [ -f "$path" ]; then printf '%s\n' "$path"; fi
    done || true)
    DELETED_TEST_LEAN_FILES=$(git diff --diff-filter=D --name-only "$BASE_REF" "$HEAD_REF" -- 'tests/*.lean' 'tests/**/*.lean' || true)
    TEST_LEAN_FILES=$(grep '^tests/.*\.lean$' <<<"$CHANGED_FILES" | while IFS= read -r path; do
        if [ -f "$path" ]; then printf '%s\n' "$path"; fi
    done || true)
    AUDIT_TOOL_LEAN_FILES=$(grep -E '^(tools/quality/(OperatorGeometryDeclarationAudit|TwoBoundaryDeclarationAudit)|tools/infra/axiom_index|lean/NoncommutativeGaugeAndBraidedHolonomy|verification/attention-query/AttentionDeclarationAudit|verification/courant-dirac/CapstoneDeclarationAudit|verification/(klein-operator-hierarchy|supplied-zorn-counterexample|witt-born-null-exactness|zorn-primal-dual)/Audit)\.lean$' <<<"$CHANGED_FILES" || true)
    # This selected package reuses canonical owners and has its own shared-lock
    # audit entry point. Route only its exact configuration and wrapper paths.
    CLIFFORD_PEIRCE_WALSH_FILES=$(grep -E '^verification/clifford-peirce-walsh/(lakefile\.lean|lake-manifest\.json|lean-toolchain|check\.py)$' <<<"$CHANGED_FILES" || true)
    # Lean umbrella modules are still ordinary Lake targets. Including one in
    # an incremental diff must build that changed module target, not promote
    # the whole root package to `InfoGeometry.All`.
    BUILD_CONFIG_FILES=$(grep -E '^(lakefile\.lean|lake-manifest\.json|lean-toolchain|lib/InfoGeometryCore/lakefile\.lean|lib/InfoGeometryCore/lake-manifest\.json)$|^lib/InfoGeometryCore/.*\.lean$' <<<"$CHANGED_FILES" || true)
    if [ "$CHANGED_ONLY" = "1" ]; then
        BUILD_CONFIG_FILES=""
        SRC_BUILD_CONFIG_FILES=""
    else
        if grep -Fxq 'lakefile.lean' <<<"$BUILD_CONFIG_FILES" && classify_additive_lakefile_targets "lakefile.lean" "lean"; then
            BUILD_CONFIG_FILES="$(grep -Fxv 'lakefile.lean' <<<"$BUILD_CONFIG_FILES" || true)"
        fi
        if grep -Fxq 'lakefile.src.lean' <<<"$SRC_BUILD_CONFIG_FILES" && classify_additive_lakefile_targets "lakefile.src.lean" "src"; then
            SRC_BUILD_CONFIG_FILES=""
        fi
    fi
    UNSUPPORTED_PACKAGE_CONFIGS=$(grep -E '^(lean/lakefile\.lean|lean/lake-manifest\.json|lean/lean-toolchain|lean_sandbox/lakefile\.lean|lean_sandbox/lake-manifest\.json|lean_sandbox/lean-toolchain|proofs/lakefile\.(toml|lean)|proofs/lake-manifest\.json|proofs/lean-toolchain|verification/spinorial-core/lakefile\.lean|verification/spinorial-core/lake-manifest\.json|verification/spinorial-core/lean-toolchain)$' <<<"$CHANGED_FILES" || true)
    UNROUTED_LEAN_FILES=$(grep -Ev '^(lakefile\.(src\.)?lean|lean-toolchain|lean/(Agent|AuditNative|AuditNativeRun|AuditStrict|B3PresentedGroup|CheckBasis|CheckTemp|DAG|Docs|Experimental|GrandPartitionAll|GrandPartitionEuler|GrandPartitionOnline|GrandPartitionPolynomial|GrandPartitionProbability|GrandPartitionRational|GrandPartitionRobustPoisson|GrandPartitionTransform|GrandUnifiedNoncommutativeOperatorSynthesis|InfoGeometry|KaplanskyCliffordBridge|NonIsoConf3OrlikSolomon|NoncommutativeGaugeAndBraidedHolonomy|Omega|PrimitiveSetsAboveX|SelfReference|Socratic|SplitOctonionBraidSU3|Test|TestFin|VirasoroProject|YangBaxterQSwap|YangBaxterZornBridge|ZornScalingFlow|ast_export_test|temp_test|test_fixes2|test_reflection|test_rpow|test_selfconcordance)\.lean|src/(Agent|AuditNative|AuditNativeRun|AuditStrict|B3PresentedGroup|CheckBasis|CheckTemp|DAG|Docs|Experimental|GrandPartitionAll|GrandPartitionEuler|GrandPartitionOnline|GrandPartitionPolynomial|GrandPartitionProbability|GrandPartitionRational|GrandPartitionRobustPoisson|GrandPartitionTransform|InfoGeometry|KaplanskyCliffordBridge|NonIsoConf3OrlikSolomon|Omega|PrimitiveSetsAboveX|SelfReference|Socratic|SplitOctonionBraidSU3|Test|TestFin|VirasoroProject|YangBaxterQSwap|YangBaxterZornBridge|ZornScalingFlow|ast_export_test|temp_test|test_fixes2|test_reflection|test_rpow|test_selfconcordance)\.lean|verification/clifford-peirce-walsh/lakefile\.lean|verification/attention-query/AttentionDeclarationAudit\.lean|verification/courant-dirac/CapstoneDeclarationAudit\.lean|verification/(klein-operator-hierarchy|supplied-zorn-counterexample|witt-born-null-exactness|zorn-primal-dual)/Audit\.lean|tools/quality/(OperatorGeometryDeclarationAudit|TwoBoundaryDeclarationAudit)\.lean|tools/infra/axiom_index\.lean)$|^lean/(InfoGeometry|DAG|GRR|Agent|Docs|Socratic|Omega|VirasoroProject|PrimitiveSetsAboveX|SelfReference|scripts|Experimental|sandbox|lean)/.*\.lean$|^src/(InfoGeometry|DAG|Agent|Docs|Socratic|Omega|VirasoroProject|SelfReference|scripts|Experimental|sandbox)/.*\.lean$|^proofs/.*\.lean$|^lib/InfoGeometryCore/.*\.lean$|^contributions/(wilson|wilson-gaussian)/.*\.lean$|^scratch/.*\.lean$|^tests/.*\.lean$' <<<"$ALL_CHANGED_LEAN_FILES" || true)

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

    if [ -z "$CHANGED_LEAN_FILES" ] && [ -z "$DELETED_LEAN_FILES" ] \
        && [ -z "$SRC_CHANGED_LEAN_FILES" ] && [ -z "$DELETED_SRC_LEAN_FILES" ] \
        && [ -z "$SRC_BUILD_CONFIG_FILES" ] \
        && [ -z "$PROOFS_CHANGED_LEAN_FILES" ] && [ -z "$DELETED_PROOFS_LEAN_FILES" ] \
        && [ -z "$BUILD_CONFIG_FILES" ] \
        && [ -z "$ADDED_LAKEFILE_LEAN_TARGETS" ] && [ -z "$ADDED_SRC_LAKEFILE_TARGETS" ]; then
        echo "  ℹ No Lean source or build-configuration files modified in range ($BASE_REF..$HEAD_REF)."
        echo "  ⏩ Skipping Lake build and Lean semantic audits."
    else
        if [ -n "$CHANGED_LEAN_FILES" ]; then
            echo "  Modified Lean files:"
            sed 's/^/    - /' <<<"$CHANGED_LEAN_FILES"
        fi
        if [ -n "$ADDED_LAKEFILE_LEAN_TARGETS" ]; then
            echo "  Added lakefile.lean targets: $ADDED_LAKEFILE_LEAN_TARGETS"
        fi
        if [ -n "$ADDED_SRC_LAKEFILE_TARGETS" ]; then
            echo "  Added lakefile.src.lean targets: $ADDED_SRC_LAKEFILE_TARGETS"
        fi
        if [ -n "$DELETED_LEAN_FILES" ]; then
            echo "  Deleted Lean files (umbrella build required to detect dangling imports):"
            sed 's/^/    - /' <<<"$DELETED_LEAN_FILES"
        fi
        if [ -n "$PROOFS_CHANGED_LEAN_FILES" ]; then
            echo "  Modified proofs Lean files:"
            sed 's/^/    - /' <<<"$PROOFS_CHANGED_LEAN_FILES"
        fi
        if [ -n "$DELETED_PROOFS_LEAN_FILES" ]; then
            echo "  Deleted proofs Lean files (proofs umbrella build required):"
            sed 's/^/    - /' <<<"$DELETED_PROOFS_LEAN_FILES"
        fi
        if [ -n "$BUILD_CONFIG_FILES" ]; then
            echo "  Modified build configuration / umbrella files:"
            sed 's/^/    - /' <<<"$BUILD_CONFIG_FILES"
        fi

        # 1. Locked Lake builds (incremental targets or umbrella if configuration/all changed)
        TARGETS=$(grep -E '^lean/(InfoGeometry|DAG|GRR|Agent|Docs|Socratic|Omega|VirasoroProject|PrimitiveSetsAboveX|SelfReference|scripts|Experimental|sandbox|lean)/.*\.lean$' <<<"$CHANGED_LEAN_FILES" | sed -e 's|^lean/||' -e 's|\.lean$||' -e 's|/|.|g' || true)
        TOP_LEVEL_TARGETS=$(grep -E '^lean/[^/]+\.lean$' <<<"$CHANGED_LEAN_FILES" | grep -Ev '^lean/(lakefile|AuditNativeRun|NoncommutativeGaugeAndBraidedHolonomy)\.lean$' | sed -e 's|^lean/||' -e 's|\.lean$||' || true)
        if [ -n "$TOP_LEVEL_TARGETS" ]; then
            TARGETS="${TARGETS:+$TARGETS }$TOP_LEVEL_TARGETS"
        fi
        if [ -n "$ADDED_LAKEFILE_LEAN_TARGETS" ]; then
            TARGETS="${TARGETS:+$TARGETS }$ADDED_LAKEFILE_LEAN_TARGETS"
        fi
        if [ -n "$TARGETS" ]; then
            TARGETS="$(tr ' ' '\n' <<<"$TARGETS" | grep -Ev '^AuditNativeRun$' | awk 'NF && !seen[$0]++' | paste -sd' ' - || true)"
        fi
        if [ -n "$BUILD_CONFIG_FILES" ] || [ -n "$DELETED_LEAN_FILES" ]; then
            run_check "Locked Lake build (umbrella)" \
                python3 tools/infra/run_locked_lake_build.py \
                  --wait-for-build-lock InfoGeometry.All
            EXTRA_NON_IG_TARGETS=$(tr ' ' '\n' <<<"$TARGETS" | grep -Ev '^($|InfoGeometry(\.|$)|AuditNative$|AuditNativeRun$)' || true)
            if [ -n "$EXTRA_NON_IG_TARGETS" ]; then
                run_check "Locked Lake build (changed non-umbrella targets)" \
                    python3 tools/infra/run_locked_lake_build.py \
                      --wait-for-build-lock $EXTRA_NON_IG_TARGETS
            fi
        fi
        if [ -n "$DELETED_PROOFS_LEAN_FILES" ]; then
            run_check "Locked Lake build (proofs umbrella)" \
                python3 tools/infra/run_locked_lake_build.py \
                  --wait-for-build-lock proofs
        fi
        if [ -z "$BUILD_CONFIG_FILES" ] && [ -z "$DELETED_LEAN_FILES" ]; then
            if [ -n "$TARGETS" ]; then
                run_check "Locked Lake build (incremental targets)" \
                    python3 tools/infra/run_locked_lake_build.py \
                      --wait-for-build-lock $TARGETS
            fi
        fi
        if [ -z "$DELETED_PROOFS_LEAN_FILES" ]; then
            PROOFS_TARGETS=$(grep -E '^proofs/.*\.lean$' <<<"$PROOFS_CHANGED_LEAN_FILES" | sed -e 's|^proofs/||' -e 's|\.lean$||' -e 's|/|.|g' -e 's|^|proofs.|' || true)
            if [ -n "$PROOFS_TARGETS" ]; then
                run_check "Locked Lake build (proofs incremental targets)" \
                    python3 tools/infra/run_locked_lake_build.py \
                      --wait-for-build-lock $PROOFS_TARGETS
            fi
        fi

        # The maintained source lane uses lakefile.src.lean and .lake/src-build;
        # accepting a src path must never silently reuse canonical artifacts.
        if [ -n "$SRC_BUILD_CONFIG_FILES" ] || [ -n "$DELETED_SRC_LEAN_FILES" ]; then
            run_check "Locked Lake build (src umbrella)" \
                python3 tools/infra/run_locked_lake_build.py \
                  --wait-for-build-lock --source-lane InfoGeometry.All
        elif [ -n "$SRC_CHANGED_LEAN_FILES" ] || [ -n "$ADDED_SRC_LAKEFILE_TARGETS" ]; then
            SRC_TARGETS=""
            if [ -n "$SRC_CHANGED_LEAN_FILES" ]; then
                SRC_TARGETS=$(sed -e 's|^src/||' -e 's|\.lean$||' -e 's|/|.|g' <<<"$SRC_CHANGED_LEAN_FILES" | grep -Ev '^AuditNativeRun$' || true)
            fi
            if [ -n "$ADDED_SRC_LAKEFILE_TARGETS" ]; then
                SRC_TARGETS="${SRC_TARGETS:+$SRC_TARGETS }$ADDED_SRC_LAKEFILE_TARGETS"
            fi
            SRC_TARGETS="$(tr ' ' '\n' <<<"$SRC_TARGETS" | grep -Ev '^AuditNativeRun$' | awk 'NF && !seen[$0]++' | paste -sd' ' - || true)"
            if [ -n "$SRC_TARGETS" ]; then
                run_check "Locked Lake build (src incremental targets)" \
                    python3 tools/infra/run_locked_lake_build.py \
                      --wait-for-build-lock --source-lane $SRC_TARGETS
            fi
        fi

        # 2. Incremental Axiom & Debt Audit
        AUDIT_LEAN_FILES=$(printf '%s\n%s\n%s\n' "$CHANGED_LEAN_FILES" "$SRC_CHANGED_LEAN_FILES" "$PROOFS_CHANGED_LEAN_FILES" | sed '/^[[:space:]]*$/d' || true)
        if [ -n "$AUDIT_LEAN_FILES" ]; then
            run_check "Axiom & Debt Audit (incremental)" \
                python3 tools/infra/axiom_audit.py --fail-on-gaps $AUDIT_LEAN_FILES
        else
            echo "  ℹ No changed Lean source files for the incremental axiom/debt audit."
        fi

        # 3. Incremental Semantic Content Audit
        if [ -n "$BUILD_CONFIG_FILES" ] || [ -n "$DELETED_LEAN_FILES" ]; then
            run_gate "Semantic Content Audit (incremental)" \
                python3 tools/quality/semantic_content_audit.py --file-prefix lean --gate
        elif [ -n "$CHANGED_LEAN_FILES" ]; then
            LEAN_SEMANTIC_ARGS=()
            while IFS= read -r path; do
                [ -n "$path" ] || continue
                LEAN_SEMANTIC_ARGS+=(--file-prefix "$path")
            done <<<"$CHANGED_LEAN_FILES"
            run_gate "Semantic Content Audit (incremental)" \
                python3 tools/quality/semantic_content_audit.py "${LEAN_SEMANTIC_ARGS[@]}" --gate
        fi
        if [ -n "$DELETED_PROOFS_LEAN_FILES" ]; then
            run_gate "Semantic Content Audit (proofs incremental)" \
                python3 tools/quality/semantic_content_audit.py --file-prefix proofs --gate
        elif [ -n "$PROOFS_CHANGED_LEAN_FILES" ]; then
            PROOFS_SEMANTIC_ARGS=()
            while IFS= read -r path; do
                [ -n "$path" ] || continue
                PROOFS_SEMANTIC_ARGS+=(--file-prefix "$path")
            done <<<"$PROOFS_CHANGED_LEAN_FILES"
            run_gate "Semantic Content Audit (proofs incremental)" \
                python3 tools/quality/semantic_content_audit.py "${PROOFS_SEMANTIC_ARGS[@]}" --gate
        fi
        if [ -n "$SRC_BUILD_CONFIG_FILES" ] || [ -n "$DELETED_SRC_LEAN_FILES" ]; then
            run_gate "Semantic Content Audit (src incremental)" \
                python3 tools/quality/semantic_content_audit.py --file-prefix src --gate
        elif [ -n "$SRC_CHANGED_LEAN_FILES" ]; then
            SRC_SEMANTIC_ARGS=()
            while IFS= read -r path; do
                [ -n "$path" ] || continue
                SRC_SEMANTIC_ARGS+=(--file-prefix "$path")
            done <<<"$SRC_CHANGED_LEAN_FILES"
            run_gate "Semantic Content Audit (src incremental)" \
                python3 tools/quality/semantic_content_audit.py "${SRC_SEMANTIC_ARGS[@]}" --gate
        fi
    fi

    # Test files are compiled as the InfoGeometryTestSuite Lake library. Build
    # changed test module targets incrementally unless test deletions or root
    # build-config changes require the full test suite umbrella.
    if [ -n "$DELETED_TEST_LEAN_FILES" ] || { [ -n "$BUILD_CONFIG_FILES" ] && [ -n "$TEST_LEAN_FILES" ]; }; then
        run_check "Locked Lake build (InfoGeometryTestSuite)" \
            python3 tools/infra/run_locked_lake_build.py \
              --wait-for-build-lock InfoGeometryTestSuite
    elif [ -n "$TEST_LEAN_FILES" ] || [ -n "$ADDED_LAKEFILE_TEST_TARGETS" ]; then
        TEST_TARGETS=""
        if [ -n "$TEST_LEAN_FILES" ]; then
            TEST_TARGETS=$(sed -e 's|^tests/||' -e 's|\.lean$||' -e 's|/|.|g' <<<"$TEST_LEAN_FILES")
        fi
        if [ -n "$ADDED_LAKEFILE_TEST_TARGETS" ]; then
            TEST_TARGETS="${TEST_TARGETS:+$TEST_TARGETS }$ADDED_LAKEFILE_TEST_TARGETS"
        fi
        TEST_TARGETS="$(tr ' ' '\n' <<<"$TEST_TARGETS" | awk 'NF && !seen[$0]++' | paste -sd' ' - || true)"
        if [ -n "$TEST_TARGETS" ]; then
            run_check "Locked Lake build (test incremental targets)" \
                python3 tools/infra/run_locked_lake_build.py \
                  --wait-for-build-lock $TEST_TARGETS
        fi
    fi

    # This repository-wide declaration audit is a standalone Lean command
    # module under tools/quality, outside the root Lake library. Elaborate it
    # directly under the shared lock whenever its source changes.
    if [ -n "$AUDIT_TOOL_LEAN_FILES" ]; then
        while IFS= read -r audit_file; do
            [ -n "$audit_file" ] || continue
            run_check "Kernel check ($audit_file)" \
                python3 tools/infra/run_locked_lean.py \
                  --wait-for-build-lock "$audit_file"
        done <<<"$AUDIT_TOOL_LEAN_FILES"
    fi

    # Keep this package audit in addition to every existing root/source route.
    if [ -n "$CLIFFORD_PEIRCE_WALSH_FILES" ]; then
        run_check "Locked Clifford-Peirce-Walsh declaration audit" \
            python3 verification/clifford-peirce-walsh/check.py
    fi

    # External-Stacks-dependent GRR port modules (full StacksFrontier build
    # targets external_refs/Stacks v4.34.0-rc2/v4.35.0 per lean/GRR/README.md).
    if [ -n "$GRR_STACKS_LEAN_FILES" ]; then
        echo "  ℹ StacksFrontier-dependent GRR files audited here; external Stacks v4.34.0-rc2/v4.35.0 build note: lean/GRR/README.md."
        run_check "Axiom & Debt Audit (GRR Stacks-dependent port)" \
            python3 tools/infra/axiom_audit.py --fail-on-gaps $GRR_STACKS_LEAN_FILES
        run_check "OpenGauss Screener (GRR Stacks-dependent port)" \
            python3 tools/infra/opengauss_screener.py $GRR_STACKS_LEAN_FILES
    fi

    # External 4D_Wilson_Loop_RG contribution overlays (compiled against upstream
    # v4.34.0-rc2/v4.36.0 in .github/workflows/wilson-{gaussian-upstream,upstream-validation}.yml).
    if [ -n "$WILSON_CONTRIB_LEAN_FILES" ]; then
        echo "  ℹ External 4D_Wilson_Loop_RG compilation is covered by .github/workflows/wilson-upstream-validation.yml and .github/workflows/wilson-gaussian-upstream.yml."
        run_check "External Wilson contribution manifest SHA-256 & evidence check" \
            python3 -c '
import hashlib, json
from pathlib import Path
wg = json.loads(Path("contributions/wilson-gaussian/source-manifest.json").read_text())
for rel, exp in wg["overlay_sha256"].items():
    p = Path("contributions/wilson-gaussian/overlay") / rel
    assert p.is_file(), f"Missing {p}"
    got = hashlib.sha256(p.read_bytes()).hexdigest()
    assert got == exp, f"Hash mismatch for {p}: {got} != {exp}"
pkg = Path("contributions/wilson/validation/evidence/package-ff8e163.json")
assert pkg.is_file() and pkg.stat().st_size > 0, f"Missing {pkg}"
for cand in ("cutoff", "gaussian", "gram", "states"):
    for fname in ("source-inventory.json", "axiom-audit.json", "artifact-receipt.json"):
        ep = Path(f"contributions/wilson/validation/evidence/exact-{cand}-ff8e163") / fname
        assert ep.is_file() and ep.stat().st_size > 0, f"Missing {ep}"
n_wg = len(wg["overlay_sha256"])
print(f"Verified wilson-gaussian overlay manifest ({n_wg} files) and wilson CI evidence inventories.")
'
        run_check "Axiom & Debt Audit (Wilson upstream contributions)" \
            python3 tools/infra/axiom_audit.py --fail-on-gaps $WILSON_CONTRIB_LEAN_FILES
        run_check "OpenGauss Screener (Wilson upstream contributions)" \
            python3 tools/infra/opengauss_screener.py $WILSON_CONTRIB_LEAN_FILES
    fi

    # Incremental scope and quarantine audits
    if [ -n "$BUILD_CONFIG_FILES" ]; then
        run_check "Tracked Lean Scope Audit" \
            python3 tools/quality/repo_lean_scope_audit.py --fail-on authoritative
    else
        SCOPE_AUDIT_FILES=()
        while IFS= read -r path; do
            [ -n "$path" ] || continue
            if [ -f "$path" ]; then
                SCOPE_AUDIT_FILES+=("$path")
            fi
        done <<<"$ALL_CHANGED_LEAN_FILES"
        if [ ${#SCOPE_AUDIT_FILES[@]} -gt 0 ]; then
            run_check "Tracked Lean Scope Audit (incremental)" \
                python3 tools/quality/repo_lean_scope_audit.py --fail-on authoritative "${SCOPE_AUDIT_FILES[@]}"
        else
            echo "  ℹ No changed .lean files for incremental scope audit."
        fi
    fi

    if [ -n "$CHANGED_DISABLED_LEAN_FILES" ]; then
        QUARANTINE_AUDIT_FILES=()
        while IFS= read -r path; do
            [ -n "$path" ] || continue
            QUARANTINE_AUDIT_FILES+=("$path")
        done <<<"$CHANGED_DISABLED_LEAN_FILES"
        run_check "Quarantined Lean Artifact Audit (incremental)" \
            python3 tools/quality/repo_lean_quarantine_audit.py "${QUARANTINE_AUDIT_FILES[@]}"
    else
        echo "  ℹ No changed .lean.disabled files for incremental quarantine audit."
    fi

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
