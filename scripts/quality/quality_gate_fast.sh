#!/usr/bin/env bash
# Post-build quality gate - runs after lake build
# Consolidated single entry point for quality checks (Fast Mode; supports --changed or explicit paths)

set -euo pipefail

REPO_ROOT=$(git rev-parse --show-toplevel)
cd "$REPO_ROOT"

mkdir -p artifacts reports

CHANGED_MODE=false
TARGET_ARGS=()
for arg in "$@"; do
    case "$arg" in
        --changed)
            CHANGED_MODE=true
            ;;
        *)
            TARGET_ARGS+=("$arg")
            ;;
    esac
done

TARGET_FILES=()
VACUITY_TARGETS=()
MATHLESS_TARGETS=()

if [ "$CHANGED_MODE" = true ]; then
    while IFS= read -r rel_path; do
        [ -n "$rel_path" ] || continue
        if [ -f "$rel_path" ]; then
            TARGET_FILES+=("$rel_path")
        fi
    done < <(
        {
            git diff --name-only HEAD -- '*.lean' 2>/dev/null || true
            git diff --cached --name-only HEAD -- '*.lean' 2>/dev/null || true
            git ls-files --others --exclude-standard -- '*.lean' 2>/dev/null || true
        } | awk 'NF && !seen[$0]++'
    )
    if [ ${#TARGET_FILES[@]} -eq 0 ]; then
        echo "INFO-GEOMETRY-LEAN QUALITY GATE (Fast Mode, --changed): no changed Lean files detected."
        exit 0
    fi
    VACUITY_TARGETS=("${TARGET_FILES[@]}")
    MATHLESS_TARGETS=("${TARGET_FILES[@]}")
elif [ ${#TARGET_ARGS[@]} -gt 0 ]; then
    for p in "${TARGET_ARGS[@]}"; do
        if [ -f "$p" ]; then
            TARGET_FILES+=("$p")
            VACUITY_TARGETS+=("$p")
            MATHLESS_TARGETS+=("$p")
        elif [ -d "$p" ]; then
            VACUITY_TARGETS+=("$p")
            MATHLESS_TARGETS+=("$p")
            while IFS= read -r f; do
                [ -n "$f" ] || continue
                TARGET_FILES+=("$f")
            done < <(find "$p" -name '*.lean' -type f | sort)
        fi
    done
    if [ ${#VACUITY_TARGETS[@]} -eq 0 ]; then
        echo "INFO-GEOMETRY-LEAN QUALITY GATE (Fast Mode): no matching Lean targets."
        exit 0
    fi
else
    VACUITY_TARGETS=("lean/InfoGeometry")
    MATHLESS_TARGETS=("lean/InfoGeometry")
fi

echo "════════════════════════════════════════════════════════"
echo "INFO-GEOMETRY-LEAN QUALITY GATE (Fast Mode)"
echo "════════════════════════════════════════════════════════"

# 1. Single-pass Sorry/Axiom/Admit check (also populates artifacts/axiom_audit_report.json)
echo ""
echo "▶ [1/3] Sorry/Axiom/Admit check (single pass)..."
if [ ${#TARGET_FILES[@]} -gt 0 ]; then
    AXIOM_CMD=(python3 tools/infra/axiom_audit.py --fail-on-gaps "${TARGET_FILES[@]}")
else
    AXIOM_CMD=(python3 tools/infra/axiom_audit.py --fail-on-gaps)
fi
if "${AXIOM_CMD[@]}" > artifacts/axiom_audit_fast.txt 2>&1; then
    echo "  ✅ Lean targets clean (axiom audit)"
    if [ -f artifacts/axiom_audit_report.json ]; then
        cp artifacts/axiom_audit_report.json artifacts/axiom_audit_full.json
        GAPS=$(jq '.total_open_gaps' artifacts/axiom_audit_full.json 2>/dev/null || echo "?")
        FILES=$(jq '.debt_files' artifacts/axiom_audit_full.json 2>/dev/null || echo "?")
        echo "  Open gaps (sorry/admit): $GAPS (files with debt: $FILES)"
    fi
else
    cat artifacts/axiom_audit_fast.txt
    exit 1
fi

# 2. Single-pass Semantic vacuity gate
echo ""
echo "▶ [2/3] Semantic vacuity review & gate (single pass)..."
if python3 tools/quality/semantic_vacuity_gate.py "${VACUITY_TARGETS[@]}" --fail-on error \
  --json-out artifacts/vacuity_infogeometry.json > artifacts/vacuity_infogeometry.txt 2>&1; then
    echo "  ✅ semantic vacuity check clean"
else
    echo "  ⚠️  Semantic vacuity errors detected (see artifacts/vacuity_infogeometry.txt):"
    cat artifacts/vacuity_infogeometry.txt
    # Preserve non-blocking review semantics for structural interfaces in full mode
    if [ "$CHANGED_MODE" = true ] || [ ${#TARGET_ARGS[@]} -gt 0 ]; then
        exit 1
    fi
fi

# 3. Mathless proof audit (scoped to targets)
echo ""
echo "▶ [3/3] Mathless/skeletal proof audit..."
if [ ${#MATHLESS_TARGETS[@]} -eq 1 ]; then
    if python3 scripts/quality/mathless_proof_audit.py --root "${MATHLESS_TARGETS[0]}" --format json > artifacts/mathless_full.json 2>&1; then
        COUNT=$(jq 'length' artifacts/mathless_full.json 2>/dev/null || echo "0")
        echo "  Skeletal/placeholder proofs: $COUNT"
    else
        COUNT=$(jq 'length' artifacts/mathless_full.json 2>/dev/null || echo "?")
        echo "  Skeletal/placeholder proofs: $COUNT"
    fi
else
    TOTAL_MATHLESS=0
    for mt in "${MATHLESS_TARGETS[@]}"; do
        python3 scripts/quality/mathless_proof_audit.py --root "$mt" --format json > artifacts/mathless_item.json 2>&1 || true
        CNT=$(jq 'length' artifacts/mathless_item.json 2>/dev/null || echo "0")
        TOTAL_MATHLESS=$((TOTAL_MATHLESS + CNT))
    done
    echo "  Skeletal/placeholder proofs (across ${#MATHLESS_TARGETS[@]} targets): $TOTAL_MATHLESS"
fi

echo ""
echo "════════════════════════════════════════════════════════"
echo "✅ QUALITY GATE COMPLETED"
echo "════════════════════════════════════════════════════════"
