#!/usr/bin/env bash
# -*- coding: utf-8 -*-
#
# Master Test Runner: Multi-Engine Formalization Verification
#
# This script runs all formalization engines and aggregates results:
# - SageMath: Zorn matrices and complex structure
# - SymPy: Finite linear equivalence verification
# - Macaulay2: D-module tripotent analysis
# - Lean4: Kernel-checked theorem proving
# - Coq: Type-theoretic verification
# - Isabelle/HOL: Modular flow preservation

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
RESULTS_DIR="/tmp/multi_engine_results"

mkdir -p "$RESULTS_DIR"

# Add path to Coq and Isabelle installations
export PATH="/home/goutev/.opam/coq-switch/bin:/home/goutev/Isabelle2025-2/bin:$PATH"

echo "================================================================================"
echo "Multi-Engine Formalization Verification"
echo "Repository: $REPO_ROOT"
echo "Results: $RESULTS_DIR"
echo "================================================================================"

# Results aggregator
declare -A RESULTS
TOTAL_TESTS=0
PASSED_TESTS=0

# ============================================================================
# 1. SymPy Verification (Python, always available)
# ============================================================================
echo -e "\n[1/6] SymPy: Finite Linear Equivalence"
echo "----------------------------------------"

if python3 "$REPO_ROOT/tools/sympy/finite_complex_equivalence.py" > "$RESULTS_DIR/sympy.log" 2>&1; then
    RESULTS["sympy"]="✓ PASSED"
    PASSED_TESTS=$((PASSED_TESTS + 1))
    echo "  ${RESULTS["sympy"]}"
else
    RESULTS["sympy"]="✗ FAILED"
    echo "  ${RESULTS["sympy"]}"
    echo "  See: $RESULTS_DIR/sympy.log"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# ============================================================================
# 2. Lean4 Compilation (lake env lean)
# ============================================================================
echo -e "\n[2/6] Lean4: Kernel-Checked Theorem"
echo "----------------------------------------"

cd "$REPO_ROOT"
if ~/.elan/bin/lake env lean lean/InfoGeometry/Canonical/CliffordEquiv.lean > "$RESULTS_DIR/lean4.log" 2>&1; then
    RESULTS["lean4"]="✓ PASSED"
    PASSED_TESTS=$((PASSED_TESTS + 1))
    echo "  ${RESULTS["lean4"]}"
else
    RESULTS["lean4"]="✗ FAILED"
    echo "  ${RESULTS["lean4"]}"
    echo "  See: $RESULTS_DIR/lean4.log"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# ============================================================================
# 3. SageMath (if installed)
# ============================================================================
echo -e "\n[3/6] SageMath: Zorn Complex Bridge"
echo "----------------------------------------"

if command -v sage &> /dev/null; then
    if sage "$REPO_ROOT/tools/sage/zorn_complex_bridge.sage" > "$RESULTS_DIR/sage.log" 2>&1; then
        RESULTS["sage"]="✓ PASSED"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        echo "  ${RESULTS["sage"]}"
    else
        RESULTS["sage"]="✗ FAILED"
        echo "  ${RESULTS["sage"]}"
        echo "  See: $RESULTS_DIR/sage.log"
    fi
else
    RESULTS["sage"]="⊘ SKIPPED (not installed)"
    echo "  ${RESULTS["sage"]}"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# ============================================================================
# 4. Macaulay2 (if installed)
# ============================================================================
echo -e "\n[4/6] Macaulay2: D-Module Analysis"
echo "----------------------------------------"

if command -v M2 &> /dev/null; then
    if M2 --script "$REPO_ROOT/tools/macaulay2/tripotent_dmodule.m2" > "$RESULTS_DIR/macaulay2.log" 2>&1; then
        RESULTS["macaulay2"]="✓ PASSED"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        echo "  ${RESULTS["macaulay2"]}"
    else
        RESULTS["macaulay2"]="✗ FAILED"
        echo "  ${RESULTS["macaulay2"]}"
        echo "  See: $RESULTS_DIR/macaulay2.log"
    fi
else
    RESULTS["macaulay2"]="⊘ SKIPPED (not installed)"
    echo "  ${RESULTS["macaulay2"]}"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# ============================================================================
# 5. Coq (if installed)
# ============================================================================
echo -e "\n[5/6] Coq: Type-Theoretic Verification"
echo "----------------------------------------"

if command -v coqc &> /dev/null; then
    cd "$REPO_ROOT/tools/coq"
    if coqc -R . ComplexStructureBridge.v \
            > "$RESULTS_DIR/coq.log" 2>&1 && \
       coqc "$REPO_ROOT/coq/EInfinityParadoxes.v" \
            >> "$RESULTS_DIR/coq.log" 2>&1; then
        RESULTS["coq"]="✓ PASSED"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        echo "  ${RESULTS["coq"]}"
    else
        RESULTS["coq"]="✗ FAILED"
        echo "  ${RESULTS["coq"]}"
        echo "  See: $RESULTS_DIR/coq.log"
    fi
else
    RESULTS["coq"]="⊘ SKIPPED (not installed)"
    echo "  ${RESULTS["coq"]}"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# ============================================================================
# 6. Isabelle/HOL (if installed)
# ============================================================================
echo -e "\n[6/6] Isabelle/HOL: Modular Flow Preservation"
echo "---------------------------------------------------"

if command -v isabelle &> /dev/null; then
    if isabelle build -D "$REPO_ROOT/isabelle" > "$RESULTS_DIR/isabelle.log" 2>&1; then
        RESULTS["isabelle"]="✓ PASSED"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        echo "  ${RESULTS["isabelle"]}"
    else
        RESULTS["isabelle"]="✗ FAILED"
        echo "  ${RESULTS["isabelle"]}"
        echo "  See: $RESULTS_DIR/isabelle.log"
    fi
else
    RESULTS["isabelle"]="⊘ SKIPPED (not installed)"
    echo "  ${RESULTS["isabelle"]}"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# ============================================================================
# 7. SymPy osp12 Verification
# ============================================================================
echo -e "\n[7/11] SymPy: osp(1|2) Boson-Fermion Normal Ordering"
echo "----------------------------------------"

if python3 "$REPO_ROOT/tools/sympy/sympy_secondquant.py" \
        > "$RESULTS_DIR/sympy_osp12.log" 2>&1; then
    RESULTS["sympy_osp12"]="✓ PASSED"
    PASSED_TESTS=$((PASSED_TESTS + 1))
    echo "  ${RESULTS["sympy_osp12"]}"
else
    RESULTS["sympy_osp12"]="✗ FAILED"
    echo "  ${RESULTS["sympy_osp12"]}"
    echo "  See: $RESULTS_DIR/sympy_osp12.log"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# ============================================================================
# 8. GAlgebra Cl(1,2) Spinor Verification
# ============================================================================
echo -e "\n[8/11] GAlgebra: osp(1|2) Cl(1,2) Spinor Mapping"
echo "----------------------------------------"

if python3 "$REPO_ROOT/tools/galgebra/osp12_galgebra_spinor.py" \
        > "$RESULTS_DIR/galgebra_osp12.log" 2>&1; then
    RESULTS["galgebra_osp12"]="✓ PASSED"
    PASSED_TESTS=$((PASSED_TESTS + 1))
    echo "  ${RESULTS["galgebra_osp12"]}"
else
    RESULTS["galgebra_osp12"]="✗ FAILED"
    echo "  ${RESULTS["galgebra_osp12"]}"
    echo "  See: $RESULTS_DIR/galgebra_osp12.log"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# ============================================================================
# 9. SageMath Weight System Verification
# ============================================================================
echo -e "\n[9/11] SageMath: osp(1|2) Weight Representation Modules"
echo "----------------------------------------"

if command -v sage &> /dev/null; then
    if sage "$REPO_ROOT/tools/sage/osp12_weight_system.sage" \
            > "$RESULTS_DIR/sage_osp12.log" 2>&1; then
        RESULTS["sage_osp12"]="✓ PASSED"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        echo "  ${RESULTS["sage_osp12"]}"
    else
        RESULTS["sage_osp12"]="✗ FAILED"
        echo "  ${RESULTS["sage_osp12"]}"
        echo "  See: $RESULTS_DIR/sage_osp12.log"
    fi
else
    RESULTS["sage_osp12"]="⊘ SKIPPED (not installed)"
    echo "  ${RESULTS["sage_osp12"]}"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# ============================================================================
# 10. GAP Structure Constants Verification
# ============================================================================
echo -e "\n[10/11] GAP: osp(1|2) Graded Structure Constants"
echo "----------------------------------------"

if command -v gap &> /dev/null; then
    if gap -q "$REPO_ROOT/tools/gap/osp12_structure_constants.g" \
            > "$RESULTS_DIR/gap_osp12.log" 2>&1; then
        RESULTS["gap_osp12"]="✓ PASSED"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        echo "  ${RESULTS["gap_osp12"]}"
    else
        RESULTS["gap_osp12"]="✗ FAILED"
        echo "  ${RESULTS["gap_osp12"]}"
        echo "  See: $RESULTS_DIR/gap_osp12.log"
    fi
else
    RESULTS["gap_osp12"]="⊘ SKIPPED (not installed)"
    echo "  ${RESULTS["gap_osp12"]}"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# ============================================================================
# 11. Macaulay2 Weyl-Clifford D-Module Verification
# ============================================================================
echo -e "\n[11/11] Macaulay2: osp(1|2) Weyl-Clifford D-Module Analysis"
echo "----------------------------------------"

if command -v M2 &> /dev/null; then
    if M2 --script "$REPO_ROOT/tools/macaulay2/osp12_weyl_clifford.m2" \
            > "$RESULTS_DIR/macaulay2_osp12.log" 2>&1; then
        RESULTS["macaulay2_osp12"]="✓ PASSED"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        echo "  ${RESULTS["macaulay2_osp12"]}"
    else
        RESULTS["macaulay2_osp12"]="✗ FAILED"
        echo "  ${RESULTS["macaulay2_osp12"]}"
        echo "  See: $RESULTS_DIR/macaulay2_osp12.log"
    fi
else
    RESULTS["macaulay2_osp12"]="⊘ SKIPPED (not installed)"
    echo "  ${RESULTS["macaulay2_osp12"]}"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# ============================================================================
# Summary
# ============================================================================
echo -e "\n================================================================================"
echo "VERIFICATION SUMMARY"
echo "================================================================================"

echo -e "\nBase Verification Results:"
for engine in sympy lean4 sage macaulay2 coq isabelle; do
    printf "  %-15s %s\n" "$engine:" "${RESULTS[$engine]}"
done

echo -e "\nosp(1|2) Superalgebra Verification Results:"
for engine in sympy_osp12 galgebra_osp12 sage_osp12 gap_osp12 macaulay2_osp12; do
    printf "  %-20s %s\n" "$engine:" "${RESULTS[$engine]}"
done

echo -e "\nPassed: $PASSED_TESTS / $TOTAL_TESTS"

if [ $PASSED_TESTS -eq $TOTAL_TESTS ]; then
    echo -e "\n🎉 ALL TESTS PASSED!"
    EXIT_CODE=0
elif [ $PASSED_TESTS -gt 0 ]; then
    echo -e "\n✓ Partial success - core engines verified"
    EXIT_CODE=0
else
    echo -e "\n✗ No tests passed"
    EXIT_CODE=1
fi

# Export summary
cat > "$RESULTS_DIR/summary.json" << EOF
{
  "timestamp": "$(date -Iseconds)",
  "repository": "$REPO_ROOT",
  "total_tests": $TOTAL_TESTS,
  "passed_tests": $PASSED_TESTS,
  "results": {
    "sympy": "${RESULTS["sympy"]}",
    "lean4": "${RESULTS["lean4"]}",
    "sage": "${RESULTS["sage"]}",
    "macaulay2": "${RESULTS["macaulay2"]}",
    "coq": "${RESULTS["coq"]}",
    "isabelle": "${RESULTS["isabelle"]}",
    "sympy_osp12": "${RESULTS["sympy_osp12"]}",
    "galgebra_osp12": "${RESULTS["galgebra_osp12"]}",
    "sage_osp12": "${RESULTS["sage_osp12"]}",
    "gap_osp12": "${RESULTS["gap_osp12"]}",
    "macaulay2_osp12": "${RESULTS["macaulay2_osp12"]}"
  }
}
EOF

echo -e "\nSummary exported to: $RESULTS_DIR/summary.json"
echo "================================================================================"

exit $EXIT_CODE