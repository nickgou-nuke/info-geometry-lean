#!/usr/bin/env bash
# -*- coding: utf-8 -*-
#
# Master Test Runner: Attention = Quantum Fluid Simplified Verification
#
# This script runs the verification suite for the simplified attention quantum fluid theorem.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
RESULTS_DIR="/tmp/attention_results"

mkdir -p "$RESULTS_DIR"

export PATH="/home/goutev/.opam/coq-switch/bin:/home/goutev/Isabelle2025-2/bin:$PATH"

echo "================================================================================"
echo "Attention = Quantum Fluid Simplified Verification"
echo "Repository: $REPO_ROOT"
echo "Results: $RESULTS_DIR"
echo "================================================================================"

declare -A RESULTS
TOTAL_TESTS=0
PASSED_TESTS=0

# 1. SymPy
echo -e "\n[1/8] SymPy: Log-Sum-Exp & Softmax Derivatives"
echo "----------------------------------------"
if python3 "$REPO_ROOT/tools/infra/attention_sympy.py" > "$RESULTS_DIR/sympy.log" 2>&1; then
    RESULTS["sympy"]="✓ PASSED"
    PASSED_TESTS=$((PASSED_TESTS + 1))
    echo "  ${RESULTS["sympy"]}"
else
    RESULTS["sympy"]="✗ FAILED"
    echo "  ${RESULTS["sympy"]}"
    echo "  See: $RESULTS_DIR/sympy.log"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# 2. Lean 4
echo -e "\n[2/8] Lean 4: LogSumExpAttention Compilation"
echo "----------------------------------------"
cd "$REPO_ROOT"
if ~/.elan/bin/lake env lean lean/InfoGeometry/Attention/LogSumExpAttention.lean > "$RESULTS_DIR/lean4.log" 2>&1; then
    RESULTS["lean4"]="✓ PASSED"
    PASSED_TESTS=$((PASSED_TESTS + 1))
    echo "  ${RESULTS["lean4"]}"
else
    RESULTS["lean4"]="✗ FAILED"
    echo "  ${RESULTS["lean4"]}"
    echo "  See: $RESULTS_DIR/lean4.log"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# 3. SageMath
echo -e "\n[3/8] SageMath: Legendre Duality"
echo "----------------------------------------"
if command -v sage &> /dev/null; then
    if sage "$REPO_ROOT/tools/infra/attention_sage.sage" > "$RESULTS_DIR/sage.log" 2>&1; then
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

# 4. GAP
echo -e "\n[4/8] GAP: Skew-Symmetric (Bivector) Trace"
echo "----------------------------------------"
if command -v gap &> /dev/null; then
    if gap -q "$REPO_ROOT/tools/infra/attention_gap.g" > "$RESULTS_DIR/gap.log" 2>&1; then
        RESULTS["gap"]="✓ PASSED"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        echo "  ${RESULTS["gap"]}"
    else
        RESULTS["gap"]="✗ FAILED"
        echo "  ${RESULTS["gap"]}"
        echo "  See: $RESULTS_DIR/gap.log"
    fi
else
    RESULTS["gap"]="⊘ SKIPPED (not installed)"
    echo "  ${RESULTS["gap"]}"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# 5. GAlgebra
echo -e "\n[5/8] GAlgebra: Clifford Reversal (Skew-Adjointness)"
echo "----------------------------------------"
if python3 "$REPO_ROOT/tools/infra/galgebra_clifford_attention.py" > "$RESULTS_DIR/galgebra.log" 2>&1; then
    RESULTS["galgebra"]="✓ PASSED"
    PASSED_TESTS=$((PASSED_TESTS + 1))
    echo "  ${RESULTS["galgebra"]}"
else
    RESULTS["galgebra"]="✗ FAILED"
    echo "  ${RESULTS["galgebra"]}"
    echo "  See: $RESULTS_DIR/galgebra.log"
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))

# 6. Macaulay2
echo -e "\n[6/8] Macaulay2: Weyl Algebra & trace(K) = 0"
echo "----------------------------------------"
if command -v M2 &> /dev/null; then
    if M2 --script "$REPO_ROOT/tools/infra/bridge_data/attention_m2.m2" > "$RESULTS_DIR/macaulay2.log" 2>&1; then
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

# 7. Coq
echo -e "\n[7/8] Coq: Type-Theoretic Attention Flow"
echo "----------------------------------------"
if command -v coqc &> /dev/null; then
    if coqc "$REPO_ROOT/tools/infra/bridge_data/AttentionQuantumFluid.v" > "$RESULTS_DIR/coq.log" 2>&1; then
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

# 8. Isabelle/HOL
echo -e "\n[8/8] Isabelle/HOL: Unified Flow Theory"
echo "----------------------------------------"
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

# Summary
echo -e "\n================================================================================"
echo "ATTENTION = QUANTUM FLUID VERIFICATION SUMMARY"
echo "================================================================================"
for engine in sympy lean4 sage gap galgebra macaulay2 coq isabelle; do
    printf "  %-15s %s\n" "$engine:" "${RESULTS[$engine]}"
done
echo -e "\nPassed: $PASSED_TESTS / $TOTAL_TESTS"

if [ $PASSED_TESTS -eq $TOTAL_TESTS ]; then
    echo -e "\n🎉 ALL 8 SYSTEMS VERIFIED SUCCESSFULLY!"
    exit 0
else
    echo -e "\n✗ Some verification steps failed."
    exit 1
fi
