#!/bin/bash
# Master Verification Script for Pellis Fine-Structure Constant
# Runs all formalizations across 9 computational engines

set -e  # Exit on first error

echo "========================================================================"
echo "PELLIS FINE-STRUCTURE CONSTANT - MULTI-SYSTEM VERIFICATION"
echo "========================================================================"
echo ""
echo "Running formalizations across all computational engines..."
echo ""

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FAILED=0
PASSED=0

# 1. Lean4 build
echo "[1/8] Lean4 formalization..."
if ~/.elan/bin/lake build InfoGeometry.Physics.PellisFineStructure 2>&1 | grep -q "completed"; then
    echo "  ✓ Lean4: PASSED"
    ((PASSED++))
else
    echo "  ✗ Lean4: FAILED"
    ((FAILED++))
fi

# 2. SageMath
echo "[2/8] SageMath verification..."
if command -v sage &> /dev/null; then
    if sage "$SCRIPT_DIR/sage/pellis_fine_structure.sage" 2>&1 | grep -q "ALL VERIFICATIONS PASSED"; then
        echo "  ✓ SageMath: PASSED"
        ((PASSED++))
    else
        echo "  ✗ SageMath: FAILED"
        ((FAILED++))
    fi
else
    echo "  ⊘ SageMath: SKIPPED (not installed)"
fi

# 3. SymPy/Python
echo "[3/8] SymPy verification..."
if command -v python3 &> /dev/null; then
    if python3 "$SCRIPT_DIR/python/verify_pellis.py" 2>&1 | grep -q "ALL SYMPY VERIFICATIONS PASSED"; then
        echo "  ✓ SymPy: PASSED"
        ((PASSED++))
    else
        echo "  ✗ SymPy: FAILED"
        ((FAILED++))
    fi
else
    echo "  ⊘ Python3: SKIPPED"
fi

# 4. GAP
echo "[4/8] GAP verification..."
if command -v gap &> /dev/null; then
    if gap -q "$SCRIPT_DIR/gap/pellis.gap" 2>&1 | grep -q "ALL GAP VERIFICATIONS PASSED"; then
        echo "  ✓ GAP: PASSED"
        ((PASSED++))
    else
        echo "  ✗ GAP: FAILED"
        ((FAILED++))
    fi
else
    echo "  ⊘ GAP: SKIPPED (not installed)"
fi

# 5. Macaulay2
echo "[5/8] Macaulay2 verification..."
if command -v M2 &> /dev/null; then
    if M2 < "$SCRIPT_DIR/macaulay2/pellis.m2" 2>&1 | grep -q "Normal form"; then
        echo "  ✓ Macaulay2: PASSED"
        ((PASSED++))
    else
        echo "  ✗ Macaulay2: FAILED"
        ((FAILED++))
    fi
else
    echo "  ⊘ Macaulay2: SKIPPED (not installed)"
fi

# 6. Singular
echo "[6/8] Singular verification..."
if command -v Singular &> /dev/null; then
    if Singular "$SCRIPT_DIR/singular/pellis.sing" 2>&1 | grep -q "COMPLETE"; then
        echo "  ✓ Singular: PASSED"
        ((PASSED++))
    else
        echo "  ✗ Singular: FAILED"
        ((FAILED++))
    fi
else
    echo "  ⊘ Singular: SKIPPED (not installed)"
fi

# 7. Clifford/GAlgebra
echo "[7/8] Clifford/GAlgebra verification..."
if command -v python3 &> /dev/null && python3 -c "import galgebra" 2>/dev/null; then
    if python3 "$SCRIPT_DIR/clifford/pellis.py" 2>&1 | grep -q "COMPLETE"; then
        echo "  ✓ Clifford: PASSED"
        ((PASSED++))
    else
        echo "  ✗ Clifford: FAILED"
        ((FAILED++))
    fi
else
    echo "  ⊘ Clifford: SKIPPED (galgebra not installed)"
fi

# 8. Isabelle (commented - requires setup)
echo "[8/8] Isabelle/HOL formalization..."
echo "  ⊘ Isabelle: SKIPPED (requires manual build withAFP)"
echo "     To verify: isabelle build -d isabelle/InfoGeometry/Canonical PellisFineStructure"

echo ""
echo "========================================================================"
echo "VERIFICATION SUMMARY"
echo "========================================================================"
echo "Passed: $PASSED"
echo "Failed: $FAILED"
echo ""

if [ $FAILED -eq 0 ]; then
    echo "✓ All available formalizations PASSED"
    exit 0
else
    echo "✗ Some formalizations FAILED"
    exit 1
fi