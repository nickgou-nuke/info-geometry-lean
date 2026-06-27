#!/bin/bash
# Verify Clifford algebra constructions across multiple engines
# Usage: ./verify_clifford_multi_engine.sh

set -e

echo "===================================================================="
echo "Multi-Engine Clifford Algebra Verification"
echo "===================================================================="
echo ""

# SymPy verification (Euclidean signature Cl(d,0))
echo "[1/3] SymPy: Weyl-Brauer construction for Cl(d,0)"
echo "--------------------------------------------------------------------"
python3 tools/clifford/verify_gamma_matrices.py
echo ""

# SageMath verification (abstract, both signatures)
echo "[2/3] SageMath: Abstract Clifford algebra"
echo "--------------------------------------------------------------------"
if command -v sage &> /dev/null; then
    sage -python tools/clifford/gamma_sage.py
else
    echo "sage not found, skipping..."
fi
echo ""

# GAP verification (group structure)
echo "[3/3] GAP: Gamma group structure"
echo "--------------------------------------------------------------------"
if command -v gap &> /dev/null; then
    gap -b tools/clifford/gamma_group.gap
else
    echo "gap not found, skipping..."
fi
echo ""

echo "===================================================================="
echo "Verification Complete"
echo "===================================================================="
echo ""
echo "Note: These tools verify Euclidean signature Cl(d,0)."
echo "The repo's canonical implementation uses split signature Cl(n,n) in:"
echo "  - InfoGeometry.Clifford.ClNN"
echo "  - InfoGeometry.Clifford.Cl11CoordinateAlgebra"
echo "  - InfoGeometry.Clifford.Cl11InfiniteCarrier"