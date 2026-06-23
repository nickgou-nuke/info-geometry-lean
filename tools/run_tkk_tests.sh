#!/bin/bash
# Master Test Suite for the Cl(5,5) TKK Closure and Boundary Defect Cancellation

set -e

echo "=========================================================="
echo "    Running TKK Closure & Boundary Verification Suite"
echo "=========================================================="
echo ""

echo ">>> 1. Verifying Lean 4 Formalization (SplitCliffordO55TKKClosure.lean)"
lake env lean /home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SplitCliffordO55TKKClosure.lean
echo "  [OK] Lean 4 structural proofs successfully kernel-checked."
echo ""

echo ">>> 2. Verifying GAP Root Systems & Weyl Group (o55_tkk.g, weyl_klein.g)"
gap -q /home/goutev/.gemini/antigravity-cli/brain/958b6d2f-df75-46a3-89f9-523aa320b53a/scratch/o55_tkk.g < /dev/null
gap -q /home/goutev/.gemini/antigravity-cli/brain/958b6d2f-df75-46a3-89f9-523aa320b53a/scratch/weyl_klein.g < /dev/null
echo "  [OK] GAP D_5 dimension and Weyl order 1920 verified."
echo ""

echo ">>> 3. Verifying Macaulay2 D-Modules (o55_dmodules.m2, weyl_klein.m2)"
M2 --script /home/goutev/.gemini/antigravity-cli/brain/958b6d2f-df75-46a3-89f9-523aa320b53a/scratch/o55_dmodules.m2
M2 --script /home/goutev/.gemini/antigravity-cli/brain/958b6d2f-df75-46a3-89f9-523aa320b53a/scratch/weyl_klein.m2
echo "  [OK] Macaulay2 D-module holonomic ranks and nilpotent constraints verified."
echo ""

echo ">>> 4. Verifying Python/SymPy Algebraic Commutators (sympy_algebra.py, weyl_klein_sympy.py)"
python3 /home/goutev/.gemini/antigravity-cli/brain/958b6d2f-df75-46a3-89f9-523aa320b53a/scratch/sympy_algebra.py > /dev/null
python3 /home/goutev/.gemini/antigravity-cli/brain/958b6d2f-df75-46a3-89f9-523aa320b53a/scratch/weyl_klein_sympy.py
echo "  [OK] SymPy exact commutator bracket evaluation and Cuntz boundaries verified."
echo ""

echo ">>> 5. Verifying Python/Clifford Geometric Algebra (o55_tkk.py, weyl_klein_clifford.py, pin55_witness.py)"
python3 /home/goutev/.gemini/antigravity-cli/brain/958b6d2f-df75-46a3-89f9-523aa320b53a/scratch/o55_tkk.py
python3 /home/goutev/.gemini/antigravity-cli/brain/958b6d2f-df75-46a3-89f9-523aa320b53a/scratch/weyl_klein_clifford.py
python3 /home/goutev/.gemini/antigravity-cli/brain/958b6d2f-df75-46a3-89f9-523aa320b53a/scratch/pin55_witness.py
echo "  [OK] Clifford algebra Pin(5,5) involutions, parity cancellation, and chiral nilpotency verified."
echo ""

echo "=========================================================="
echo "    ALL TKK CLOSURE AND ANOMALY TESTS PASSED SUCCESSFULLY"
echo "=========================================================="
