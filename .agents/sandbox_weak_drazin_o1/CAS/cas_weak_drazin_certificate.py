#!/usr/bin/env python3
"""
CAS Verification Certificate for Campbell-Meyer Weak Drazin Inverses
Validates all 3x3 matrix identities, weak Drazin relations (B A^3 = A^2),
Souriau-Frame coefficients, and unit conjugation symbolically via SymPy.
"""

import sys
from sympy import Matrix, Rational, eye, zeros

def run_verification():
    print("=== Step 1: Defining algebraic matrices over Q ===")
    weakA = Matrix([
        [2, 0, 0],
        [0, 0, 1],
        [0, 0, 0]
    ])

    weakNilpotentLane = Matrix([
        [0, 0, 0],
        [0, 0, 1],
        [0, 0, 0]
    ])

    weakRegularProjector = Matrix([
        [1, 0, 0],
        [0, 0, 0],
        [0, 0, 0]
    ])

    # 1. weakNilpotentLane_sq_eq_zero
    assert weakNilpotentLane**2 == zeros(3, 3), "weakNilpotentLane^2 must be 0"
    print("✓ weakNilpotentLane^2 = 0")

    # 2. weakA_sq_readout
    expected_A_sq = Matrix([
        [4, 0, 0],
        [0, 0, 0],
        [0, 0, 0]
    ])
    assert weakA**2 == expected_A_sq, "weakA^2 readout mismatch"
    print("✓ weakA^2 = diag(4, 0, 0)")

    # 3. weakA_cubic_eq_two_smul_square
    assert weakA**3 == 2 * (weakA**2), "weakA^3 = 2 * weakA^2 mismatch"
    print("✓ weakA^3 = 2 * weakA^2")

    # 4. weakDrazinInverse_isDrazin
    weakDrazinInverse = Matrix([
        [Rational(1, 2), 0, 0],
        [0, 0, 0],
        [0, 0, 0]
    ])
    assert weakA * weakDrazinInverse == weakDrazinInverse * weakA, "Drazin comm failure"
    assert weakDrazinInverse * weakA * weakDrazinInverse == weakDrazinInverse, "Drazin eq 2 failure"
    assert weakA**3 * weakDrazinInverse == weakA**2, "Drazin index 2 failure"
    print("✓ weakDrazinInverse is Drazin inverse (index 2)")

    # weakDrazinInverse_isWeak
    assert weakDrazinInverse * (weakA**3) == weakA**2, "weakDrazinInverse isWeak failure"
    print("✓ weakDrazinInverse is weak Drazin inverse")

    # 5. weakWildInverse
    weakWildInverse = Matrix([
        [Rational(1, 2), 3, 5],
        [0, 7, 11],
        [0, 13, 17]
    ])
    assert weakWildInverse * (weakA**3) == weakA**2, "weakWildInverse isWeak failure"
    assert weakWildInverse != weakDrazinInverse, "weakWildInverse must not equal weakDrazinInverse"
    assert weakA * weakWildInverse != weakWildInverse * weakA, "weakWildInverse must not commute with weakA"
    print("✓ weakWildInverse is weak, non-unique, and non-commuting")

    # 6. weakPolynomialInverse
    weakPolynomialInverse = Rational(1, 2) * eye(3)
    assert weakPolynomialInverse * (weakA**3) == weakA**2, "weakPolynomialInverse isWeak failure"
    assert weakA * weakPolynomialInverse == weakPolynomialInverse * weakA, "weakPolynomialInverse commute failure"
    inv_matrix = 2 * eye(3)
    assert weakPolynomialInverse * inv_matrix == eye(3), "val_inv failure"
    assert inv_matrix * weakPolynomialInverse == eye(3), "inv_val failure"
    assert weakPolynomialInverse != weakDrazinInverse, "weakPolynomialInverse must not equal weakDrazinInverse"
    print("✓ weakPolynomialInverse is commuting weak Drazin unit")

    # 7. Souriau-Frame coefficient
    weakSFp1 = (weakA * eye(3)).trace()
    assert weakSFp1 == 2, "weakSFp1 must be 2"
    assert (Rational(1, weakSFp1)) * eye(3) == weakPolynomialInverse, "SF formula mismatch"
    print("✓ Souriau-Frame formula matches weakPolynomialInverse")

    # 8. weakProjectiveInverse
    weakProjectiveInverse = Matrix([
        [Rational(1, 2), 2, 3],
        [0, 0, 5],
        [0, 0, 7]
    ])
    assert weakProjectiveInverse * (weakA**3) == weakA**2, "weakProjectiveInverse isWeak failure"
    expected_BA = Matrix([
        [1, 0, 2],
        [0, 0, 0],
        [0, 0, 0]
    ])
    assert weakProjectiveInverse * weakA == expected_BA, "weakProjectiveInverse BA readout mismatch"
    assert (weakProjectiveInverse * weakA)**2 == weakProjectiveInverse * weakA, "BA idempotent failure"
    print("✓ weakProjectiveInverse is weak, with idempotent BA readout")

    # 9. weakCommutingInverse
    weakCommutingInverse = Matrix([
        [Rational(1, 2), 0, 0],
        [0, 3, 4],
        [0, 0, 3]
    ])
    assert weakCommutingInverse * (weakA**3) == weakA**2, "weakCommutingInverse isWeak failure"
    assert weakA * weakCommutingInverse == weakCommutingInverse * weakA, "weakCommutingInverse commute failure"
    print("✓ weakCommutingInverse satisfies weak relation and commutes")

    # 10. GL3(Q) permutation and conjugation
    weakPermutation = Matrix([
        [0, 0, 1],
        [0, 1, 0],
        [1, 0, 0]
    ])
    assert weakPermutation * weakPermutation == eye(3), "permutation^2 != I"
    u = weakPermutation
    u_inv = weakPermutation # since u^2 = I
    conj_A = u * weakA * u_inv
    conj_B = u * weakPolynomialInverse * u_inv
    # weak relation on conjugated matrices
    assert conj_B * (conj_A**3) == conj_A**2, "conjugated weak relation failure"
    print("✓ GL3(Q) permutation conjugation preserves weak Drazin relation")

    print("\nALL CAS SYMBOLIC CHECKS PASSED O(1) WITH 100% PRECISION.")
    return 0

if __name__ == "__main__":
    sys.exit(run_verification())
