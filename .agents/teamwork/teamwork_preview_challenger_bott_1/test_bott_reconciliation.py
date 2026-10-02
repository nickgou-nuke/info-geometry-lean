#!/usr/bin/env python3
"""
Empirical stress-testing harness for BottPeriodicityReconciliation.lean
Verifies:
1. CL(1,1) relations:
   sigma1^2 == I2, epsilon^2 == -I2, sigma1*epsilon + epsilon*sigma1 == 0
2. Basis linear independence & determinant:
   Determinant of flattened basis matrix M (exact integer and floating point)
3. Spanning inversion:
   Exact symbolic and numerical reconstruction for:
   - 10,000 random matrices
   - Extensive corner cases (zero, identity, diagonal, anti-diagonal, nilpotent, rank-1, ill-conditioned, extreme dynamic range)
4. Exact rational arithmetic verification (zero floating point drift)
"""

import numpy as np
from fractions import Fraction
import itertools

def exact_det_4x4(M):
    """Compute exact determinant of a 4x4 nested list of numbers/Fractions using Leibniz formula."""
    det = Fraction(0, 1)
    for perm in itertools.permutations(range(4)):
        term = Fraction(1, 1)
        inversions = 0
        for i in range(4):
            for j in range(i + 1, 4):
                if perm[i] > perm[j]:
                    inversions += 1
            term *= Fraction(M[i][perm[i]])
        sign = -1 if (inversions % 2 == 1) else 1
        det += sign * term
    return det

def test_cl11_relations():
    print("=== TASK 1: CL(1,1) Matrix Relations ===")
    sigma1 = np.array([[0, 1], [1, 0]], dtype=np.int64)
    epsilon = np.array([[0, 1], [-1, 0]], dtype=np.int64)
    I2 = np.array([[1, 0], [0, 1]], dtype=np.int64)
    sigma3 = np.array([[1, 0], [0, -1]], dtype=np.int64)
    zero2 = np.zeros((2, 2), dtype=np.int64)

    # 1. sigma1 * sigma1 == I2
    s1_sq = sigma1 @ sigma1
    assert np.array_equal(s1_sq, I2), f"sigma1^2 != I2:\n{s1_sq}"
    print("[PASS] sigma1 * sigma1 == I2")

    # 2. epsilon * epsilon == -I2
    eps_sq = epsilon @ epsilon
    assert np.array_equal(eps_sq, -I2), f"epsilon^2 != -I2:\n{eps_sq}"
    print("[PASS] epsilon * epsilon == -I2")

    # 3. sigma1 * epsilon + epsilon * sigma1 == 0
    anticomm = sigma1 @ epsilon + epsilon @ sigma1
    assert np.array_equal(anticomm, zero2), f"Anticommutator != 0:\n{anticomm}"
    print("[PASS] sigma1 * epsilon + epsilon * sigma1 == 0")

    # Check products with sigma3
    assert np.array_equal(sigma1 @ epsilon, -sigma3), "sigma1 * epsilon != -sigma3"
    assert np.array_equal(epsilon @ sigma1, sigma3), "epsilon * sigma1 != sigma3"
    assert np.array_equal(sigma3 @ sigma3, I2), "sigma3^2 != I2"
    print("[PASS] Clifford algebra product relations verified.")

def test_basis_and_determinant():
    print("\n=== TASK 2: Basis and Linear Independence ===")
    # Flattening row-major:
    I2_vec = [1, 0, 0, 1]
    sigma1_vec = [0, 1, 1, 0]
    epsilon_vec = [0, 1, -1, 0]
    sigma3_vec = [1, 0, 0, -1]

    # Change-of-basis matrix with basis vectors as columns:
    M_col = [
        [1, 0,  0,  1],
        [0, 1,  1,  0],
        [0, 1, -1,  0],
        [1, 0,  0, -1]
    ]

    det_col_exact = exact_det_4x4(M_col)
    print(f"Exact determinant (column basis): {det_col_exact}")
    assert det_col_exact == Fraction(4, 1), f"Expected det=4, got {det_col_exact}"

    # Change-of-basis matrix with basis vectors as rows:
    M_row = [I2_vec, sigma1_vec, epsilon_vec, sigma3_vec]
    det_row_exact = exact_det_4x4(M_row)
    print(f"Exact determinant (row basis): {det_row_exact}")
    assert det_row_exact == Fraction(4, 1), f"Expected det=4, got {det_row_exact}"

    # NumPy floating point check:
    M_col_np = np.array(M_col, dtype=np.float64)
    det_col_np = np.linalg.det(M_col_np)
    print(f"NumPy floating-point determinant: {det_col_np:.6f}")
    assert abs(det_col_np - 4.0) < 1e-12

    # Rank check
    rank = np.linalg.matrix_rank(M_col_np)
    print(f"Matrix rank: {rank} (out of 4)")
    assert rank == 4, f"Expected rank 4, got {rank}"

    print("[PASS] Basis is linearly independent with det = 4 != 0 and rank = 4.")

def reconstruct_matrix(A):
    # a = (A00 + A11)/2
    # b = (A01 + A10)/2
    # c = (A01 - A10)/2
    # d = (A00 - A11)/2
    a = (A[0, 0] + A[1, 1]) / 2.0
    b = (A[0, 1] + A[1, 0]) / 2.0
    c = (A[0, 1] - A[1, 0]) / 2.0
    d = (A[0, 0] - A[1, 1]) / 2.0

    I2 = np.array([[1.0, 0.0], [0.0, 1.0]])
    sigma1 = np.array([[0.0, 1.0], [1.0, 0.0]])
    epsilon = np.array([[0.0, 1.0], [-1.0, 0.0]])
    sigma3 = np.array([[1.0, 0.0], [0.0, -1.0]])

    A_recon = a * I2 + b * sigma1 + c * epsilon + d * sigma3
    return A_recon, (a, b, c, d)

def test_spanning_inversion():
    print("\n=== TASK 3: Spanning Inversion & Numerical Stress Testing ===")

    # 1. Corner cases
    corner_cases = {
        "Zero Matrix": np.zeros((2, 2)),
        "Identity Matrix": np.eye(2),
        "Negative Identity": -np.eye(2),
        "Diagonal Matrix 1": np.array([[5.0, 0.0], [0.0, -3.0]]),
        "Diagonal Extreme Ratio": np.array([[1e8, 0.0], [0.0, 1e-8]]),
        "Anti-diagonal 1": np.array([[0.0, 7.0], [-4.0, 0.0]]),
        "Anti-diagonal Symmetric": np.array([[0.0, 3.5], [3.5, 0.0]]),
        "Anti-diagonal Skew": np.array([[0.0, 2.5], [-2.5, 0.0]]),
        "Nilpotent Upper": np.array([[0.0, 1.0], [0.0, 0.0]]),
        "Nilpotent Lower": np.array([[0.0, 0.0], [1.0, 0.0]]),
        "Nilpotent Trace-Free Rank-1": np.array([[1.0, 1.0], [-1.0, -1.0]]),
        "Rank-1 Symmetric": np.array([[1.0, 2.0], [2.0, 4.0]]),
        "Rank-1 General": np.array([[3.0, 6.0], [1.5, 3.0]]),
        "Ill-conditioned near singular": np.array([[1.0, 1.0], [1.0, 1.0 + 1e-12]]),
        "Ill-conditioned very near singular": np.array([[1.0, 1.0], [1.0, 1.0 + 1e-14]]),
        "Large Magnitude (1e12)": np.array([[1e12, -2e12], [3e12, -4e12]]),
        "Tiny Magnitude (1e-15)": np.array([[1e-15, 2e-15], [-3e-15, 4e-15]]),
        "Mixed High Dynamic Range": np.array([[1e14, 1e-14], [1.0, 0.0]])
    }

    max_err_corner = 0.0
    for name, A in corner_cases.items():
        A_recon, coeffs = reconstruct_matrix(A)
        err = np.max(np.abs(A - A_recon))
        # Relative error where scale > 0
        scale = max(1.0, float(np.max(np.abs(A))))
        rel_err = err / scale
        if scale <= 10.0:
            assert err < 1e-15, f"Corner case {name} failed: absolute error {err} >= 1e-15"
        else:
            assert rel_err < 1e-15, f"Corner case {name} failed: relative error {rel_err} >= 1e-15"
        max_err_corner = max(max_err_corner, rel_err)
        print(f"  [PASS] Corner case: {name:35s} | abs_err={err:.2e}, rel_err={rel_err:.2e}")

    print(f"All corner cases passed. Max relative error: {max_err_corner:.2e}")

    # 2. Random matrices test: 10,000 random matrices
    np.random.seed(42)
    n_random = 10000
    print(f"\nTesting {n_random} random 2x2 matrices (normal distribution N(0, 1))...")
    random_matrices = np.random.randn(n_random, 2, 2)
    max_err_rand = 0.0
    for i in range(n_random):
        A = random_matrices[i]
        A_recon, coeffs = reconstruct_matrix(A)
        err = np.max(np.abs(A - A_recon))
        assert err < 1e-15, f"Random matrix {i} failed: abs_err={err}"
        if err > max_err_rand:
            max_err_rand = err

    print(f"[PASS] {n_random} random matrices verified. Max absolute error: {max_err_rand:.2e} < 1e-15")

    # 3. Uniform random matrices in [-1000, 1000]
    print(f"Testing 5,000 uniform random matrices in [-1000, 1000]...")
    uniform_matrices = np.random.uniform(-1000.0, 1000.0, (5000, 2, 2))
    max_err_uniform = 0.0
    for i in range(5000):
        A = uniform_matrices[i]
        A_recon, _ = reconstruct_matrix(A)
        err = np.max(np.abs(A - A_recon))
        scale = np.max(np.abs(A))
        rel_err = err / scale
        assert rel_err < 1e-15, f"Uniform matrix {i} failed: rel_err={rel_err}"
        if rel_err > max_err_uniform:
            max_err_uniform = rel_err
    print(f"[PASS] 5,000 uniform matrices verified. Max relative error: {max_err_uniform:.2e} < 1e-15")

def test_exact_rational_field():
    print("\n=== Exact Rational Arithmetic Inversion ===")
    for num in range(500):
        # generate rational entries
        n1, d1 = (num * 3 - 50), (num % 7 + 1)
        n2, d2 = (num * 7 - 12), (num % 5 + 1)
        n3, d3 = (num * 2 + 19), (num % 9 + 1)
        n4, d4 = (num * 5 - 33), (num % 11 + 1)
        A00 = Fraction(n1, d1)
        A01 = Fraction(n2, d2)
        A10 = Fraction(n3, d3)
        A11 = Fraction(n4, d4)

        a = (A00 + A11) / 2
        b = (A01 + A10) / 2
        c = (A01 - A10) / 2
        d = (A00 - A11) / 2

        # Recon:
        # A_recon_00 = a + d
        # A_recon_01 = b + c
        # A_recon_10 = b - c
        # A_recon_11 = a - d
        assert (a + d) == A00, f"Rational mismatch 00: {a+d} != {A00}"
        assert (b + c) == A01, f"Rational mismatch 01: {b+c} != {A01}"
        assert (b - c) == A10, f"Rational mismatch 10: {b-c} != {A10}"
        assert (a - d) == A11, f"Rational mismatch 11: {a-d} != {A11}"

    print("[PASS] 500 exact rational matrices verified with 0 error.")

if __name__ == "__main__":
    test_cl11_relations()
    test_basis_and_determinant()
    test_spanning_inversion()
    test_exact_rational_field()
    print("\n=======================================================")
    print("ALL EMPIRICAL AND SYMBOLIC TESTS PASSED WITH 100% SUCCESS")
    print("=======================================================")
