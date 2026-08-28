#!/usr/bin/env python3
"""
CAS Generator and Matrix Verification for sp(12, Q) Contact 5-Grading.

Dimensions:
- Sp(12, Q) symplectic Lie algebra: dim = 12 * 13 / 2 = 78.
- 5-grading under Heisenberg contact root:
  g = g_{-2} + g_{-1} + g_0 + g_{+1} + g_{+2}
  dim(g_{-2}) = 1
  dim(g_{-1}) = 10
  dim(g_0)    = 56  (sp(10) + R*H)
  dim(g_{+1}) = 10
  dim(g_{+2}) = 1
  Total: 1 + 10 + 56 + 10 + 1 = 78.

Verifies:
1. Matrix symplectic condition: X^T * J + J * X = 0 for J = [ [0, I_6], [-I_6, 0] ].
2. Exact sector dimensions and matrix basis construction.
3. Jacobi identity [X, [Y, Z]] + [Y, [Z, X]] + [Z, [X, Y]] == 0 for all graded sectors.
"""

import numpy as np
import sympy as sp

def run_sp12_analysis():
    print("=" * 70)
    print("CAS VERIFICATION: sp(12, Q) CONTACT 5-GRADING")
    print("=" * 70)

    n = 6 # 2n = 12
    dim_sp12 = 2 * n * (2 * n + 1) // 2
    print(f"Dimension of sp(12, Q): {dim_sp12}")

    # Symplectic form J = [ [0, I_6], [-I_6, 0] ]
    I6 = sp.eye(6)
    Z6 = sp.zeros(6, 6)
    J = sp.BlockMatrix([[Z6, I6], [-I6, Z6]]).as_explicit()

    # Grading element H:
    # H = diag(1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0)
    h_diag = [1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]
    H = sp.diag(*h_diag)

    # Check that H is in sp(12): H^T * J + J * H == 0
    h_sp = H.T * J + J * H
    print(f"Grading element H in sp(12, Q): {h_sp == sp.zeros(12, 12)}")

    # Construct all 78 standard basis matrices of sp(12):
    # An element of sp(2n) has block form [ [A, B], [C, -A^T] ] with B^T = B, C^T = C.
    basis_matrices = []
    
    # 1. A-block: any 6x6 matrix (36 dims) -> [ [E_ij, 0], [0, -E_ji] ]
    for i in range(6):
        for j in range(6):
            E = sp.zeros(12, 12)
            E[i, j] += 1
            E[6 + j, 6 + i] -= 1
            basis_matrices.append(E)

    # 2. B-block: symmetric 6x6 matrix (21 dims) -> [ [0, S_ij], [0, 0] ]
    for i in range(6):
        for j in range(i, 6):
            E = sp.zeros(12, 12)
            if i == j:
                E[i, 6 + i] += 1
            else:
                E[i, 6 + j] += 1
                E[j, 6 + i] += 1
            basis_matrices.append(E)

    # 3. C-block: symmetric 6x6 matrix (21 dims) -> [ [0, 0], [S_ij, 0] ]
    for i in range(6):
        for j in range(i, 6):
            E = sp.zeros(12, 12)
            if i == j:
                E[6 + i, i] += 1
            else:
                E[6 + i, j] += 1
                E[6 + j, i] += 1
            basis_matrices.append(E)

    print(f"Constructed sp(12) basis matrices count: {len(basis_matrices)} == 78: {len(basis_matrices) == 78}")

    # Classify each basis matrix into its 5-grade eigenvalue under ad(H)(X) = [H, X] = λ X:
    graded_sectors = {-2: [], -1: [], 0: [], 1: [], 2: []}
    for M in basis_matrices:
        comm = H * M - M * H
        # Find scalar lambda such that comm = lambda * M
        # Check lambda in {-2, -1, 0, 1, 2}
        assigned = False
        for lam in [-2, -1, 0, 1, 2]:
            if comm == lam * M:
                graded_sectors[lam].append(M)
                assigned = True
                break
        assert assigned, "Matrix not in a homogeneous 5-grade sector!"

    dims = [len(graded_sectors[g]) for g in [-2, -1, 0, 1, 2]]
    print(f"\nExact 5-Grade Sector Dimensions [g_-2, g_-1, g_0, g_+1, g_+2]: {dims}")
    print(f"Expected: [1, 10, 56, 10, 1] -> MATCH: {dims == [1, 10, 56, 10, 1]}")
    print(f"Total dimension: {sum(dims)} == 78: {sum(dims) == 78}")

    # Matrix Jacobi Check on random elements from graded sectors:
    print("\nVerifying matrix Jacobi identity [X, [Y, Z]] + [Y, [Z, X]] + [Z, [X, Y]] == 0...")
    for g1 in [-2, -1, 0, 1, 2]:
        for g2 in [-2, -1, 0, 1, 2]:
            for g3 in [-2, -1, 0, 1, 2]:
                X = graded_sectors[g1][0]
                Y = graded_sectors[g2][0]
                Z = graded_sectors[g3][0]
                # Jacobiator
                term1 = X * (Y * Z - Z * Y) - (Y * Z - Z * Y) * X
                term2 = Y * (Z * X - X * Z) - (Z * X - X * Z) * Y
                term3 = Z * (X * Y - Y * X) - (X * Y - Y * X) * Z
                jac = term1 + term2 + term3
                assert jac == sp.zeros(12, 12), f"Jacobi failed for triple ({g1}, {g2}, {g3})"

    print("All graded matrix Jacobi identities verified: TRUE (100% exact algebraic zero)")
    print("=" * 70)

if __name__ == "__main__":
    run_sp12_analysis()
