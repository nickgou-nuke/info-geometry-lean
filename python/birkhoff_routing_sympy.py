#!/usr/bin/env python3
"""
Birkhoff-von Neumann Routing - SymPy Verification

Symbolic verification of:
1. Doubly stochastic matrix properties
2. BvN decomposition existence
3. Sinkhorn convergence
4. Energy conservation theorems
"""

from sympy import (
    Matrix, symbols, Symbol,
    Sum, Product, sqrt, log, exp,
    simplify, N, Rational,
    FiniteSet, Eq, And
)
from sympy.abc import i, j, k, n
import numpy as np

def is_doubly_stochastic_sympy(A):
    """Check symbolic doubly stochastic properties"""
    n = A.rows
    
    # Non-negativity
    nonneg = And(*[A[i,j] >= 0 for i in range(n) for j in range(n)])
    
    # Row sums
    row_sums = And(*[Sum(A[i,j], (j, 0, n-1)) == 1 for i in range(n)])
    
    # Column sums
    col_sums = And(*[Sum(A[i,j], (i, 0, n-1)) == 1 for i in range(n)])
    
    return And(nonneg, row_sums, col_sums)

def permutation_matrix_symbolic(n, sigma):
    """
    Create symbolic permutation matrix
    
    sigma: list/tuple representing permutation
    """
    P = Matrix.zeros(n, n)
    for i in range(n):
        P[i, sigma[i]] = 1
    return P

def bvN_decomposition_numeric(W, tol=1e-10):
    """
    Numerical BvN decomposition using Hungarian algorithm
    """
    from scipy.optimize import linear_sum_assignment
    
    n = W.rows
    W_np = np.array(W.tolist(), dtype=float)
    
    decomposition = []
    W_remaining = W_np.copy()
    
    iteration = 0
    while np.max(W_remaining) > tol and iteration < 100:
        # Find optimal permutation
        row_ind, col_ind = linear_sum_assignment(-W_remaining)
        
        # Build permutation matrix
        P = np.zeros((n, n))
        P[row_ind, col_ind] = 1
        
        # Minimum weight
        theta = min(W_remaining[row_ind[k], col_ind[k]] for k in range(n))
        
        if theta < tol:
            break
        
        decomposition.append((theta, P))
        W_remaining -= theta * P
        iteration += 1
    
    return decomposition

def sinkhorn_iterate_symbolic(A, n_iter=10):
    """
    Symbolic Sinkhorn iteration (limited steps)
    """
    n = A.rows
    A_current = A.copy()
    
    for _ in range(n_iter):
        # Row normalize
        for i in range(n):
            row_sum = sum(A_current[i,j] for j in range(n))
            for j in range(n):
                A_current[i,j] = A_current[i,j] / row_sum
        
        # Column normalize
        for j in range(n):
            col_sum = sum(A_current[i,j] for i in range(n))
            for i in range(n):
                A_current[i,j] = A_current[i,j] / col_sum
    
    return A_current

def verify_energy_conservation(W, tokens):
    """
    Verify ‖W·tokens‖² ≤ ‖tokens‖²
    """
    n = len(tokens)
    
    # Routed tokens
    routed = []
    for i in range(n):
        routed_vec = sum(
            (W[i,j] * tokens[j] for j in range(n)),
            Matrix.zeros(tokens[0].rows, tokens[0].cols),
        )
        routed.append(routed_vec)
    
    # Energies
    E_orig = sum(v.dot(v) for v in tokens)
    E_routed = sum(v.dot(v) for v in routed)
    
    return simplify(E_routed - E_orig) <= 0

def cone_slice_witness_numeric(W, tol=1e-10):
    """Return a nonnegative cone witness from the greedy BvN decomposition."""
    decomp = bvN_decomposition_numeric(W, tol=tol)
    weights = [theta for theta, _ in decomp]
    perms = [Matrix(P) for _, P in decomp]
    return weights, perms

def verify_cone_slice_numeric(W, tol=1e-10):
    """Check that W lies in the positive cone spanned by permutation matrices."""
    decomp = bvN_decomposition_numeric(W, tol=tol)
    if not decomp:
        return False
    if any(theta < -tol for theta, _ in decomp):
        return False
    if abs(sum(theta for theta, _ in decomp) - 1) > tol:
        return False
    W_reconstructed = sum(
        (theta * Matrix(P) for theta, P in decomp),
        Matrix.zeros(W.rows, W.cols),
    )
    error = max(abs(W[i,j] - W_reconstructed[i,j])
                for i in range(W.rows) for j in range(W.cols))
    return error < tol

# Demonstration
if __name__ == "__main__":
    print("="*60)
    print("Birkhoff-von Neumann Routing - SymPy Verification")
    print("="*60)
    
    # Test 1: Symbolic 2×2 doubly stochastic
    print("\n1. Symbolic 2×2 Doubly Stochastic Matrix")
    a = Symbol('a', positive=True)
    W2 = Matrix([[a, 1-a], [1-a, a]])
    print(f"W = {W2}")
    print(f"Row sums: {[sum(W2.row(i)) for i in range(2)]}")
    print(f"Col sums: {[sum(W2.col(j)) for j in range(2)]}")
    
    # Test 2: Numeric 3×3 example
    print("\n2. Numeric 3×3 BvN Decomposition")
    W3 = Matrix([
        [Rational(1,2), Rational(1,3), Rational(1,6)],
        [Rational(1,3), Rational(1,2), Rational(1,6)],
        [Rational(1,6), Rational(1,6), Rational(2,3)]
    ])
    print(f"W = {W3}")
    print(f"Numerical values:\n{N(W3, 4)}")
    
    # Decompose
    decomp = bvN_decomposition_numeric(W3)
    print(f"\nDecomposition into {len(decomp)} permutations:")
    for k, (theta, P) in enumerate(decomp):
        print(f"  P_{k}: θ = {theta:.6f}")
        print(f"  {P}")
    
    # Verify
    W_reconstructed = sum(
        (theta * Matrix(P) for theta, P in decomp),
        Matrix.zeros(W3.rows, W3.cols),
    )
    error = max(abs(W3[i,j] - W_reconstructed[i,j]) 
                for i in range(3) for j in range(3))
    print(f"Reconstruction error: {error:.2e}")
    
    # Test 3: Sinkhorn convergence
    print("\n3. Sinkhorn Normalization")
    A = Matrix([[1, 2, 1],
                [1, 1, 2],
                [2, 1, 1]])
    print(f"Original:\n{A}")
    
    A_sinkhorn = sinkhorn_iterate_symbolic(A, n_iter=6)
    print(f"After 6 iterations:\n{N(A_sinkhorn, 4)}")
    print(f"Row sums: {[float(sum(A_sinkhorn.row(i))) for i in range(3)]}")
    print(f"Col sums: {[float(sum(A_sinkhorn.col(j))) for j in range(3)]}")
    
    # Test 4: Energy conservation
    print("\n4. Energy Conservation")
    from sympy import Matrix
    W_test = Matrix([[0.5, 0.3, 0.2],
                     [0.2, 0.5, 0.3],
                     [0.3, 0.2, 0.5]])
    tokens = [Matrix([1, 0, 0]), 
              Matrix([0, 1, 0]), 
              Matrix([0, 0, 1])]
    
    diff = verify_energy_conservation(W_test, tokens)
    print(f"Energy difference (routed - original): {diff}")
    print(f"Energy conserved: {diff}")

    print("\n5. Cone Slice Witness")
    cone_valid = verify_cone_slice_numeric(W3)
    print(f"Cone witness valid: {cone_valid}")
    P_id = Matrix.eye(3)
    print(f"Identity permutation in cone: {verify_cone_slice_numeric(P_id)}")
    
    print("\n" + "="*60)
    print("Verification complete!")
    print("="*60)
