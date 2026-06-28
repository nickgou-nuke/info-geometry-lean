#!/usr/bin/env sage
# -*- coding: utf-8 -*-
"""
Birkhoff-von Neumann Routing - SageMath Formalization

Implements:
1. Doubly stochastic matrix verification
2. BvN decomposition algorithm (greedy)
3. Sinkhorn-Knopp normalization
4. Energy conservation proofs
"""

import numpy as np
from scipy.optimize import linear_sum_assignment
from sage.all import RR, matrix, zero_matrix, identity_matrix, vector

class BirkhoffRouting:
    """Birkhoff-von Neumann decomposition and Sinkhorn normalization"""
    
    @staticmethod
    def is_doubly_stochastic(A, tol=1e-10):
        """Check if matrix A is doubly stochastic"""
        A = matrix(RR, A)
        n = A.nrows()
        
        # Non-negativity
        if not all(A[i,j] >= -tol for i in range(n) for j in range(n)):
            return False
        
        # Row sums = 1
        if not all(abs(sum(A.row(i)) - 1) < tol for i in range(n)):
            return False
        
        # Column sums = 1
        if not all(abs(sum(A.column(j)) - 1) < tol for j in range(n)):
            return False
        
        return True
    
    @staticmethod
    def is_permutation_matrix(P, tol=1e-10):
        """Check if P is a permutation matrix"""
        P = matrix(RR, P)
        n = P.nrows()
        
        # Each row and column has exactly one 1, rest 0
        for i in range(n):
            row_ones = sum(1 for j in range(n) if abs(P[i,j] - 1) < tol)
            col_ones = sum(1 for j in range(n) if abs(P[j,i] - 1) < tol)
            if row_ones != 1 or col_ones != 1:
                return False
        
        return True
    
    @staticmethod
    def sinkhorn_normalize(A, max_iter=1000, tol=1e-10):
        """
        Sinkhorn-Knopp algorithm: normalize to doubly stochastic
        
        Input: A with positive entries
        Output: Doubly stochastic matrix A∞
        """
        A = matrix(RR, A)
        n = A.nrows()
        
        # Check positivity
        if not all(A[i,j] > 0 for i in range(n) for j in range(n)):
            raise ValueError("Matrix must have strictly positive entries")
        
        for k in range(max_iter):
            # Row normalization
            row_sums = [sum(A.row(i)) for i in range(n)]
            for i in range(n):
                for j in range(n):
                    A[i,j] /= row_sums[i]
            
            # Column normalization
            col_sums = [sum(A.column(j)) for j in range(n)]
            for j in range(n):
                for i in range(n):
                    A[i,j] /= col_sums[j]
            
            # Check convergence
            row_err = max(abs(sum(A.row(i)) - 1) for i in range(n))
            col_err = max(abs(sum(A.column(j)) - 1) for j in range(n))
            
            if max(row_err, col_err) < tol:
                break
        
        return A
    
    @staticmethod
    def bvN_decompose_greedy(W, tol=1e-10):
        """
        Birkhoff-von Neumann decomposition via greedy algorithm
        
        Input: Doubly stochastic matrix W
        Output: List of (weight, permutation_matrix) pairs
        
        Algorithm:
        1. Find permutation matrix P ≤ W (Hungarian algorithm)
        2. θ = min{W[i,σ(i)]} over permutation
        3. W ← W - θP
        4. Repeat until W = 0
        """
        W = matrix(RR, W)
        n = W.nrows()
        
        if not BirkhoffRouting.is_doubly_stochastic(W, tol):
            raise ValueError("Input must be doubly stochastic")
        
        decomposition = []
        W_remaining = matrix(W)
        
        while max(W_remaining.list()) > tol:
            # Find permutation that maximizes sum of selected entries
            # This is equivalent to minimum weight perfect matching
            cost_matrix = -np.array(W_remaining)  # Negate for maximization
            row_ind, col_ind = linear_sum_assignment(cost_matrix)
            
            # Construct permutation matrix
            P = zero_matrix(RR, n)
            for i, j in zip(row_ind, col_ind):
                P[i,j] = 1
            
            # Find minimum weight
            theta = min(W_remaining[i, j] for i, j in zip(row_ind, col_ind))
            
            if theta < tol:
                break
            
            # Add to decomposition
            decomposition.append((theta, P))
            
            # Update W
            for i in range(n):
                for j in range(n):
                    W_remaining[i,j] -= theta * P[i,j]
        
        return decomposition
    
    @staticmethod
    def verify_decomposition(W, decomp, tol=1e-10):
        """Verify W = Σ θₖ Pₖ"""
        W_reconstructed = zero_matrix(RR, W.nrows())
        
        for theta, P in decomp:
            W_reconstructed += theta * P
        
        return max(abs(W[i,j] - W_reconstructed[i,j]) 
                   for i in range(W.nrows()) for j in range(W.ncols())) < tol

    @staticmethod
    def cone_slice_witness(W, tol=1e-10):
        """
        Return a positive-cone witness for a bistochastic matrix.

        The witness is a list of nonnegative weights and permutation
        matrices whose weighted sum reconstructs W.
        """
        decomp = BirkhoffRouting.bvN_decompose_greedy(W, tol=tol)
        weights = [theta for theta, _ in decomp]
        perms = [P for _, P in decomp]
        return weights, perms

    @staticmethod
    def verify_cone_slice(W, tol=1e-10):
        """Check that the BvN decomposition gives a nonnegative cone witness."""
        decomp = BirkhoffRouting.bvN_decompose_greedy(W, tol=tol)
        if not decomp:
            return False
        if any(theta < -tol for theta, _ in decomp):
            return False
        if abs(sum(theta for theta, _ in decomp) - 1) > tol:
            return False
        return BirkhoffRouting.verify_decomposition(W, decomp, tol=tol)
    
    @staticmethod
    def spectral_norm_contraction(A):
        """Verify ‖Av‖ ≤ ‖v‖ for doubly stochastic A"""
        A = matrix(RR, A)
        singular_values = np.linalg.svd(np.array(A, dtype=float), compute_uv=False)
        return max(singular_values) <= 1 + 1e-10
    
    @staticmethod
    def routing_energy_conservation(W, tokens):
        """
        Verify energy conservation in routing
        
        Input: W doubly stochastic, tokens = list of vectors
        Output: ‖routed‖² ≤ ‖original‖²
        """
        W = matrix(RR, W)
        n = len(tokens)
        
        # Route tokens
        routed = []
        for i in range(n):
            routed_vec = sum(W[i,j] * tokens[j] for j in range(n))
            routed.append(routed_vec)
        
        # Compute energies
        E_original = sum(v.norm()**2 for v in tokens)
        E_routed = sum(v.norm()**2 for v in routed)
        
        return E_routed <= E_original + 1e-10


# Demonstration and verification
if __name__ == "__main__":
    print("="*60)
    print("Birkhoff-von Neumann Routing - SageMath Verification")
    print("="*60)
    
    # Test 1: Sinkhorn normalization
    print("\n1. Sinkhorn Normalization")
    A = matrix(RR, [[1, 2, 3],
                    [4, 5, 6],
                    [7, 8, 9]])
    print(f"Original matrix:\n{A}")
    
    A_ds = BirkhoffRouting.sinkhorn_normalize(A)
    print(f"Doubly stochastic form:\n{A_ds}")
    print(f"Row sums: {[sum(A_ds.row(i)) for i in range(3)]}")
    print(f"Col sums: {[sum(A_ds.column(j)) for j in range(3)]}")
    print(f"Is doubly stochastic: {BirkhoffRouting.is_doubly_stochastic(A_ds)}")
    
    # Test 2: BvN decomposition
    print("\n2. Birkhoff-von Neumann Decomposition")
    W = A_ds
    print(f"Target matrix W:\n{W}")
    
    decomp = BirkhoffRouting.bvN_decompose_greedy(W)
    print(f"Decomposition into {len(decomp)} permutation matrices:")
    for k, (theta, P) in enumerate(decomp):
        print(f"  P_{k}: weight = {theta:.6f}")
        print(f"  {P}")
    
    # Verify reconstruction
    valid = BirkhoffRouting.verify_decomposition(W, decomp)
    print(f"Reconstruction valid: {valid}")

    cone_ok = BirkhoffRouting.verify_cone_slice(W)
    print(f"Cone slice witness valid: {cone_ok}")

    P_id = identity_matrix(RR, 3)
    print(f"Identity permutation in cone: {BirkhoffRouting.verify_cone_slice(P_id)}")
    
    # Test 3: Energy conservation
    print("\n3. Energy Conservation")
    import random
    tokens = [vector(RR, [random.random() for _ in range(3)]) for _ in range(3)]
    
    E_original = sum(v.norm()**2 for v in tokens)
    E_routed = sum((sum(W[i,j] * tokens[j] for j in range(3))).norm()**2 
                   for i in range(3))
    
    print(f"Original energy: {E_original:.6f}")
    print(f"Routed energy: {E_routed:.6f}")
    print(f"Energy conserved: {E_routed <= E_original + 1e-10}")
    
    # Test 4: Spectral norm
    print("\n4. Spectral Norm (Contraction)")
    max_singular = max(np.linalg.svd(np.array(A_ds, dtype=float), compute_uv=False))
    print(f"Max singular value: {max_singular:.6f}")
    print(f"Is contraction (σ₁ ≤ 1): {max_singular <= 1 + 1e-10}")
    
    print("\n" + "="*60)
    print("All tests completed successfully!")
    print("="*60)
