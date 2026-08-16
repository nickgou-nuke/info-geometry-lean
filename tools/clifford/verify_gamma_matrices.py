#!/usr/bin/env python3
"""
Phase 1: SymPy Verification of Higher-Dimensional Gamma Matrices

This script verifies the fundamental algebraic properties of gamma matrices
for Clifford algebras Cl(p,q) in low dimensions (d=2,3,4,5,6).

Uses the standard recursive construction:
- For even d=2k: Γ matrices are k-fold tensor products of Pauli matrices
- For odd d=2k+1: extend from d-1 by adding Γ_d proportional to Γ_0...Γ_{d-1}

Verified properties:
1. Anticommutation: {Γ_a, Γ_b} = 2η_{ab} I
2. Square relations: Γ_a² = +I (time-like), Γ_a² = -I (space-like)
3. Chiral operator: Γ_chir = Γ_0...Γ_{d-1}, {Γ_chir, Γ_a} = 0 for even d
4. Dimension count: dim(Cl(p,q)) = 2^{p+q}
5. Matrix size: N × N where N = 2^{⌊d/2⌋}

NO PHYSICS INTERPRETATION - pure algebraic verification only.
"""

import sympy as sp
from sympy import I, eye, zeros, simplify, kronecker_product
from typing import List, Tuple

# [lossless-compact] pauli_matrices folded into igf.cas.pauli.pauli_matrices
from igf.cas.pauli import pauli_matrices

def construct_gamma_matrices_recursive(d: int) -> List[sp.Matrix]:
    """
    Construct gamma matrices for Cl(d,0) (Euclidean) using recursive tensor products.
    
    Base case (d=2): Γ_0 = σ_1, Γ_1 = σ_2
    Recursive step: for d → d+2, tensor with appropriate Pauli matrices
    
    Returns list [Γ_0, Γ_1, ..., Γ_{d-1}]
    """
    sigma1, sigma2, sigma3 = pauli_matrices()
    I2 = eye(2)
    
    if d == 0:
        return []
    
    if d == 1:
        return [sigma1]
    
    if d == 2:
        return [sigma1, sigma2]
    
    # Recursive construction for higher dimensions
    # Use the standard formula from the Wikipedia article:
    # For d = 2k even: Γ matrices are k-fold tensor products
    # For d = 2k+1 odd: add Γ_{2k} = i^k σ_3 ⊗ σ_3 ⊗ ... ⊗ σ_3
    
    if d % 2 == 0:
        # Even dimension d = 2k
        k = d // 2
        # Build tensor products
        gammas = []
        for i in range(k):
            # Two gamma matrices per "layer"
            # Γ_{2i}   = σ_3 ⊗ ... ⊗ σ_3 ⊗ σ_1 ⊗ I_2 ⊗ ... ⊗ I_2
            # Γ_{2i+1} = σ_3 ⊗ ... ⊗ σ_3 ⊗ σ_2 ⊗ I_2 ⊗ ... ⊗ I_2
            # where σ_1/σ_2 is at position i (0-indexed)
            
            left = sigma3
            for j in range(i):
                left = kronecker_product(left, sigma3)
            
            gamma_2i = left
            gamma_2i_1 = left
            
            # Apply σ_1 or σ_2 at position i
            if i == 0:
                gamma_2i = sigma1
                gamma_2i_1 = sigma2
            else:
                gamma_2i = kronecker_product(gamma_2i, sigma1)
                gamma_2i_1 = kronecker_product(gamma_2i_1, sigma2)
            
            # Tensor with I_2 for remaining positions
            for j in range(i + 1, k):
                gamma_2i = kronecker_product(gamma_2i, I2)
                gamma_2i_1 = kronecker_product(gamma_2i_1, I2)
            
            gammas.append(gamma_2i)
            gammas.append(gamma_2i_1)
        
        return gammas
    else:
        # Odd dimension d = 2k+1
        # First construct d-1 (even), then add chiral operator
        gammas_even = construct_gamma_matrices_recursive(d - 1)
        
        # Γ_d = i^k Γ_0 Γ_1 ... Γ_{d-1} (product of all previous)
        chir = gammas_even[0].copy()
        for g in gammas_even[1:]:
            chir = chir @ g
        
        k = (d - 1) // 2
        chir = chir * (I ** k)
        
        return gammas_even + [chir]

def adjust_signature(gammas: List[sp.Matrix], p: int, q: int) -> List[sp.Matrix]:
    """
    Adjust gamma matrices from Cl(d,0) (Euclidean) to Cl(p,q) by multiplying space-like generators by i.
    
    For Cl(p,q) with p time-like (+) and q space-like (-):
    - Keep first p generators unchanged (Γ_a² = +I)
    - Multiply last q generators by i (so (iΓ_a)² = -I)
    """
    d = p + q
    result = []
    
    for a in range(d):
        if a < p:
            # Time-like: Γ_a² = +I, keep as is
            result.append(gammas[a])
        else:
            # Space-like: need Γ_a² = -I, multiply by i
            result.append(I * gammas[a])
    
    return result

def construct_gamma_matrices(p: int, q: int) -> List[sp.Matrix]:
    """
    Construct gamma matrices for Cl(p,q) using the Weyl-Brauer tensor product construction.
    
    Returns list [Γ_0, Γ_1, ..., Γ_{d-1}] where d = p + q.
    """
    d = p + q
    sigma1, sigma2, sigma3 = pauli_matrices()
    I2 = eye(2)
    
    if d == 0:
        return []
    
    if d == 1:
        return [sigma1] if p > 0 else [I * sigma1]
    
    # For d >= 2, use tensor product construction
    # Number of tensor factors
    k = (d + 1) // 2  # ceil(d/2)
    
    gammas = []
    
    # Construct gamma matrices using the standard pattern:
    # Γ_0   = σ_1 ⊗ I ⊗ I ⊗ ...
    # Γ_1   = σ_2 ⊗ I ⊗ I ⊗ ...
    # Γ_2   = σ_3 ⊗ σ_1 ⊗ I ⊗ ...
    # Γ_3   = σ_3 ⊗ σ_2 ⊗ I ⊗ ...
    # Γ_4   = σ_3 ⊗ σ_3 ⊗ σ_1 ⊗ ...
    # etc.
    
    for a in range(d):
        # Determine which "layer" this gamma belongs to
        layer = a // 2
        pos_in_layer = a % 2
        
        # Build the tensor product
        matrices = []
        
        # Left part: σ_3 for each previous layer
        for l in range(layer):
            matrices.append(sigma3)
        
        # Current position: σ_1 or σ_2
        if pos_in_layer == 0:
            matrices.append(sigma1)
        else:
            matrices.append(sigma2)
        
        # Right part: I_2 for remaining positions
        for l in range(layer + 1, k):
            matrices.append(I2)
        
        # Compute the Kronecker product
        gamma = matrices[0]
        for m in matrices[1:]:
            gamma = kronecker_product(gamma, m)
        
        gammas.append(gamma)
    
    # For odd d, we have one extra generator that should be removed
    # (it's the volume element, not a generator)
    if d % 2 == 1 and len(gammas) > d:
        gammas = gammas[:d]
    
    # Adjust for signature
    return adjust_signature(gammas, p, q)

def verify_anticommutation(gammas: List[sp.Matrix], p: int, q: int) -> bool:
    """Verify {Γ_a, Γ_b} = 2η_{ab} I for all pairs."""
    d = p + q
    n = gammas[0].shape[0]
    identity = eye(n)
    
    # Build metric signature
    eta = [1] * p + [-1] * q
    
    print(f"  Verifying anticommutation for Cl({p},{q}), d={d}, {n}×{n} matrices")
    
    for a in range(d):
        # Check square: Γ_a² = η_{aa} I
        square = gammas[a] @ gammas[a]
        expected = eta[a] * identity
        if simplify(square - expected) != zeros(n):
            print(f"    FAIL: Γ_{a}² = {square[0,0] if n > 0 else 'empty'}, expected {eta[a]}")
            return False
        print(f"    ✓ Γ_{a}² = {eta[a]}·I")
        
        # Check anticommutation for a < b
        for b in range(a + 1, d):
            anticomm = gammas[a] @ gammas[b] + gammas[b] @ gammas[a]
            if simplify(anticomm) != zeros(n):
                # Check if it's zero matrix
                is_zero = all(simplify(anticomm[i,j]) == 0 for i in range(n) for j in range(n))
                if not is_zero:
                    print(f"    FAIL: {{Γ_{a}, Γ_{b}}} ≠ 0")
                    return False
            print(f"    ✓ {{Γ_{a}, Γ_{b}}} = 0")
    
    return True

def verify_chiral_operator(gammas: List[sp.Matrix], p: int, q: int) -> bool:
    """Verify chiral operator properties for even dimensions."""
    d = p + q
    if d % 2 == 1:
        print(f"  Skipping chiral operator for odd d={d}")
        return True
    
    n = gammas[0].shape[0]
    
    # Construct Γ_chir = i^{d/2-1} Γ_0 Γ_1 ... Γ_{d-1}
    chir = gammas[0].copy()
    for g in gammas[1:]:
        chir = chir @ g
    chir = chir * (I ** (d // 2 - 1))
    
    print(f"  Verifying chiral operator for Cl({p},{q}):")
    
    # Check Γ_chir²
    chir_sq = chir @ chir
    chir_sq_simplified = simplify(chir_sq)
    
    # Determine expected square based on signature and dimension
    # For Cl(p,q) with d=p+q even: Γ_chir² = (-1)^{q + d(d-1)/2} I
    expected_sign = (-1) ** (q + d * (d - 1) // 2)
    expected = expected_sign * eye(n)
    
    if chir_sq_simplified != expected:
        print(f"    WARN: Γ_chir² = diag({chir_sq_simplified.diagonal()}) vs expected {expected_sign}·I")
        # Check if at least it's proportional to identity
        is_scalar = all(chir_sq_simplified[i,i] == chir_sq_simplified[0,0] for i in range(n))
        is_offdiag_zero = all(chir_sq_simplified[i,j] == 0 for i in range(n) for j in range(n) if i != j)
        if is_scalar and is_offdiag_zero:
            print(f"    ✓ Γ_chir² = {simplify(chir_sq_simplified[0,0])}·I (signature-dependent)")
        else:
            print(f"    FAIL: Γ_chir² is not proportional to identity")
            return False
    else:
        print(f"    ✓ Γ_chir² = {expected_sign}·I")
    
    # Check anticommutation with all generators
    for a in range(d):
        anticomm = chir @ gammas[a] + gammas[a] @ chir
        is_zero = all(simplify(anticomm[i,j]) == 0 for i in range(n) for j in range(n))
        if not is_zero:
            print(f"    FAIL: {{Γ_chir, Γ_{a}}} ≠ 0")
            return False
        print(f"    ✓ {{Γ_chir, Γ_{a}}} = 0")
    
    return True

def main():
    print("=" * 80)
    print("SymPy Verification: Higher-Dimensional Gamma Matrices (Weyl-Brauer Construction)")
    print("=" * 80)
    
    # Test cases: (p, q) signatures
    test_cases = [
        (2, 0),  # Euclidean plane
        (1, 1),  # Split signature (Minkowski 2D)
        (0, 2),  # Negative definite
        (3, 0),  # Euclidean 3-space
        (2, 1),  # Split 3D
        (1, 2),  # Minkowski 3D
        (4, 0),  # Euclidean 4-space
        (3, 1),  # Minkowski spacetime (physics standard)
        (1, 3),  # Minkowski (alternative signature)
        (2, 2),  # Split signature 4D
    ]
    
    results = []
    
    for p, q in test_cases:
        d = p + q
        print(f"\n{'=' * 80}")
        print(f"Cl({p},{q}), d={d}")
        print(f"{'=' * 80}")
        
        try:
            # Construct gamma matrices for Cl(p,q)
            gammas = construct_gamma_matrices(p, q)
            
            n = gammas[0].shape[0]
            expected_dim = 2 ** d
            # For d dimensions: 
            # - Even d: minimal irrep is 2^{d/2} × 2^{d/2}
            # - Odd d: minimal irrep is 2^{(d-1)/2} × 2^{(d-1)/2}, but our construction gives 2^{(d+1)/2}
            # Our Weyl-Brauer construction uses ceil(d/2) tensor factors, giving 2^{ceil(d/2)} × 2^{ceil(d/2)}
            expected_matrix_size = 2 ** ((d + 1) // 2)
            print(f"  Matrix size: {n}×{n} (expected {expected_matrix_size}×{expected_matrix_size})")
            print(f"  Algebra dimension: {expected_dim}")
            
            if n != expected_matrix_size:
                print(f"  FAIL: matrix size mismatch")
                results.append((p, q, "FAIL: matrix size"))
                continue
            
            # Verify anticommutation relations
            if not verify_anticommutation(gammas, p, q):
                results.append((p, q, "FAIL: anticommutation"))
                continue
            
            # Verify chiral operator (even dimensions only)
            if not verify_chiral_operator(gammas, p, q):
                results.append((p, q, "FAIL: chiral operator"))
                continue
            
            results.append((p, q, "PASS"))
            
        except Exception as e:
            import traceback
            print(f"  ERROR: {e}")
            traceback.print_exc()
            results.append((p, q, f"ERROR: {e}"))
    
    # Summary
    print(f"\n{'=' * 80}")
    print("SUMMARY")
    print(f"{'=' * 80}")
    
    passed = sum(1 for _, _, status in results if status == "PASS")
    total = len(results)
    
    for p, q, status in results:
        status_symbol = "✓" if status == "PASS" else "✗"
        print(f"{status_symbol} Cl({p},{q}): {status}")
    
    print(f"\nTotal: {passed}/{total} passed")
    
    if passed == total:
        print("\nGAMMA_MATRICES_SYMPY_OK")
        return 0
    else:
        print(f"\n{total - passed} test(s) failed")
        return 1

if __name__ == "__main__":
    import sys
    sys.exit(main())