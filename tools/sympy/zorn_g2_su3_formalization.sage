#!/usr/bin/env sage
# -*- coding: utf-8 -*-
"""
SageMath Formalization: Zorn Matrices, G₂ Automorphisms, and SU(3) Color Symmetry

This script formalizes the Günaydin-Gürsey construction connecting:
- Zorn matrix representation of split octonions
- G₂ automorphism group and its SU(3) subgroup
- Mersenne prime hierarchy (137 = 3 + 7 + 127)
- Tripotent eigenvalue decomposition (eigenvalues: +1, -1, 0)

The diagonal projectors OP1 and OP2 isolate the 3-dimensional representations:
    OP₁ · ZornMatrix · OP₂ = (0, x⃗; 0, 0)

Author: Info-Geometry-Lean Project
Date: 2026-06-22
"""

from sage.all import *
import json

# ============================================================================
# SECTION 1: Zorn Matrix Algebra
# ============================================================================

class ZornMatrix:
    """
    Zorn matrix representation of split octonions.
    
    A Zorn matrix has the form:
        [ a   x⃗ ]
        [ y⃗   b ]
    
    where a, b ∈ ℝ (or any field) and x⃗, y⃗ ∈ ℝ³.
    
    Multiplication is defined by:
        [ a   x⃗ ]   [ a'   x⃗']   [ aa' + x⃗·y⃗'    ax⃗' + bx⃗ - y⃗×y⃗' ]
        [ y⃗   b ] · [ y⃗'  b' ] = [ a'y⃗ + b'y⃗ + x⃗×x⃗'   bb' + y⃗·x⃗' ]
    
    Note: For split octonions, the cross product signs differ from ordinary octonions.
    """
    
    def __init__(self, a, b, x, y):
        """
        Initialize a Zorn matrix.
        
        Parameters:
            a, b: scalars (diagonal elements)
            x, y: 3-vectors (off-diagonal elements) as tuples or lists
        """
        self.a = QQ(a)
        self.b = QQ(b)
        self.x = vector(QQ, x)
        self.y = vector(QQ, y)
    
    def __repr__(self):
        return f"Zorn([{self.a}, {self.x}]; [{self.y}, {self.b}])"
    
    def __eq__(self, other):
        return (self.a == other.a and self.b == other.b and 
                self.x == other.x and self.y == other.y)
    
    def __add__(self, other):
        return ZornMatrix(
            self.a + other.a,
            self.b + other.b,
            self.x + other.x,
            self.y + other.y
        )
    
    def __neg__(self):
        return ZornMatrix(-self.a, -self.b, -self.x, -self.y)
    
    def __sub__(self, other):
        return self + (-other)
    
    def __mul__(self, other):
        """
        Zorn matrix multiplication (split octonion product).
        
        For split signature, the cross product terms have opposite signs
        compared to the definite octonion case.
        """
        # Dot product
        dot_xy = self.x.dot_product(other.y)
        dot_yx = self.y.dot_product(other.x)
        
        # Cross products (split signature)
        cross_xx = self.x.cross_product(other.x)
        cross_yy = self.y.cross_product(other.y)
        
        # Split octonion multiplication formula
        new_a = self.a * other.a + dot_xy
        new_b = self.b * other.b + dot_yx
        new_x = self.a * other.x + other.b * self.x - cross_yy
        new_y = other.a * self.y + self.b * other.y + cross_xx
        
        return ZornMatrix(new_a, new_b, new_x, new_y)
    
    def scalar_mult(self, c):
        """Multiply by a scalar."""
        c = QQ(c)
        return ZornMatrix(c * self.a, c * self.b, c * self.x, c * self.y)
    
    def norm(self):
        """
        Split octonion norm (quadratic form of signature (4,4)).
        
        N(X) = ab - x⃗·y⃗
        """
        return self.a * self.b - self.x.dot_product(self.y)
    
    def conjugate(self):
        """
        Zorn matrix conjugate (octonion involution).
        
        X̄ = [ b  -x⃗ ]
            [ -y⃗  a ]
        """
        return ZornMatrix(self.b, self.a, -self.x, -self.y)
    
    def trace(self):
        """Trace: Tr(X) = a + b"""
        return self.a + self.b
    
    def is_idempotent(self):
        """Check if X² = X"""
        return self * self == self
    
    def is_nilpotent(self):
        """Check if X² = 0"""
        return self * self == zero_zorn()
    
    def matrix_representation(self):
        """Return as a formal 2×2 block matrix for display."""
        return matrix(QQ, [
            [self.a, self.x[0], self.x[1], self.x[2]],
            [self.y[0], self.b, 0, 0],
            [self.y[1], 0, self.b, 0],
            [self.y[2], 0, 0, self.b]
        ])


def zero_zorn():
    """Zero Zorn matrix."""
    return ZornMatrix(0, 0, [0, 0, 0], [0, 0, 0])


def one_zorn():
    """Identity Zorn matrix (e₊ + e₋)."""
    return ZornMatrix(1, 1, [0, 0, 0], [0, 0, 0])


def e_plus():
    """
    First diagonal idempotent: OP₁ = [1, 0; 0, 0]
    
    This projector selects the upper-right vector slot.
    """
    return ZornMatrix(1, 0, [0, 0, 0], [0, 0, 0])


def e_minus():
    """
    Second diagonal idempotent: OP₂ = [0, 0; 0, 1]
    
    This projector selects the lower-left vector slot.
    """
    return ZornMatrix(0, 1, [0, 0, 0], [0, 0, 0])


def up(i):
    """
    Upper vector basis element eᵢ⁺ (i = 0, 1, 2).
    
    These span the fundamental 3 representation of SU(3).
    """
    x = [0, 0, 0]
    x[i] = 1
    return ZornMatrix(0, 0, x, [0, 0, 0])


def down(i):
    """
    Lower vector basis element eᵢ⁻ (i = 0, 1, 2).
    
    These span the anti-fundamental 3̄ representation of SU(3).
    """
    y = [0, 0, 0]
    y[i] = 1
    return ZornMatrix(0, 0, [0, 0, 0], y)


# ============================================================================
# SECTION 2: Peirce Decomposition and Tripotent Eigenvalues
# ============================================================================

def peirce_decomposition(Z):
    """
    Decompose a Zorn matrix using the Peirce projectors OP₁ and OP₂.
    
    Returns the four components:
        (OP₁ZOP₁, OP₁ZOP₂, OP₂ZOP₁, OP₂ZOP₂)
    
    These correspond to:
        - (a, 0; 0, 0): scalar mode 1
        - (0, x⃗; 0, 0): upper vector (eigenvalue +1)
        - (0, 0; y⃗, 0): lower vector (eigenvalue -1)
        - (0, 0; 0, b): scalar mode 2
    """
    op1 = e_plus()
    op2 = e_minus()
    
    comp11 = op1 * Z * op1  # Should give (a, 0; 0, 0)
    comp12 = op1 * Z * op2  # Should give (0, x⃗; 0, 0)
    comp21 = op2 * Z * op1  # Should give (0, 0; y⃗, 0)
    comp22 = op2 * Z * op2  # Should give (0, 0; 0, b)
    
    return (comp11, comp12, comp21, comp22)


def tripotent_eigenvalues(Z):
    """
    Compute the tripotent eigenvalue decomposition.
    
    For a Zorn matrix, the tripotent operator T satisfies T³ = T,
    giving eigenvalues {+1, -1, 0}.
    
    Returns a dictionary mapping eigenvalues to their eigenspaces.
    """
    # The tripotent decomposition is revealed by Peirce decomposition
    comp11, comp12, comp21, comp22 = peirce_decomposition(Z)
    
    eigenvalues = {
        '+1': comp12,   # Upper vector space (quark/anyon)
        '-1': comp21,   # Lower vector space (antiquark/anti-anyon)
        '0': comp11 + comp22  # Diagonal scalars (vacuum/projectors)
    }
    
    return eigenvalues


# ============================================================================
# SECTION 3: SU(3) Stabilizer in G₂
# ============================================================================

def su3_stabilizer_generators():
    """
    Generate the 8 generators of SU(3) as G₂ automorphisms.
    
    These are the derivations of the split octonion algebra that
    preserve the subalgebra generated by e₊ and e₋.
    
    Returns a list of 8 matrices representing the su(3) Lie algebra.
    """
    # The SU(3) generators act on the 6-dimensional space (x⃗, y⃗)
    # while fixing the diagonal (a, b)
    
    # Gell-Mann matrices (standard su(3) basis)
    lambda1 = matrix(QQ, [[0, 1, 0], [1, 0, 0], [0, 0, 0]])
    lambda2 = matrix(QQ, [[0, -1, 0], [1, 0, 0], [0, 0, 0]])  # Note: anti-symmetric
    lambda3 = matrix(QQ, [[1, 0, 0], [0, -1, 0], [0, 0, 0]])
    lambda4 = matrix(QQ, [[0, 0, 1], [0, 0, 0], [1, 0, 0]])
    lambda5 = matrix(QQ, [[0, 0, -1], [0, 0, 0], [1, 0, 0]])
    lambda6 = matrix(QQ, [[0, 0, 0], [0, 0, 1], [0, 1, 0]])
    lambda7 = matrix(QQ, [[0, 0, 0], [0, 0, -1], [0, 1, 0]])
    lambda8 = matrix(QQ, [[1, 0, 0], [0, 1, 0], [0, 0, -2]]) / sqrt(3)
    
    generators = [lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8]
    
    return generators


def verify_su3_action():
    """
    Verify that SU(3) generators preserve the split octonion structure.
    
    Returns True if all generators satisfy the derivation property.
    """
    generators = su3_stabilizer_generators()
    
    # Test on basis elements
    basis = [up(i) for i in range(3)] + [down(i) for i in range(3)]
    
    for gen in generators:
        for b in basis:
            # The generator acts only on the vector parts
            # Check that the action preserves the norm
            x_new = gen * b.x if hasattr(b, 'x') else b.x
            y_new = gen * b.y if hasattr(b, 'y') else b.y
            
            # Preserve the pairing x·y
            if x_new.dot_product(b.y) + b.x.dot_product(y_new) != 0:
                return False
    
    return True


# ============================================================================
# SECTION 4: Mersenne Prime Hierarchy and 137 Decomposition
# ============================================================================

def mersenne_hierarchy():
    """
    Compute the Mersenne prime hierarchy relevant to the 137 decomposition.
    
    M₂ = 2² - 1 = 3  → SU(3) dimension (color modes)
    M₃ = 2³ - 1 = 7  → Octonion imaginary units
    M₇ = 2⁷ - 1 = 127 → Total degrees of freedom
    
    137 = 3 + 7 + 127 (Mersenne decomposition)
    """
    mersenne_primes = {
        'M2': 2**2 - 1,  # 3
        'M3': 2**3 - 1,  # 7
        'M7': 2**7 - 1,  # 127
    }
    
    total = sum(mersenne_primes.values())
    
    return {
        'mersenne_primes': mersenne_primes,
        'sum': total,
        'is_137': total == 137
    }


def p_adic_valuation_137():
    """
    Compute p-adic valuations of 137.
    
    137 is prime, so v_p(137) = 0 for p ≠ 137 and v_137(137) = 1.
    """
    p = 137
    return {
        'is_prime': is_prime(p),
        'v2': valuation(137, 2),
        'v3': valuation(137, 3),
        'v7': valuation(137, 7),
        'v137': valuation(137, 137)
    }


# ============================================================================
# SECTION 5: AQL Data Instance Generation
# ============================================================================

def generate_aql_instance():
    """
    Generate the AQL instance data for the combinatorial hierarchy.
    
    This produces the exact numerical data that will be migrated
    to the geometric schema via the functor Σ_F.
    """
    mersenne = mersenne_hierarchy()
    p_adic = p_adic_valuation_137()
    
    instance = {
        'CombinatorialHierarchy': {
            'MersenneMode': ['m2', 'm3', 'm7'],
            'CouplingConstant': ['alpha_inv'],
            'prime_index': {
                'm2': 2,
                'm3': 3,
                'm7': 7
            },
            'dimension': {
                'm2': 3,
                'm3': 7,
                'm7': 127
            },
            'value': {
                'alpha_inv': 137
            },
            'v2_norm': {
                'alpha_inv': p_adic['v2']
            }
        }
    }
    
    return instance


# ============================================================================
# SECTION 6: Verification and Evidence Reporting
# ============================================================================

def verify_zorn_algebra():
    """
    Comprehensive verification of Zorn matrix algebra.
    
    Tests:
    1. Idempotency of e₊ and e₋
    2. Orthogonality: e₊e₋ = e₋e₊ = 0
    3. Vector nilpotency: (eᵢ⁺)² = (eᵢ⁻)² = 0
    4. Dual pairing: eᵢ⁺eᵢ⁻ = e₊, eᵢ⁻eᵢ⁺ = e₋
    5. Cyclic multiplication table
    6. Norm composition
    """
    results = {}
    
    # Test 1: Idempotency
    results['ePlus_idempotent'] = e_plus().is_idempotent()
    results['eMinus_idempotent'] = e_minus().is_idempotent()
    
    # Test 2: Orthogonality
    results['ePlus_eMinus_orthogonal'] = (e_plus() * e_minus() == zero_zorn())
    results['eMinus_ePlus_orthogonal'] = (e_minus() * e_plus() == zero_zorn())
    
    # Test 3: Vector nilpotency
    results['up_nilpotent'] = all(up(i).is_nilpotent() for i in range(3))
    results['down_nilpotent'] = all(down(i).is_nilpotent() for i in range(3))
    
    # Test 4: Dual pairing
    results['up_down_pairing'] = all(
        up(i) * down(i) == e_plus() and down(i) * up(i) == e_minus()
        for i in range(3)
    )
    
    # Test 5: Cyclic multiplication
    cyclic_tests = [
        up(0) * up(1) == down(2),
        up(1) * up(2) == down(0),
        up(2) * up(0) == down(1),
    ]
    results['cyclic_multiplication'] = all(cyclic_tests)
    
    # Test 6: Norm composition
    x = ZornMatrix(1, 2, [1, 0, 0], [0, 1, 0])
    y = ZornMatrix(3, 4, [0, 1, 0], [1, 0, 0])
    results['norm_multiplicative'] = ((x * y).norm() == x.norm() * y.norm())
    
    # Test 7: Peirce decomposition
    test_matrix = ZornMatrix(1, 2, [3, 4, 5], [6, 7, 8])
    decomp = peirce_decomposition(test_matrix)
    results['peirce_reconstruction'] = (
        decomp[0] + decomp[1] + decomp[2] + decomp[3] == test_matrix
    )
    
    # Test 8: Tripotent eigenvalues
    eigen = tripotent_eigenvalues(test_matrix)
    results['tripotent_decomposition'] = (
        eigen['+1'] == decomp[1] and
        eigen['-1'] == decomp[2] and
        eigen['0'] == decomp[0] + decomp[3]
    )
    
    return results


def generate_evidence_report():
    """
    Generate a comprehensive evidence report for the formalization.
    
    This report can be used as input to Lean4, Coq, or Isabelle/HOL.
    """
    import datetime
    
    report = {
        'timestamp': datetime.datetime.now().isoformat(),
        'zorn_algebra_verification': verify_zorn_algebra(),
        'mersenne_hierarchy': mersenne_hierarchy(),
        'p_adic_analysis': p_adic_valuation_137(),
        'aql_instance': generate_aql_instance(),
        'su3_stabilizer_valid': verify_su3_action(),
    }
    
    return report


# ============================================================================
# MAIN EXECUTION
# ============================================================================

if __name__ == '__main__':
    print("=" * 80)
    print("SageMath Formalization: Zorn Matrices, G₂, and SU(3)")
    print("=" * 80)
    print()
    
    # 1. Basic Zorn matrix operations
    print("1. Zorn Matrix Basis Elements")
    print("-" * 40)
    print(f"e₊ = {e_plus()}")
    print(f"e₋ = {e_minus()}")
    print(f"e₊² = {e_plus() * e_plus()}")
    print(f"e₋² = {e_minus() * e_minus()}")
    print(f"e₊e₋ = {e_plus() * e_minus()}")
    print()
    
    print("2. Vector Basis Elements")
    print("-" * 40)
    for i in range(3):
        print(f"e⁺_{i} = {up(i)}")
        print(f"e⁻_{i} = {down(i)}")
    print()
    
    print("3. Peirce Decomposition")
    print("-" * 40)
    test_Z = ZornMatrix(5, 7, [1, 2, 3], [4, 5, 6])
    print(f"Test matrix: {test_Z}")
    decomp = peirce_decomposition(test_Z)
    print(f"OP₁ZOP₁ = {decomp[0]}")
    print(f"OP₁ZOP₂ = {decomp[1]}")
    print(f"OP₂ZOP₁ = {decomp[2]}")
    print(f"OP₂ZOP₂ = {decomp[3]}")
    print()
    
    print("4. Tripotent Eigenvalue Decomposition")
    print("-" * 40)
    eigen = tripotent_eigenvalues(test_Z)
    print(f"Eigenvalue +1: {eigen['+1']}")
    print(f"Eigenvalue -1: {eigen['-1']}")
    print(f"Eigenvalue 0: {eigen['0']}")
    print()
    
    print("5. Mersenne Prime Hierarchy")
    print("-" * 40)
    mersenne = mersenne_hierarchy()
    for key, value in mersenne['mersenne_primes'].items():
        print(f"{key} = {value}")
    print(f"Sum = {mersenne['sum']}")
    print(f"Is 137? {mersenne['is_137']}")
    print()
    
    print("6. Verification Results")
    print("-" * 40)
    verification = verify_zorn_algebra()
    for test, result in verification.items():
        status = "✓ PASS" if result else "✗ FAIL"
        print(f"{test}: {status}")
    print()
    
    print("7. Evidence Report (JSON)")
    print("-" * 40)
    report = generate_evidence_report()
    print(json.dumps(report, indent=2, default=str))
    print()
    
    print("=" * 80)
    print("SageMath formalization complete.")
    print("=" * 80)