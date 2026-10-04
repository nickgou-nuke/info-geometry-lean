#!/usr/bin/env python3
"""Exploratory finite calculations for convexity, skew matrices, and weights.

The checks in this script do not prove a causal chain from LLM attention to
fluid dynamics or a KMS condition. A trace-free matrix is the Jacobian of a
divergence-free *linear* vector field when used as that field's Jacobian.
Finite softmax weights are Gibbs-form probabilities for energy equal to the
negative logits; verifying normalization does not establish the KMS condition.
"""

import numpy as np
from typing import Tuple, Callable
import sympy as sp

# ============================================================================
# STAGE 1: Quadratic Potential and Its Gradient
# ============================================================================

def quadratic_potential_and_gradient(theta: np.ndarray) -> Tuple[float, np.ndarray]:
    """
    For the illustrative potential L(θ)=||θ||², return its value and
    gradient. This is not a Fenchel conjugate computation.
    """
    # Simple quadratic loss as example: L(θ) = ||θ||²
    L = np.sum(theta ** 2)
    
    # Dual variable: η = ∇L = 2θ
    eta = 2 * theta
    
    return L, eta


def verify_quadratic_nonnegative(theta: np.ndarray) -> bool:
    """
    Check the elementary fact that the chosen squared norm is nonnegative.
    """
    L, _eta = quadratic_potential_and_gradient(theta)
    return bool(L >= 0)


# ============================================================================
# STAGE 2: Euclidean Direction Normalization
# ============================================================================

def normalize_or_zero(eta: np.ndarray) -> np.ndarray:
    """
    Normalize a nonzero Euclidean vector, and return zero for a vector
    below the numerical threshold. This is not a Krein-space projection.
    """
    # Normalize to get direction
    norm = np.linalg.norm(eta)
    if norm < 1e-10:
        return np.zeros_like(eta)
    
    base_velocity = eta / norm
    
    return base_velocity


def simple_bivector_skew_matrix(v: np.ndarray) -> np.ndarray:
    """
    Encode the coefficients of the simple exterior bivector v ∧ e₀ in a
    skew-symmetric matrix. This matrix is not asserted to be a Clifford
    representation.
    """
    # Add one basis direction e₀ and store the wedge coefficients.
    n = len(v)
    B = np.zeros((n+1, n+1))
    
    # B₀ᵢ = vᵢ, Bᵢ₀ = -vᵢ
    for i, vi in enumerate(v, start=1):
        B[0, i] = vi
        B[i, 0] = -vi
    
    return B


# ============================================================================
# STAGE 3: Trace of the Skew Matrix
# ============================================================================

def bivector_trace(B: np.ndarray) -> float:
    """
    Compute the trace of the matrix encoding the simple bivector.
    """
    return np.trace(B)


def verify_trace_free(B: np.ndarray) -> bool:
    """
    Numerically check that the skew-symmetric matrix has trace zero.
    """
    tr = bivector_trace(B)
    return np.abs(tr) < 1e-10


# ============================================================================
# STAGE 4: Divergence of the Associated Linear Vector Field
# ============================================================================

def linear_field_divergence_from_jacobian(B: np.ndarray) -> float:
    """
    For the linear vector field u(x) = Bx, the Jacobian is B and
    div(u) = trace(B). This is a finite-dimensional calculus identity.
    """
    # Interpret B specifically as the Jacobian of x ↦ Bx.
    return bivector_trace(B)  # Same mathematical object


def verify_divergence_free(B: np.ndarray) -> bool:
    """
    Verify the divergence of the linear field x ↦ Bx is zero.
    """
    div = linear_field_divergence_from_jacobian(B)
    return np.abs(div) < 1e-10


# ============================================================================
# STAGE 5: Finite Gibbs-Form Weights
# ============================================================================

def softmax_as_finite_gibbs_weights(logits: np.ndarray, beta: float = 1.0) -> np.ndarray:
    """
    Finite Gibbs-form weights with energy H_i = -logits_i.
    
    For logits z, the softmax is:
      p_i = exp(β z_i) / Σ_j exp(β z_j)
    
    This gives exp(-β H_i) / Z. A probability vector alone is not a KMS
    state; that notion also requires an observable algebra and time evolution.
    """
    # Direct finite Gibbs-weight formula.
    exp_z = np.exp(beta * logits)
    p = exp_z / np.sum(exp_z)
    return p


def verify_gibbs_probability_weights(p: np.ndarray) -> Tuple[bool, float]:
    """
    Verify the normalization and positivity of finite Gibbs weights.
    
    Properties:
    1. Σ p_i = 1 (normalization)
    2. p_i > 0 (positivity)
    3. Minimum entropy at β → ∞ (pure state)
    """
    # Normalization
    norm = np.sum(p)
    
    # Positivity
    positive = bool(np.all(p > 0))
    
    # Entropy
    entropy = -np.sum(p * np.log(p + 1e-10))
    
    return (bool(np.abs(norm - 1) < 1e-10) and positive, entropy)


# ============================================================================
# Independent Finite Checks
# ============================================================================

class FiniteStructureChecks:
    """
    Runs several independent finite numerical checks; they are not a proof of
    a causal relation among information theory, attention, and fluid physics.
    """
    
    def __init__(self):
        self.results = {}
    
    def run_checks(self, theta: np.ndarray, logits: np.ndarray | None = None):
        """
        Execute and verify the entire chain.
        """
        print("=" * 80)
        print("INDEPENDENT FINITE STRUCTURE CHECKS")
        print("=" * 80)
        print()
        print("Checks: quadratic gradient, skew-matrix trace, linear-field divergence,")
        print("        and finite Gibbs-form probability weights")
        print()
        
        # Stage 1: Information Theory → Convex Analysis
        print("### Stage 1: Information Theory → Convex Analysis ###")
        print(f"Input θ: {theta}")
        L, eta = quadratic_potential_and_gradient(theta)
        info_eq = verify_quadratic_nonnegative(theta)
        print(f"Quadratic potential L(θ) = {L:.6f}")
        print(f"Gradient ∇L(θ) = {eta}")
        print(f"✓ Quadratic potential is nonnegative: {info_eq}")
        self.results['stage1'] = {'L': L, 'eta': eta, 'verified': info_eq}
        print()
        
        # Stage 2: Euclidean normalization and a skew coefficient matrix
        print("### Stage 2: Euclidean Direction and Simple Bivector Matrix ###")
        v = normalize_or_zero(eta)
        B = simple_bivector_skew_matrix(v)
        print(f"Normalized direction v = {v}")
        print(f"Skew matrix B encoding v ∧ e₀:")
        print(B)
        self.results['stage2'] = {'velocity': v, 'bivector': B}
        print()
        
        # Stage 3: the skew-matrix trace
        print("### Stage 3: Trace of the Skew Matrix ###")
        tr = bivector_trace(B)
        trace_free = verify_trace_free(B)
        print(f"Trace(B) = {tr:.10f}")
        print(f"✓ Trace-free condition (Trace=0): {trace_free}")
        self.results['stage3'] = {'trace': tr, 'verified': trace_free}
        print()
        
        # Stage 4: view B as the Jacobian of the explicit linear field x ↦ Bx
        print("### Stage 4: Divergence of the Linear Field x ↦ Bx ###")
        div = linear_field_divergence_from_jacobian(B)
        div_free = verify_divergence_free(B)
        print(f"Divergence ∇·u = {div:.10f}")
        print(f"✓ Divergence-free flow (∇·u=0): {div_free}")
        self.results['stage4'] = {'divergence': div, 'verified': div_free}
        print()
        
        # Stage 5: finite Gibbs-form softmax weights
        print("### Stage 5: Finite Gibbs-Form Softmax Weights ###")
        if logits is None:
            logits = np.random.randn(5)  # Random logits
        p = softmax_as_finite_gibbs_weights(logits)
        weights_valid, entropy = verify_gibbs_probability_weights(p)
        print(f"Logits: {logits}")
        print(f"Softmax Gibbs-form weights: p = {p}")
        print(f"Entropy: S = {entropy:.6f}")
        print(f"✓ Normalized positive probability vector: {weights_valid}")
        self.results['stage5'] = {'probabilities': p, 'entropy': entropy, 'verified': weights_valid}
        print()
        
        # Complete chain verification
        print("=" * 80)
        print("FINITE CHECK SUMMARY")
        print("=" * 80)
        
        all_verified = (
            self.results['stage1']['verified'] and
            self.results['stage2'] is not None and
            self.results['stage3']['verified'] and
            self.results['stage4']['verified'] and
            self.results['stage5']['verified']
        )
        
        if all_verified:
            print("\n✅ LOCAL SCRIPTED CHECKS PASSED")
            print("\nThe configured checks establish these separate facts:")
            print("  The selected quadratic potential is nonnegative.")
            print("  The constructed skew matrix has trace zero.")
            print("  Interpreting that matrix as the Jacobian of u(x)=Bx gives")
            print("  a linear vector field with zero divergence.")
            print()
            print("Additional local script output:")
            print("  - Softmax weights have finite Gibbs form and are normalized")
            print()
            print("Status:")
            print("  The script's staged checks passed for this test configuration.")
            print("  Any broader AI/ML or physics interpretation remains outside")
            print("  the verified scope of this executable check.")
        else:
            print("\n⚠️  VERIFICATION FAILED")
            for stage, result in self.results.items():
                if not result.get('verified', True):
                    print(f"  ✗ {stage} failed")
        
        print("=" * 80)
        
        return all_verified


# ============================================================================
# Main Execution
# ============================================================================

def main():
    """Run the illustrative finite checks."""
    print("\n" + "=" * 80)
    print("FINITE CONVEXITY, MATRIX, AND PROBABILITY CHECKS")
    print("Exploratory calculations; no cross-domain theorem is claimed")
    print("=" * 80 + "\n")
    
    # Test case 1: Simple gradient
    theta = np.array([1.0, 2.0, 3.0])
    logits = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
    
    verifier = FiniteStructureChecks()
    result = verifier.run_checks(theta, logits)
    
    # Test case 2: the quadratic potential is small near the zero vector.
    print("\n\n" + "=" * 80)
    print("TEST CASE 2: Quadratic Potential Near Zero")
    print("=" * 80 + "\n")
    
    theta_eq = np.array([1e-6, 1e-6, 1e-6])
    result_eq = verifier.run_checks(theta_eq, logits)
    
    # Summary
    print("\n" + "=" * 80)
    print("FINAL SUMMARY")
    print("=" * 80)
    print()
    
    if result and result_eq:
        print("✅ ALL CONFIGURED FINITE CHECKS PASSED")
        print()
        print("Mathematical content:")
        print("  ✓ Quadratic gradient was calculated.")
        print("  ✓ The constructed skew matrix has trace zero.")
        print("  ✓ The associated linear vector field has zero divergence.")
        print("  ✓ Softmax gives normalized positive finite Gibbs-form weights.")
        print()
        print("Interpretive status:")
        print("  The local scripted checks succeeded for the configured examples.")
        print("  Broader conclusions about LLM attention or physics are not")
        print("  certified by this script alone.")
    else:
        print("⚠️  SOME VERIFICATIONS FAILED")
    
    print("\n" + "=" * 80 + "\n")
    
    return result and result_eq


if __name__ == "__main__":
    import sys
    success = main()
    sys.exit(0 if success else 1)
