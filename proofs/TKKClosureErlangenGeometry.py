#!/usr/bin/env python3
"""
Finite matrix diagnostics for chiral generators and Pauli soldering
==================================================================

This script checks selected finite matrix identities numerically. In particular,
it checks chiral commutators and samples the determinant identity for the Pauli
soldering map. It does not construct or prove a five-graded TKK Lie algebra,
identify the two-dimensional span of the chiral ladder matrices with the full
four-dimensional Hermitian carrier, or derive Minkowski spacetime from that
span. Those are separate formalization obligations.

Usage:
  python TKKClosureErlangenGeometry.py
  python TKKClosureErlangenGeometry.py --plot
"""

import sys
import math
import cmath
from typing import Tuple, List, Dict

import numpy as np
from scipy import linalg
import mpmath as mp

mp.mp.dps = 50

# ══════════════════════════════════════════════════════════════════════════════
# Part 1:  Chiral Matrix Adjoint-Weight Identities
# ══════════════════════════════════════════════════════════════════════════════

# Matrix-unit basis for Mat₂(ℂ); these are named matrices, not assigned
# homogeneous components of a constructed graded Lie algebra.
N_plus  = np.array([[1, 0], [0, 0]], dtype=complex)   # E₁₁
N_minus = np.array([[0, 0], [0, 1]], dtype=complex)   # E₂₂
S_plus  = np.array([[0, 1], [0, 0]], dtype=complex)   # E₁₂
S_minus = np.array([[0, 0], [1, 0]], dtype=complex)   # E₂₁
I2 = np.eye(2, dtype=complex)

# Diagonal adjoint-weight operator h = E₁₁ − E₂₂ = σ₃
h = N_plus - N_minus

# Pauli matrices for reference
sigma_1 = np.array([[0, 1], [1, 0]], dtype=complex)
sigma_2 = np.array([[0, -1j], [1j, 0]], dtype=complex)
sigma_3 = np.array([[1, 0], [0, -1]], dtype=complex)


def commutator(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    """Lie bracket: [A, B] = AB − BA."""
    return A @ B - B @ A


def verify_grading() -> Dict:
    """
    Check selected commutators with h = diag(1,-1).

    The represented matrices have adjoint weights -2, 0, and +2. These
    checks do not construct the missing ±2 components of a five-grading
    and do not prove bracket closure of a TKK algebra.
    """
    results = {}

    # ── Adjoint weight -2: S₋ ──────────────────────────────────
    comm_h_Sm = commutator(h, S_minus)
    results['[h, S₋] = -2·S₋'] = np.allclose(comm_h_Sm, -2.0 * S_minus)

    # ── Adjoint weight 0: diagonal matrix units ────────────────
    comm_h_Np = commutator(h, N_plus)
    comm_h_Nm = commutator(h, N_minus)
    results['[h, N₊] = 0'] = np.allclose(comm_h_Np, np.zeros((2,2)))
    results['[h, N₋] = 0'] = np.allclose(comm_h_Nm, np.zeros((2,2)))

    # ── Adjoint weight +2: S₊ ─────────────────────────────────
    comm_h_Sp = commutator(h, S_plus)
    results['[h, S₊] = +2·S₊'] = np.allclose(comm_h_Sp, 2.0 * S_plus)

    # These are commutator identities (not evidence for grade ±2 spaces).
    results['[S₋, S₋] = 0'] = np.allclose(
        commutator(S_minus, S_minus), np.zeros((2,2)))
    results['[S₊, S₊] = 0'] = np.allclose(
        commutator(S_plus, S_plus), np.zeros((2,2)))

    # ── Additional exact commutators among the four matrices ───
    comm_Sp_Sm = commutator(S_plus, S_minus)
    results['[S₊, S₋] = h'] = np.allclose(comm_Sp_Sm, h)

    # Matrix-unit commutators; no graded-closure conclusion is inferred.
    results['[S₊, N₊] = −S₊'] = np.allclose(
        commutator(S_plus, N_plus), -S_plus)

    results['[S₋, N₋] = −S₋'] = np.allclose(
        commutator(S_minus, N_minus), -S_minus)

    results['[S₊, N₋] = S₊'] = np.allclose(
        commutator(S_plus, N_minus), S_plus)

    results['[S₋, N₊] = S₋'] = np.allclose(
        commutator(S_minus, N_plus), S_minus)

    # ── Summary ──────────────────────────────────────────────
    results['all_matrix_weight_identities_hold'] = all(results.values())

    return results


# ══════════════════════════════════════════════════════════════════════════════
# Part 2:  Sampled Matrix Triple-Product Identities
# ══════════════════════════════════════════════════════════════════════════════

def triple_product(X: np.ndarray, Y: np.ndarray, Z: np.ndarray) -> np.ndarray:
    """
    Unnormalized Hermitian matrix triple product:
    {X, Y, Z} = X·Y†·Z + Z·Y†·X.

    This is twice the common JB*-triple normalization. Numerical samples
    below do not prove axioms or closure of a chosen subspace.
    """
    return X @ Y.conj().T @ Z + Z @ Y.conj().T @ X


def verify_triple_system() -> Dict:
    """Check selected basis triples; this is not a universal identity proof."""
    results = {}

    # Outer symmetry on a non-identical basis triple.
    X, Y, Z = S_plus, S_plus, S_minus
    t1 = triple_product(X, Y, Z)
    t2 = triple_product(Z, Y, X)
    results['sample outer symmetry'] = np.allclose(t1, t2)

    # {S₊, S₊, S₊} = 2·S₊ (the key triple structure)
    # In the JB*-triple: {x,y,z} = x·y*·z + z·y*·x
    # {S₊, S₊, S₊} = S₊·S₊*·S₊ + S₊·S₊*·S₊ = S₊·S₋·S₊ + S₊·S₋·S₊ = 2·S₊
    t_SSS = triple_product(S_plus, S_plus, S_plus)
    results['{S₊, S₊, S₊} = 2·S₊'] = np.allclose(t_SSS, 2.0 * S_plus)

    # {S₋, S₋, S₋} = 2·S₋
    t_mmm = triple_product(S_minus, S_minus, S_minus)
    results['{S₋, S₋, S₋} = 2·S₋'] = np.allclose(t_mmm, 2.0 * S_minus)

    # {S₊, S₊, S₋} = 0 (nilpotence)
    t_SSm = triple_product(S_plus, S_plus, S_minus)
    results['{S₊, S₊, S₋} = 0'] = np.allclose(t_SSm, np.zeros((2,2)))

    # {S₋, S₋, S₊} = 0
    t_mmS = triple_product(S_minus, S_minus, S_plus)
    results['{S₋, S₋, S₊} = 0'] = np.allclose(t_mmS, np.zeros((2,2)))

    results['all_sampled_triple_identities_hold'] = all(results.values())

    return results


def triple_left_operator_samples() -> Dict:
    """
    Return left-triple-operator matrices on the ordered basis (S₊, S₋).

    These two diagonal examples are finite calculations, not a construction
    or dimension theorem for the inner-derivation algebra of a TKK system.
    """
    # With {X,Y,Z}=XY†Z+ZY†X, the computed nonzero operators are
    # L(S₊,S₊) and L(S₋,S₋), in that order of basis vectors.
    L_Sp_Sp = np.array([[2, 0], [0, 0]], dtype=complex)
    L_Sm_Sm = np.array([[0, 0], [0, 2]], dtype=complex)
    L_Sp_Sm = np.zeros((2, 2), dtype=complex)
    L_Sm_Sp = np.zeros((2, 2), dtype=complex)

    return {
        'L(S₊, S₊)': L_Sp_Sp,
        'L(S₋, S₋)': L_Sm_Sm,
        'L(S₊, S₋)': L_Sp_Sm,
        'L(S₋, S₊)': L_Sm_Sp,
        'basis_order': '(S₊, S₋)',
        'scope': 'sampled left triple operators only; no TKK algebra constructed',
    }


# ══════════════════════════════════════════════════════════════════════════════
# Part 3:  Pauli Determinant and Minkowski Quadratic Form
# ══════════════════════════════════════════════════════════════════════════════

def minkowski_metric(t: float, x: float, y: float, z: float) -> float:
    """Q(t,x,y,z) = t² − x² − y² − z²."""
    return t**2 - x**2 - y**2 - z**2


def spacetime_matrix(t: float, x: float, y: float, z: float) -> np.ndarray:
    """
    X = t·I + x·σ₁ + y·σ₂ + z·σ₃
      = [[t+z, x−iy],
         [x+iy, t−z]]

    det(X) = t² − x² − y² − z² = the Minkowski metric.
    """
    return np.array([[t+z, x-1j*y],
                     [x+1j*y, t-z]], dtype=complex)


def verify_invariant_quadratic_form() -> Dict:
    """
    Numerically check det(X) = t² − x² − y² − z² at a sample point and
    check determinant invariance for sampled SL(2,ℂ) transformations.
    """
    results = {}

    # Test coordinates
    t, x, y, z = 2.0, 0.5, -0.3, 1.2
    X = spacetime_matrix(t, x, y, z)

    det_X = np.linalg.det(X)
    Q = minkowski_metric(t, x, y, z)

    results['det(X)'] = float(det_X.real)
    results['Q(t,x,y,z)'] = Q
    results['det(X) = Q'] = abs(float(det_X.real) - Q) < 1e-10

    # ── SL(2,ℂ) invariance ────────────────────────────────────
    # Construct a proper SL(2,ℂ) matrix via the polar decomposition:
    # Λ = U·exp(H) where U ∈ SU(2) and H is Hermitian with Tr(H)=0.
    rng = np.random.default_rng(172568)

    # Random SU(2) matrix (using the standard parameterization)
    phi = rng.uniform(0, 2*math.pi)
    theta = rng.uniform(0, math.pi)
    psi = rng.uniform(0, 2*math.pi)

    u11 = math.cos(theta/2) * cmath.exp(1j*(phi+psi)/2)
    u12 = math.sin(theta/2) * cmath.exp(1j*(phi-psi)/2) * 1j
    u21 = math.sin(theta/2) * cmath.exp(-1j*(phi-psi)/2) * 1j
    u22 = math.cos(theta/2) * cmath.exp(-1j*(phi+psi)/2)

    U = np.array([[u11, u12], [u21, u22]], dtype=complex)
    # Verify U ∈ SU(2): det(U) = 1
    det_U = np.linalg.det(U)

    # Random Hermitian traceless 2×2 matrix (Lie algebra element)
    hx, hy, hz = rng.normal(0, 0.3), rng.normal(0, 0.3), rng.normal(0, 0.3)
    H_alg = hx*sigma_1 + hy*sigma_2 + hz*sigma_3
    # exp(H_alg) has det = exp(Tr(H_alg)) = exp(0) = 1
    # Compute matrix exponential
    Lambda = linalg.expm(H_alg)
    Lambda_det = np.linalg.det(Lambda)

    results['SL2C_det'] = float(Lambda_det.real)
    results['SL2C_det_equals_1'] = abs(float(Lambda_det.real) - 1.0) < 1e-10

    # Transform X under the Lorentz action: X → Λ X Λ†
    X_transformed = Lambda @ X @ Lambda.conj().T
    det_transformed = np.linalg.det(X_transformed)

    results['det(ΛXΛ†)'] = float(det_transformed.real)
    results['invariance'] = abs(float(det_transformed.real) - Q) < 1e-10

    # ── Matrix nilpotency is not a spacetime mass-shell identification ──
    det_Sp = np.linalg.det(S_plus)
    results['det(S₊) = 0'] = abs(complex(det_Sp)) < 1e-10
    results['S₊ operator status'] = (
        'S₊ is a square-zero 2×2 ladder matrix; no momentum-space identification is asserted.'
    )

    # Any purely off-diagonal matrix has det = −(off_diag_product)
    # For M = a·S₊ + b·S₋ = [[0, a], [b, 0]], det(M) = −a·b
    # This is generally non-zero (unless a=0 or b=0)
    # So "any off-diagonal" is NOT automatically on the light cone.
    # Only nilpotent off-diagonals (a=0 OR b=0) have det=0.
    a_off, b_off = 1.0 + 0.5j, -0.3 + 0.8j
    M_off = a_off * S_plus + b_off * S_minus
    det_off = np.linalg.det(M_off)
    results['det([0,a;b,0]) = −ab'] = abs(complex(det_off) + a_off*b_off) < 1e-10
    results['operator determinant distinction'] = (
        'The mixed off-diagonal determinant is −ab. Interpreting either determinant '
        'as physical mass requires a separately specified soldering map.'
    )

    results['all_invariance_verified'] = (
        results['det(X) = Q'] and results['invariance'] and
        results['det(S₊) = 0'] and results['det([0,a;b,0]) = −ab']
    )

    return results


# ══════════════════════════════════════════════════════════════════════════════
# Part 4:  Rank-two Hermitian determinant carriers
# ══════════════════════════════════════════════════════════════════════════════

def rank_two_determinant_carrier_dimensions() -> Dict:
    """
    Reference dimension metadata for determinant quadratic carriers on
    rank-two Hermitian matrices. This function does not construct a Jordan
    product, a TKK algebra, or an isomorphism with any Lie algebra.
    """

    # Reference dimensions for Lorentz algebras attached to determinant
    # quadratic carriers. These entries are not a TKK classification proof.
    carriers = {
        'R': {'algebra': 'H_2(R)', 'dim_Jordan': 3, 'LorentzAlgebra': 'so(1,2)',
              'dimLorentz': 3, 'spacetime_dim': 3, 'signature': '(1,2)'},
        'C': {'algebra': 'H_2(C)', 'dim_Jordan': 4, 'LorentzAlgebra': 'so(1,3) ≅ sl(2,C)_R',
              'dimLorentz': 6, 'spacetime_dim': 4, 'signature': '(1,3)'},
        'H': {'algebra': 'H_2(H)', 'dim_Jordan': 6, 'LorentzAlgebra': 'so(1,5)',
              'dimLorentz': 15, 'spacetime_dim': 6, 'signature': '(1,5)'},
        'O': {'algebra': 'H_2(O)', 'dim_Jordan': 10, 'LorentzAlgebra': 'so(1,9)',
              'dimLorentz': 45, 'spacetime_dim': 10, 'signature': '(1,9)'},
    }

    return {
        'carriers': carriers,
        'our_entry': 'C (complex numbers): Herm₂(C) determinant gives a 4D Lorentz quadratic carrier',
        'key_insight': (
            'The determinant on 2×2 Hermitian complex matrices is the '
            'Minkowski quadratic form; SL(2,C) acts by determinant-preserving '
            'congruence. This routine checks matrix identities, not a TKK theorem.'
        ),
        'octonion_note': (
            'The 10-dimensional Lorentz carrier is a dimension count only; '
            'it does not derive the critical dimension of string theory.'
        ),
    }


# ══════════════════════════════════════════════════════════════════════════════
# Part 5:  Independent Pauli determinant sample
# ══════════════════════════════════════════════════════════════════════════════

def sample_pauli_determinant_identity() -> Dict:
    """Evaluate det(X)=t²−x²−y²−z² on one Hermitian 2×2 matrix.

    This remains an independent finite sample; it does not identify the
    chiral ladder span with the four-real-dimensional Hermitian carrier.
    """
    t, x, y, z = 1.5, 0.7, -0.4, 0.9
    determinant = float(np.linalg.det(spacetime_matrix(t, x, y, z)).real)
    quadratic_form = minkowski_metric(t, x, y, z)

    return {
        'coordinates': (t, x, y, z),
        'determinant': determinant,
        'quadratic_form': quadratic_form,
        'identity_holds_at_sample': abs(determinant - quadratic_form) < 1e-10,
    }


# ══════════════════════════════════════════════════════════════════════════════
# Part 7:  Run All
# ══════════════════════════════════════════════════════════════════════════════

def run_all(show_plots: bool = False):
    """Run finite matrix samples; these are not a TKK proof."""

    print("=" * 72)
    print("  Chiral Matrix Diagnostics — finite algebraic samples")
    print("  No five-grading or TKK-to-spacetime construction is asserted")
    print("=" * 72)

    # ── Adjoint-weight identities ───────────────────────────────
    print("\n" + "─" * 72)
    print("  Part 1: Adjoint weights of selected matrix units")
    print("─" * 72)

    grading = verify_grading()
    print(f"\n  Weight operator h = E₁₁ − E₂₂ = σ₃ = diag(1,−1)")
    for key, val in grading.items():
        if key != 'all_matrix_weight_identities_hold':
            status = "✓" if val else "✗"
            print(f"    {status}  {key}")
    print(f"\n  All displayed matrix identities hold: {grading['all_matrix_weight_identities_hold']}")

    # ── Triple System ───────────────────────────────────────────
    print("\n" + "─" * 72)
    print("  Part 2: Sampled Hermitian triple-product values")
    print("─" * 72)

    triple = verify_triple_system()
    for key, val in triple.items():
        if key != 'all_sampled_triple_identities_hold':
            status = "✓" if val else "✗"
            print(f"    {status}  {key}")
    print(f"\n  All sampled values match: {triple['all_sampled_triple_identities_hold']}")

    # ── Structure Algebra ────────────────────────────────────────
    print("\n" + "─" * 72)
    print("  Part 3: Left-triple-operator samples")
    print("─" * 72)

    g0 = triple_left_operator_samples()
    for key, val in g0.items():
        if isinstance(val, np.ndarray):
            print(f"    {key} = {val}")
        else:
            print(f"    {key}: {val}")

    # ── Invariant Quadratic Form ─────────────────────────────────
    print("\n" + "─" * 72)
    print("  Part 4: Pauli determinant sample = Minkowski quadratic form")
    print("─" * 72)

    inv = verify_invariant_quadratic_form()
    print(f"\n  Q(t,x,y,z) = t² − x² − y² − z²")
    print(f"  Test point: (t,x,y,z) = (2.0, 0.5, −0.3, 1.2)")
    print(f"    det(X) = {inv['det(X)']:.6f}")
    print(f"    Q      = {inv['Q(t,x,y,z)']:.6f}")
    print(f"    det = Q: {inv['det(X) = Q']}")
    print(f"\n  SL(2,ℂ) invariance:")
    print(f"    det(Λ) = {inv['SL2C_det']:.6f} = 1: {inv['SL2C_det_equals_1']}")
    print(f"    det(ΛXΛ†) = {inv['det(ΛXΛ†)']:.6f} = Q: {inv['invariance']}")
    print(f"\n  Nilpotent structure:")
    print(f"    det(S₊) = 0: {inv['det(S₊) = 0']}")
    print(f"    {inv['S₊ operator status']}")
    print(f"    det([0,a;b,0]) = −ab: {inv['det([0,a;b,0]) = −ab']}")
    print(f"    {inv['operator determinant distinction']}")

    # ── Determinant carrier dimension reference data ─────────────
    print("\n" + "─" * 72)
    print("  Part 5: Lorentz algebras associated with determinant carriers (reference dimensions)")
    print("─" * 72)

    carriers = rank_two_determinant_carrier_dimensions()
    print(f"\n  H₂(𝔸) determinant carriers (dimension data, not a TKK classification):")
    for div_alg in ['R', 'C', 'H', 'O']:
        entry = carriers['carriers'][div_alg]
        print(f"    𝔸 = {div_alg}: {entry['algebra']} ({entry['dim_Jordan']}D carrier)"
              f" → {entry['LorentzAlgebra']} (dim {entry['dimLorentz']})")
        print(f"      Carrier dimension: {entry['spacetime_dim']}D, signature {entry['signature']}")
    print(f"\n  Complex entry: {carriers['our_entry']}")
    print(f"  {carriers['key_insight']}")
    print(f"\n  {carriers['octonion_note']}")

    # ── Independent Pauli determinant sample ─────────────────────
    print("\n" + "─" * 72)
    print("  Part 6: Independent Pauli determinant sample")
    print("─" * 72)

    sample = sample_pauli_determinant_identity()
    print(f"\n  Coordinates (t,x,y,z): {sample['coordinates']}")
    print(f"  det(X) = {sample['determinant']:.6f}")
    print(f"  Q       = {sample['quadratic_form']:.6f}")
    print(f"  Identity holds at this sample: {sample['identity_holds_at_sample']}")

    # ── Summary ──────────────────────────────────────────────────
    print("\n" + "=" * 72)
    print("  Verified scope and open structural comparison")
    print("=" * 72)
    print("""
    Felix Klein (1872) — Erlangen Program:
      Geometry = a set of points + a group of transformations.
      Invariants of the group action define the geometric properties.

    The present script checks selected finite-dimensional matrix identities.
    It does not establish a general Erlangen/TKK completion theorem.

    In this Mat₂(ℂ) representation, h has three adjoint-weight spaces:
    weight −2: span{S₋}; weight 0: span{N₊,N₋}; weight +2: span{S₊}.
    This does not supply additional nonzero outer components of a five-grading.

    This numerical model evaluates Q on a four-component carrier and checks
    agreement with a 2×2 Hermitian determinant. It does not prove that an
    arbitrary TKK construction forces a unique such form:

      Q(t, x, y, z) = t² − x² − y² − z²

    This is the Minkowski quadratic form in the chosen coordinates. Its zero
    locus is the light cone. Nilpotency of the separate ladder matrices S₊,
    S₋ does not identify them with points of this cone; that requires a
    separately defined map and a proved compatibility theorem.

    Open comparison: relating a separately defined triple-system/TKK
    construction to the Hermitian determinant carrier requires an explicit
    carrier map and a proved compatibility theorem. The calculations above
    establish only the finite matrix and quadratic identities actually tested.
    """)


# ══════════════════════════════════════════════════════════════════════
# Main
# ══════════════════════════════════════════════════════════════════════

if __name__ == '__main__':
    run_all()
