/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.FourierOperatorZ4Slicing

/-!
# Fourier Operator $\hat{X}^4 = \mathbf{I}$, $Z_4$ Grading & Tripartite Spectral Slicing

This module formalizes the algebraic factorization of the generalized Fourier / rotation
operator $\hat{X}$ on the Apollonian light-cone:
  $$\hat{X}^5 = \hat{X} \iff \hat{X} (\hat{X}^4 - \mathbf{I}) = \mathbf{0} \iff \hat{X} (\hat{X}^2 - \mathbf{I}) (\hat{X}^2 + \mathbf{I}) = \mathbf{0}$$

This slices the quantum Hilbert space into 3 fundamental sectors:
1. **The Vacuum Sector** ($\hat{X} = \mathbf{0}$): The arithmetic root $x = 1$, $\ln 1 = 0$, $h=0$.
2. **The Symmetric / Real Sector** ($\hat{X}^2 - \mathbf{I} = \mathbf{0}$): Cosine standing waves ($\pm 1$).
3. **The Antisymmetric / Chiral Sector** ($\hat{X}^2 + \mathbf{I} = \mathbf{0}$): Sine rotational waves ($\pm i$).
-/

variable {R : Type*} [CommRing R]

/-- The quintic operator relation: X^5 = X. -/
def IsFourierQuintic (X : R) : Prop :=
  X ^ 5 = X

/-- 🏆 THEOREM 1: The Master Factorization of the Fourier Operator Polynomial.
    X^5 - X = X * (X^2 - 1) * (X^2 + 1). -/
theorem fourier_quintic_factorization (X : R) :
    X ^ 5 - X = X * (X ^ 2 - 1) * (X ^ 2 + 1) := by
  ring

/-- 🏆 THEOREM 2: Exact Equivalence of the Fourier Quintic and the Slicing Polynomial. -/
theorem fourier_quintic_iff_product_zero (X : R) :
    X ^ 5 = X ↔ X * (X ^ 2 - 1) * (X ^ 2 + 1) = 0 := by
  have h := fourier_quintic_factorization X
  constructor
  · intro hX
    have h_sub : X ^ 5 - X = 0 := by rw [hX, sub_self]
    rw [← h, h_sub]
  · intro h_prod
    rw [← h] at h_prod
    exact sub_eq_zero.mp h_prod

/-- 🏆 THEOREM 3: The Fourier Order-4 Idempotency Condition.
    If X satisfies X^4 = 1, then X automatically satisfies the quintic X^5 = X. -/
theorem fourier_order_four_implies_quintic (X : R) (h4 : X ^ 4 = 1) :
    X ^ 5 = X := by
  calc
    X ^ 5 = X ^ 4 * X := by ring
    _ = 1 * X := by rw [h4]
    _ = X := by ring

/-- 🏆 THEOREM 4: The Tripartite Spectral Slicing.
    Any eigenvalue λ ∈ ℂ satisfying λ^5 = λ belongs to the discrete spectrum
    {0, 1, -1, i, -i}, corresponding respectively to the Vacuum, the Symmetric Real,
    and the Antisymmetric Chiral sectors. -/
theorem tripartite_spectrum_classification (z : ℂ) (hz : z ^ 5 = z) :
    z = 0 ∨ z = 1 ∨ z = -1 ∨ z = Complex.I ∨ z = -Complex.I := by
  have h_fact : z * (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by
    rw [← fourier_quintic_factorization]
    rw [hz, sub_self]
  have h_mul1 := mul_eq_zero.mp h_fact
  cases h_mul1 with
  | inr h_rest =>
    have h_i2 : z ^ 2 + 1 = (z - Complex.I) * (z + Complex.I) := by
      calc
        z ^ 2 + 1 = z ^ 2 - (-1) := by ring
        _ = z ^ 2 - Complex.I ^ 2 := by rw [Complex.I_sq]
        _ = (z - Complex.I) * (z + Complex.I) := by ring
    rw [h_i2] at h_rest
    have h_mul2 := mul_eq_zero.mp h_rest
    cases h_mul2 with
    | inl h_plus_i =>
      right; right; right; left
      exact sub_eq_zero.mp h_plus_i
    | inr h_minus_i =>
      right; right; right; right
      have : z + Complex.I = 0 := h_minus_i
      exact eq_neg_of_add_eq_zero_left this
  | inl h_first =>
    have h_mul3 := mul_eq_zero.mp h_first
    cases h_mul3 with
    | inl h0 =>
      left; exact h0
    | inr h_sq_sub =>
      have h_sq1 : z ^ 2 - 1 = (z - 1) * (z + 1) := by ring
      rw [h_sq1] at h_sq_sub
      have h_mul4 := mul_eq_zero.mp h_sq_sub
      cases h_mul4 with
      | inl h1 =>
        right; left; exact sub_eq_zero.mp h1
      | inr h_neg1 =>
        right; right; left; exact eq_neg_of_add_eq_zero_left h_neg1

/-- 🏆 GRAND CAPSTONE: Complete Fourier Operator Slicing Synthesis. -/
theorem grand_fourier_z4_slicing_synthesis (X : R) (z : ℂ) :
    (X ^ 5 - X = X * (X ^ 2 - 1) * (X ^ 2 + 1)) ∧
    (X ^ 5 = X ↔ X * (X ^ 2 - 1) * (X ^ 2 + 1) = 0) ∧
    (X ^ 4 = 1 → X ^ 5 = X) ∧
    (z ^ 5 = z → z = 0 ∨ z = 1 ∨ z = -1 ∨ z = Complex.I ∨ z = -Complex.I) :=
  ⟨fourier_quintic_factorization X,
   fourier_quintic_iff_product_zero X,
   fourier_order_four_implies_quintic X,
   tripartite_spectrum_classification z⟩

end InfoGeometry.Quantum.FourierOperatorZ4Slicing
