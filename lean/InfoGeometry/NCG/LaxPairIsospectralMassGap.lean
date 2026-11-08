/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

/-!
# Algebraic trace identities for finite matrix Lax data

This file proves the algebraic trace cancellations associated with a matrix
commutator and the finite-dimensional determinant/kernel criterion. It does
not define a differentiable Lax flow, a spectral-gap quantity, or a Yang–Mills
mass gap. Those require additional analytic and spectral data.
-/

namespace InfoGeometry.NCG.LaxPairIsospectralMassGap

/-- The matrix commutator in the indicated order. -/
def laxCommutator {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := P * L - L * P

/-- The finite matrix trace annihilates commutators. -/
theorem trace_commutator_zero {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (laxCommutator P L) = 0 := by
  rw [laxCommutator, Matrix.trace_sub, Matrix.trace_mul_comm]
  exact sub_self _

/-- The commutator contribution to each cyclic trace-power variation vanishes.
This is an algebraic cancellation identity; it does not assert that a curve
of matrices solves the Lax differential equation. -/
theorem trace_power_commutator_zero {n : ℕ}
    (L P : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    Matrix.trace (L ^ k * laxCommutator P L) = 0 := by
  rw [laxCommutator, mul_sub, Matrix.trace_sub]
  have h₁ : Matrix.trace (L ^ k * (P * L)) =
      Matrix.trace ((L * L ^ k) * P) := by
    calc
      Matrix.trace (L ^ k * (P * L)) =
          Matrix.trace ((L ^ k * P) * L) := by simp [mul_assoc]
      _ = Matrix.trace (L * (L ^ k * P)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((L * L ^ k) * P) := by simp [mul_assoc]
  have h₂ : L * L ^ k = L ^ k * L := by
    rw [← pow_succ', pow_succ]
  calc
    Matrix.trace (L ^ k * (P * L)) - Matrix.trace (L ^ k * (L * P)) =
        Matrix.trace ((L * L ^ k) * P) - Matrix.trace ((L ^ k * L) * P) := by
          rw [h₁]
          simp only [mul_assoc]
    _ = 0 := by rw [h₂]; exact sub_self _

/-- A square complex matrix is singular exactly when its action has a nonzero
kernel vector. This is Mathlib's finite-dimensional determinant criterion. -/
theorem zeroMode_iff_det_zero {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.det L = 0) ↔ ∃ v : (Fin n → ℂ),
      v ≠ 0 ∧ Matrix.mulVec L v = 0 := by
  exact (Matrix.exists_mulVec_eq_zero_iff (M := L)).symm

end InfoGeometry.NCG.LaxPairIsospectralMassGap
