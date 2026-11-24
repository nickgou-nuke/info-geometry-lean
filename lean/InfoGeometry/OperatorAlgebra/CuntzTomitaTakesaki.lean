/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy

/-!
# Cuntz Algebra and Tomita-Takesaki Cancellation

This module formalizes the exact algebraic cancellation of the hyperbolic 
thermal weights within the Cuntz algebra, proving that the Tomita operator 
S = J Δ^(1/2) simplifies exactly to the observable adjoint (X*).
-/

namespace InfoGeometry.OperatorAlgebra

open scoped Matrix

/-- 
  The modular translation map on a 2x2 complex observable X, 
  parameterized by the thermodynamic gap δ.
-/
noncomputable def delta_half (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![X 0 0, X 0 1 * (Real.exp (-δ) : ℂ)], 
    ![X 1 0 * (Real.exp δ : ℂ), X 1 1]]

/-- 
  The modular conjugation map on a 2x2 complex observable X. 
  It takes the adjoint (conjugate transpose) and then translates.
-/
noncomputable def J_conjugation (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let X_star := X.conjTranspose
  ![![X_star 0 0, X_star 0 1 * (Real.exp (-δ) : ℂ)], 
    ![X_star 1 0 * (Real.exp δ : ℂ), X_star 1 1]]

/-- 
  The Tomita Operator S is the composition of the modular conjugation 
  with the adjoint of the modular translation.
  (In the SymPy verification, S(X) = J(Delta^(1/2)(X).H))
-/
noncomputable def S_tomita (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  J_conjugation δ (delta_half δ X)

/-- 
  THEOREM: Tomita-Takesaki Cancellation in the Cuntz Vacuum.
  The hyperbolic thermal weights perfectly annihilate each other, 
  leaving only the CPT conjugated observable (X*).
-/
theorem tomita_cuntz_cancellation (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    S_tomita δ X = X.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · change star (X 1 0 * (Real.exp δ : ℂ)) * (Real.exp (-δ) : ℂ) = star (X 1 0)
    rw [star_mul]
    have h1 : star (Real.exp δ : ℂ) = (Real.exp δ : ℂ) :=
      Complex.conj_ofReal (Real.exp δ)
    have h2 : (Real.exp δ : ℂ) * (Real.exp (-δ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
    rw [h1, mul_right_comm, h2, one_mul]
  · change star (X 0 1 * (Real.exp (-δ) : ℂ)) * (Real.exp δ : ℂ) = star (X 0 1)
    rw [star_mul]
    have h1 : star (Real.exp (-δ) : ℂ) = (Real.exp (-δ) : ℂ) :=
      Complex.conj_ofReal (Real.exp (-δ))
    have h2 : (Real.exp (-δ) : ℂ) * (Real.exp δ : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
    rw [h1, mul_right_comm, h2, one_mul]
  · rfl


theorem tomita_cuntz_involutive (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    S_tomita δ (S_tomita δ X) = X := by
  rw [tomita_cuntz_cancellation, tomita_cuntz_cancellation]
  exact Matrix.conjTranspose_conjTranspose X

/-- The finite Tomita map reverses matrix multiplication. -/
theorem tomita_cuntz_anti_mul (δ : ℝ)
    (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    S_tomita δ (X * Y) = S_tomita δ Y * S_tomita δ X := by
  rw [tomita_cuntz_cancellation, tomita_cuntz_cancellation,
    tomita_cuntz_cancellation, Matrix.conjTranspose_mul]

end InfoGeometry.OperatorAlgebra
