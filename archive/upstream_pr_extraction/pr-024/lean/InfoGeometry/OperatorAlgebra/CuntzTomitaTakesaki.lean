import Mathlib
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
  dsimp [S_tomita, J_conjugation, delta_half, Matrix.conjTranspose]
  ext i j
  have h_exp : (starRingEnd ℂ) (Complex.exp ↑δ) = Complex.exp ↑δ := by
    rw [← Complex.ofReal_exp]
    exact Complex.conj_ofReal (Real.exp δ)
  have h_exp_neg : (starRingEnd ℂ) (Complex.exp (-↑δ)) = Complex.exp (-↑δ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
    exact Complex.conj_ofReal (Real.exp (-δ))
  fin_cases i <;> fin_cases j
  · simp
  · simp
    rw [h_exp, mul_assoc, ← Complex.exp_add, add_neg_cancel (↑δ : ℂ), Complex.exp_zero, mul_one]
  · simp
    rw [h_exp_neg, mul_assoc, ← Complex.exp_add, neg_add_cancel (↑δ : ℂ), Complex.exp_zero, mul_one]
  · simp

end InfoGeometry.OperatorAlgebra
