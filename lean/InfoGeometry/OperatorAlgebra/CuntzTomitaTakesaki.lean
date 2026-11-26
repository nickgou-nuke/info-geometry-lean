/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy

/-!
# 2×2 Complex Matrix Hyperbolic-Weight Cancellation Shadow

This module verifies an elementary `2×2` complex matrix entry-scaling identity:
multiplying off-diagonal entries by `exp(-δ)` / `exp(δ)` inside `delta_half`,
taking `conjTranspose`, and multiplying by the reciprocal real weights inside
`J_conjugation` cancels via `exp(δ) * exp(-δ) = 1`, leaving `X.conjTranspose`.

No Cuntz algebra `O_n`, generating isometries, GNS vacuum, or full Tomita-Takesaki
theory is constructed here. For constructive finite/colimit polar decompositions and
Cuntz GNS colimit towers, see `InfoGeometry.Canonical.FiniteMatrixTomitaPolar` and
`InfoGeometry.Canonical.CuntzGNSFilteredTomitaColimit`.
-/

namespace InfoGeometry.OperatorAlgebra

open scoped Matrix

/-- Scales the off-diagonal entries of a `2×2` complex matrix by `exp(-δ)` and `exp(δ)`. -/
noncomputable def delta_half (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![X 0 0, X 0 1 * (Real.exp (-δ) : ℂ)], 
    ![X 1 0 * (Real.exp δ : ℂ), X 1 1]]

/-- Takes `X.conjTranspose` and scales its off-diagonal entries by `exp(-δ)` and `exp(δ)`. -/
noncomputable def J_conjugation (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let X_star := X.conjTranspose
  ![![X_star 0 0, X_star 0 1 * (Real.exp (-δ) : ℂ)], 
    ![X_star 1 0 * (Real.exp δ : ℂ), X_star 1 1]]

/-- Composition `J_conjugation δ (delta_half δ X)` on `2×2` complex matrices. -/
noncomputable def S_tomita (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  J_conjugation δ (delta_half δ X)

/-- Weight-cancellation identity: `S_tomita δ X = X.conjTranspose` from `exp(δ) * exp(-δ) = 1`. -/
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
