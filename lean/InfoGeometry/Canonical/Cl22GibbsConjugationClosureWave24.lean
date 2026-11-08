/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

noncomputable section

open scoped MatrixOrder ComplexOrder
open Matrix
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

namespace InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

/-- A finite Gibbs functional is invariant under inner conjugation by a
right-inverse pair whose left factor commutes with the Hamiltonian. -/
theorem gibbsFunctional_rightInverse_conjugation_invariant_of_commute
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ)
    (U V X : Matrix n n ℂ)
    (hVU : V * U = 1)
    (hHU : Commute H U) :
    gibbsFunctional H hH β (U * X * V) =
      gibbsFunctional H hH β X := by
  rw [gibbsFunctional_apply, gibbsFunctional_apply]
  congr 1
  let D := gibbsDensity H hH β
  have hDU : Commute D U := by
    unfold D gibbsDensity
    rw [← hH.cfc_eq]
    have hsa : IsSelfAdjoint H := hH
    exact hsa.commute_cfc hHU (expWeight β)
  calc
    Matrix.trace (D * (U * X * V)) =
        Matrix.trace (U * (D * X * V)) := by
      rw [show D * (U * X * V) = (D * U) * X * V by simp [mul_assoc], hDU.eq]
      simp only [mul_assoc]
    _ = Matrix.trace ((D * X * V) * U) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (D * X) := by
      rw [mul_assoc, hVU, mul_one]

end InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
