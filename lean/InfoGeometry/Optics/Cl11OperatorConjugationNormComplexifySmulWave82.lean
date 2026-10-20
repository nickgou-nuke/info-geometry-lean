/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Optics.Cl11OperatorConjugationNorm

noncomputable section

namespace InfoGeometry.Optics.Cl11OperatorConjugationNorm

open InfoGeometry.Optics.OperatorBogoliubovPauliBridge

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Entrywise scalar extension intertwines real matrix scaling with the
corresponding complex scalar action on the operator-valued matrix carrier. -/
theorem complexifyMatrix_smul
    (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    complexifyMatrix (W := W) (r • A) =
      (r : ℂ) • complexifyMatrix (W := W) A := by
  ext i j
  simp [complexifyMatrix, Matrix.smul_apply, smul_eq_mul]
  exact smul_comm (A i j) r _

end InfoGeometry.Optics.Cl11OperatorConjugationNorm
