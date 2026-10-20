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

/-- Entrywise scalar extension preserves addition of real matrices on the
doubled operator carrier. -/
@[simp] theorem complexifyMatrix_add
    (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    complexifyMatrix (W := W) (A + B) =
      complexifyMatrix (W := W) A + complexifyMatrix (W := W) B := by
  ext i j
  simp [complexifyMatrix, Matrix.add_apply]

end InfoGeometry.Optics.Cl11OperatorConjugationNorm
