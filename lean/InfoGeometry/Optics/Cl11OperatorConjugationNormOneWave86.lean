/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Optics.Cl11OperatorConjugationNorm

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Optics.Cl11OperatorConjugationNorm

open InfoGeometry.Algebra.SplitQuaternionMatrices
open InfoGeometry.Clifford.Cl11CoordinateAlgebra
open InfoGeometry.Optics.OperatorBogoliubovPauliBridge
open InfoGeometry.Optics.OperatorLiftCarrier
open InfoGeometry.Optics.Cl11SplitQuaternionQGTSoldering

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The doubled-carrier representation is unital: the coordinate unit acts as
 the identity endomorphism on the two-sheet carrier. -/
theorem operatorCl11_one :
    operatorCl11 (W := W) (1 : Cl11) = 1 := by
  unfold operatorCl11
  have hone : (1 : Cl11) = scalarEmbed 1 := by rfl
  have hmatrix :
      cl11SplitQuaternionMatrix (scalarEmbed 1) =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    unfold cl11SplitQuaternionMatrix scalarEmbed
    rw [splitQ_eq_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]
  rw [hone, hmatrix, complexifyMatrix_one, matrixAction_one_end]

end InfoGeometry.Optics.Cl11OperatorConjugationNorm
#print axioms InfoGeometry.Optics.Cl11OperatorConjugationNorm.operatorCl11_one
