/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Optics.Cl11OperatorConjugationNorm
import InfoGeometry.Optics.Cl11OperatorConjugationNormComplexifySmulWave82

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Optics.Cl11OperatorConjugationNorm

open InfoGeometry.Algebra.SplitQuaternionMatrices
open InfoGeometry.Clifford.Cl11CoordinateAlgebra
open InfoGeometry.Optics.OperatorBogoliubovPauliBridge
open InfoGeometry.Optics.OperatorLiftCarrier
open InfoGeometry.Optics.Cl11SplitQuaternionQGTSoldering

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The doubled-carrier representation intertwines real scalar multiplication
of `Cl(1,1)` coordinates with complex scalar multiplication of endomorphisms. -/
theorem operatorCl11_real_smul (r : ℝ) (q : Cl11) :
    operatorCl11 (W := W) (r • q) =
      (r : ℂ) • operatorCl11 (W := W) q := by
  unfold operatorCl11
  have hmatrix :
      cl11SplitQuaternionMatrix (r • q) =
        r • cl11SplitQuaternionMatrix q := by
    unfold cl11SplitQuaternionMatrix
    change splitQ (r * q.s) (r * q.e2) (r * q.e1) (-(r * q.e12)) =
      r • splitQ q.s q.e2 q.e1 (-q.e12)
    simp [splitQ, smul_add, smul_smul]
  rw [hmatrix, complexifyMatrix_smul, matrixAction_smul]

end InfoGeometry.Optics.Cl11OperatorConjugationNorm
#print axioms InfoGeometry.Optics.Cl11OperatorConjugationNorm.operatorCl11_real_smul
