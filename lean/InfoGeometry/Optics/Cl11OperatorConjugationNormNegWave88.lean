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

/-- The doubled-carrier representation intertwines coordinate negation with
negation of the represented endomorphism. -/
theorem operatorCl11_neg (q : Cl11) :
    operatorCl11 (W := W) (-q) =
      -operatorCl11 (W := W) q := by
  unfold operatorCl11
  have hmatrix :
      cl11SplitQuaternionMatrix (-q) =
        -cl11SplitQuaternionMatrix q := by
    unfold cl11SplitQuaternionMatrix
    change splitQ (-q.s) (-q.e2) (-q.e1) (-(-q.e12)) =
      -splitQ q.s q.e2 q.e1 (-q.e12)
    simp [splitQ, smul_add, smul_smul]
    module
  have hcomplex :
      complexifyMatrix (W := W) (-cl11SplitQuaternionMatrix q) =
        -complexifyMatrix (W := W) (cl11SplitQuaternionMatrix q) := by
    ext i j
    simp [complexifyMatrix]
  rw [hmatrix, hcomplex, matrixAction_neg]

end InfoGeometry.Optics.Cl11OperatorConjugationNorm
#print axioms InfoGeometry.Optics.Cl11OperatorConjugationNorm.operatorCl11_neg
