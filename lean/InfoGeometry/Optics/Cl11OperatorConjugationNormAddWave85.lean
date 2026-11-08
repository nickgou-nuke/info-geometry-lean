/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Optics.Cl11OperatorConjugationNorm
import InfoGeometry.Optics.Cl11QuaternionTwistedConjugationBridge

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Optics.Cl11OperatorConjugationNorm

open InfoGeometry.Clifford.Cl11CoordinateAlgebra
open InfoGeometry.Optics.OperatorBogoliubovPauliBridge
open InfoGeometry.Optics.OperatorLiftCarrier
open InfoGeometry.Optics.Cl11SplitQuaternionQGTSoldering
open InfoGeometry.Optics.Cl11QuaternionTwistedConjugationBridge

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The doubled-carrier representation is additive in the `Cl(1,1)` coordinate.
This supplies the additive half of the operator representation law alongside
its existing multiplicative theorem. -/
theorem operatorCl11_add (q r : Cl11) :
    operatorCl11 (W := W) (q + r) =
      operatorCl11 (W := W) q + operatorCl11 (W := W) r := by
  unfold operatorCl11
  rw [cl11SplitQuaternionMatrix_add]
  have hcomplex :
      complexifyMatrix (W := W)
          (cl11SplitQuaternionMatrix q + cl11SplitQuaternionMatrix r) =
        complexifyMatrix (W := W) (cl11SplitQuaternionMatrix q) +
          complexifyMatrix (W := W) (cl11SplitQuaternionMatrix r) := by
    ext i j
    simp [complexifyMatrix]
  rw [hcomplex, matrixAction_add]

end InfoGeometry.Optics.Cl11OperatorConjugationNorm
#print axioms InfoGeometry.Optics.Cl11OperatorConjugationNorm.operatorCl11_add
