/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Orientation
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.Orientation
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.InnerDerivationSpectra

/-!
# Dictionary: Peirce spine ↔ existing operator-algebra owners

The spine's elementwise vocabulary is identified with the owner layer:

* corners: `conePlus P A = component10 P A`, `coneMinus P C = component01 P C`
  (`Core.PeirceDecomposition`);
* grading: `invS P = reflection P = 2 • P - 1` (`Core.IdempotentCartan`);
* graded derivations: `superDerivPlus`/`superDerivPlusBar` are the pointwise
  values of `gradedDeriv`/`gradedCodiff` in `Module.End ℤ B`
  (`SquareZeroPairSpectral.Orientation`);
* Laplacians: `derivSqPhi`, `derivSqJ`, `derivSqSig` are the pointwise values of
  `phiLaplacian`, `jLaplacian`, `spinLaplacian` (`SquareZeroPairSpectral`).

Every ring is a `ℤ`-algebra, so the spine's ring `B` is used with `R = ℤ`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.OperatorAlgebra.LieJordan
open InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral

variable {B : Type*} [Ring B]

theorem conePlus_eq_component10 (P A : B) : conePlus P A = component10 P A := rfl

theorem coneMinus_eq_component01 (P C : B) : coneMinus P C = component01 P C := rfl

theorem invS_eq_reflection (P : B) : invS P = InfoGeometry.Core.IdempotentCartan.reflection P := by
  simp only [invS, InfoGeometry.Core.IdempotentCartan.reflection, two_nsmul]
  abel

/-- The spine `⋆` is the owner `hodgeStar` evaluated pointwise. -/
theorem hodgeStar_eq_owner (P X : B) :
    hodgeStar P X = SquareZeroPairSpectral.hodgeStar ℤ P X := by
  rw [SquareZeroPairSpectral.hodgeStar_apply, ← invS_eq_reflection]; rfl

theorem superDerivPlus_eq_gradedDeriv (P A X : B) :
    superDerivPlus P A X = gradedDeriv ℤ (invS P) (conePlus P A) X := by
  simp only [superDerivPlus, parityConj, gradedDeriv_apply, mul_assoc]

theorem superDerivMinus_eq_gradedDeriv (P C X : B) :
    superDerivMinus P C X = gradedDeriv ℤ (invS P) (coneMinus P C) X := by
  simp only [superDerivMinus, parityConj, gradedDeriv_apply, mul_assoc]

theorem superDerivPlusBar_eq_gradedCodiff (P A X : B) :
    superDerivPlusBar P A X = gradedCodiff ℤ (invS P) (conePlus P A) X := by
  simp only [superDerivPlusBar, parityConj, gradedCodiff_apply, mul_assoc]

theorem superDerivMinusBar_eq_gradedCodiff (P C X : B) :
    superDerivMinusBar P C X = gradedCodiff ℤ (invS P) (coneMinus P C) X := by
  simp only [superDerivMinusBar, parityConj, gradedCodiff_apply, mul_assoc]

theorem derivSqPhi_eq_phiLaplacian (P A C X : B) :
    derivSqPhi P A C X = phiLaplacian ℤ (conePlus P A) (coneMinus P C) X := by
  simp only [derivSqPhi, phiLaplacian, LinearMap.neg_apply, Module.End.mul_apply, lieOp_apply,
    comm, genPhi]

theorem derivSqJ_eq_jLaplacian (P A C X : B) :
    derivSqJ P A C X = jLaplacian ℤ (conePlus P A) (coneMinus P C) X := by
  simp only [derivSqJ, jLaplacian, Module.End.mul_apply, lieOp_apply, comm, genJ]

end InfoGeometry.OperatorAlgebra.PeirceSpine
