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

/-- Products of opposite spine arrows land in the two diagonal Peirce corners.

This records the compositional content of the identification with the core
`component10` and `component01` maps: an upper arrow followed by a lower arrow
returns to the `11` corner, while the reverse path returns to the `00` corner.
No commutativity of `B` is assumed. -/
theorem spine_mixed_products_route_to_diagonal_corners (P A C : B)
    (hP : P * P = P) :
    conePlus P A * coneMinus P C =
      component11 P (conePlus P A * coneMinus P C) ∧
    coneMinus P C * conePlus P A =
      component00 P (coneMinus P C * conePlus P A) := by
  constructor
  · change P * A * (1 - P) * ((1 - P) * C * P) =
      P * (P * A * (1 - P) * ((1 - P) * C * P)) * P
    let u := conePlus P A
    let v := coneMinus P C
    have hu : P * u = u := P_mul_conePlus hP A
    have hv : v * P = v := coneMinus_mul_P hP C
    have hleft : P * (u * v) = u * v := by
      calc
        P * (u * v) = (P * u) * v := (mul_assoc P u v).symm
        _ = u * v := by rw [hu]
    have hright : (u * v) * P = u * v := by
      calc
        (u * v) * P = u * (v * P) := mul_assoc u v P
        _ = u * v := by rw [hv]
    change u * v = P * (u * v) * P
    rw [hleft, hright]
  · change (1 - P) * C * P * (P * A * (1 - P)) =
      (1 - P) * ((1 - P) * C * P * (P * A * (1 - P))) * (1 - P)
    let u := conePlus P A
    let v := coneMinus P C
    have hq : (1 - P) * (1 - P) = 1 - P := by
      noncomm_ring [hP]
    have hleft : (1 - P) * v = v := by
      dsimp [v, coneMinus]
      calc
        (1 - P) * (((1 - P) * C) * P) = ((1 - P) * ((1 - P) * C)) * P :=
          (mul_assoc (1 - P) ((1 - P) * C) P).symm
        _ = (((1 - P) * (1 - P)) * C) * P := by rw [mul_assoc (1 - P) (1 - P) C]
        _ = ((1 - P) * C) * P := by rw [hq]
    have hright : u * (1 - P) = u := by
      dsimp [u, conePlus]
      calc
        (P * A * (1 - P)) * (1 - P) = (P * A) * ((1 - P) * (1 - P)) :=
          mul_assoc (P * A) (1 - P) (1 - P)
        _ = P * A * (1 - P) := by rw [hq]
    have hleft' : (1 - P) * (v * u) = v * u := by
      calc
        (1 - P) * (v * u) = ((1 - P) * v) * u := (mul_assoc (1 - P) v u).symm
        _ = v * u := by rw [hleft]
    have hright' : (v * u) * (1 - P) = v * u := by
      calc
        (v * u) * (1 - P) = v * (u * (1 - P)) := mul_assoc v u (1 - P)
        _ = v * u := by rw [hright]
    change v * u = (1 - P) * (v * u) * (1 - P)
    rw [hleft', hright']

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
