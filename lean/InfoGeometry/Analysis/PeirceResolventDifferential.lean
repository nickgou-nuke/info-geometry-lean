/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.ResolventTransformDifferential
import InfoGeometry.OperatorAlgebra.PeirceSpine.Resolvent

/-!
# Fréchet derivative in the raw upper Peirce coordinate

The upper coordinate is the continuous linear compression
`X ↦ P * X * (1 - P)`. Composing it with the ordered resolvent transform
gives an actual Fréchet derivative on the full real Banach algebra.

On the unit domain of `1 - genV P A C`, the arbitrary-direction Peirce
sandwich identity expresses this derivative through the full even resolvent.
-/

noncomputable section

namespace InfoGeometry.Analysis.PeirceResolventDifferential

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.ResolventTransform
open InfoGeometry.Analysis.ResolventTransformDifferential

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

/-- The raw upper-coordinate transform has the full even resolvent on both
sides of its Peirce-compressed differential. -/
theorem hasFDerivAt_eta_conePlus {P : B} (hP : P * P = P) (A C : B)
    (hV : IsUnit (1 - genV P A C)) :
    HasFDerivAt (fun X : B => eta (coneMinus P C) (conePlus P X))
      (ContinuousLinearMap.mulLeftRight ℝ B
        (Ring.inverse (1 - genV P A C) * P)
        ((1 - P) * Ring.inverse (1 - genV P A C))) A := by
  let corner : B →L[ℝ] B := ContinuousLinearMap.mulLeftRight ℝ B P (1 - P)
  have hcorner : HasFDerivAt (conePlus P) corner A := by
    exact corner.hasFDerivAt
  have hunit := (isUnit_one_sub_genV_iff hP A C).mp hV
  have h := (hasFDerivAt_eta (coneMinus P C) (conePlus P A) hunit).comp A hcorner
  apply h.congr_fderiv
  ext H
  change Ring.inverse (1 - conePlus P A * coneMinus P C) * conePlus P H *
      Ring.inverse (1 - coneMinus P C * conePlus P A) =
    (Ring.inverse (1 - genV P A C) * P) * H *
      ((1 - P) * Ring.inverse (1 - genV P A C))
  rw [← inverse_one_sub_genV_conePlus_sandwich hP A C H hV]
  simp only [conePlus, mul_assoc]

/-- Evaluation of the native derivative on an arbitrary raw direction. -/
theorem fderiv_eta_conePlus_apply {P : B} (hP : P * P = P) (A C H : B)
    (hV : IsUnit (1 - genV P A C)) :
    fderiv ℝ (fun X : B => eta (coneMinus P C) (conePlus P X)) A H =
      Ring.inverse (1 - genV P A C) * conePlus P H *
        Ring.inverse (1 - genV P A C) := by
  rw [(hasFDerivAt_eta_conePlus hP A C hV).fderiv]
  simp only [ContinuousLinearMap.mulLeftRight_apply, conePlus, mul_assoc]

end InfoGeometry.Analysis.PeirceResolventDifferential
