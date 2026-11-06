/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ResolventTransform
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Native Fréchet derivative of the ordered resolvent transform

For a real Banach algebra, the resolvent transform is differentiable wherever
`1 - A * C` is a unit. Its derivative acts on every direction in the full
algebra by left multiplication with the forward resolvent and right
multiplication with the reverse resolvent.
-/

noncomputable section

namespace InfoGeometry.Analysis.ResolventTransformDifferential

open InfoGeometry.OperatorAlgebra.ResolventTransform

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

/-- The actual Fréchet derivative on a noncommutative real Banach algebra. -/
theorem hasFDerivAt_eta (C A : B) (hA : IsUnit (1 - A * C)) :
    HasFDerivAt (eta C)
      (ContinuousLinearMap.mulLeftRight ℝ B
        (Ring.inverse (1 - A * C)) (Ring.inverse (1 - C * A))) A := by
  let rightC : B →L[ℝ] B := (ContinuousLinearMap.mul ℝ B).flip C
  have hinner : HasFDerivAt (fun X : B => 1 - X * C) (-rightC) A := by
    exact rightC.hasFDerivAt.const_sub (1 : B)
  have hinv : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ B
        (Ring.inverse (1 - A * C)) (Ring.inverse (1 - A * C))) (1 - A * C) := by
    simpa only [IsUnit.unit_spec, Ring.inverse_of_isUnit hA] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) hA.unit)
  have hmul := (hinv.comp A hinner).mul' (hasFDerivAt_id (𝕜 := ℝ) A)
  apply hmul.congr_fderiv
  ext H
  change Ring.inverse (1 - A * C) * H +
      (-(Ring.inverse (1 - A * C) * (-(H * C)) * Ring.inverse (1 - A * C))) * A =
    Ring.inverse (1 - A * C) * H * Ring.inverse (1 - C * A)
  rw [inverse_one_sub_mul_reverse A C hA]
  noncomm_ring

/-- Evaluation of the native derivative in an arbitrary operator direction. -/
theorem fderiv_eta_apply (C A H : B) (hA : IsUnit (1 - A * C)) :
    fderiv ℝ (eta C) A H =
      Ring.inverse (1 - A * C) * H * Ring.inverse (1 - C * A) := by
  rw [(hasFDerivAt_eta C A hA).fderiv]
  rfl

end InfoGeometry.Analysis.ResolventTransformDifferential
