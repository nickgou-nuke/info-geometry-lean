/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.ExteriorKleinDeterminantCovariance
import InfoGeometry.Projective.ExteriorKleinOperatorExamples

/-!
# Exact boost action on the native exterior square

The formula holds for arbitrary real parameters. Minkowski preservation and
Klein invariance use the explicit normalization `a^2 - b^2 = 1`.
-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorKleinOperatorAction

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge

/-- The `(t,x)` block map with symmetric entries `a,b`. -/
def boost01 (a b : ℝ) : Module.End ℝ Vec4 where
  toFun u i := match i with
    | I4.t => a * u I4.t + b * u I4.x
    | I4.x => b * u I4.t + a * u I4.x
    | I4.y => u I4.y
    | I4.z => u I4.z
  map_add' u v := by
    funext i
    cases i <;> simp only [Pi.add_apply] <;> ring
  map_smul' r u := by
    funext i
    cases i <;> simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

/-- The six-coordinate formula, as a genuine linear endomorphism. -/
def boostBivector01 (a b : ℝ) : Module.End ℝ Bivector4 where
  toFun P := ⟨(a^2 - b^2) * P.p01,
    a * P.p02 + b * P.p12, a * P.p03 + b * P.p13,
    b * P.p02 + a * P.p12, b * P.p03 + a * P.p13, P.p23⟩
  map_add' P Q := by
    apply Bivector4.ext
    · change (a^2 - b^2) * (P.p01 + Q.p01) =
        (a^2 - b^2) * P.p01 + (a^2 - b^2) * Q.p01
      ring
    · change a * (P.p02 + Q.p02) + b * (P.p12 + Q.p12) =
        (a * P.p02 + b * P.p12) + (a * Q.p02 + b * Q.p12)
      ring
    · change a * (P.p03 + Q.p03) + b * (P.p13 + Q.p13) =
        (a * P.p03 + b * P.p13) + (a * Q.p03 + b * Q.p13)
      ring
    · change b * (P.p02 + Q.p02) + a * (P.p12 + Q.p12) =
        (b * P.p02 + a * P.p12) + (b * Q.p02 + a * Q.p12)
      ring
    · change b * (P.p03 + Q.p03) + a * (P.p13 + Q.p13) =
        (b * P.p03 + a * P.p13) + (b * Q.p03 + a * Q.p13)
      ring
    · rfl
  map_smul' r P := by
    apply Bivector4.ext
    · change (a^2 - b^2) * (r * P.p01) = r * ((a^2 - b^2) * P.p01)
      ring
    · change a * (r * P.p02) + b * (r * P.p12) = r * (a * P.p02 + b * P.p12)
      ring
    · change a * (r * P.p03) + b * (r * P.p13) = r * (a * P.p03 + b * P.p13)
      ring
    · change b * (r * P.p02) + a * (r * P.p12) = r * (b * P.p02 + a * P.p12)
      ring
    · change b * (r * P.p03) + a * (r * P.p13) = r * (b * P.p03 + a * P.p13)
      ring
    · rfl

/-- Equality on the entire bivector module, not just on simple wedges. -/
theorem bivectorAction_boost01 (a b : ℝ) :
    bivectorAction (boost01 a b) = boostBivector01 a b := by
  have h : (bivectorAction (boost01 a b)).comp exteriorBivectorLinearEquiv.toLinearMap =
      (boostBivector01 a b).comp exteriorBivectorLinearEquiv.toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    change bivectorAction (boost01 a b)
        (exteriorBivectorLinearEquiv (exteriorPower.ιMulti ℝ 2 v)) =
      boostBivector01 a b (exteriorBivectorLinearEquiv (exteriorPower.ιMulti ℝ 2 v))
    rw [hv, exteriorBivectorLinearEquiv_ιMulti, bivectorAction_wedge]
    apply Bivector4.ext <;> dsimp [boost01, boostBivector01, wedgeVec4] <;> ring
  apply LinearMap.ext
  intro P
  obtain ⟨X, rfl⟩ := exteriorBivectorLinearEquiv.surjective P
  exact congrArg (fun L => L X) h

theorem boost01_det (a b : ℝ) : LinearMap.det (boost01 a b) = a^2 - b^2 := by
  have h := kleinForm_bivectorAction (boost01 a b) ⟨1, 0, 0, 0, 0, 1⟩
  rw [bivectorAction_boost01] at h
  simpa [boostBivector01, kleinForm] using h.symm

theorem boost01_preserves_minkowski (a b : ℝ) (h : a^2 - b^2 = 1) (u v : Vec4) :
    minkowskiDot (boost01 a b u) (boost01 a b v) = minkowskiDot u v := by
  unfold minkowskiDot
  change (a * u I4.t + b * u I4.x) * (a * v I4.t + b * v I4.x) -
      (b * u I4.t + a * u I4.x) * (b * v I4.t + a * v I4.x) -
      u I4.y * v I4.y - u I4.z * v I4.z = _
  calc
    _ = (a^2 - b^2) * (u I4.t * v I4.t - u I4.x * v I4.x) -
        u I4.y * v I4.y - u I4.z * v I4.z := by ring
    _ = _ := by rw [h, one_mul]

theorem boost01_preserves_klein (a b : ℝ) (h : a^2 - b^2 = 1) (P : Bivector4) :
    kleinForm (bivectorAction (boost01 a b) P) = kleinForm P := by
  apply kleinForm_bivectorAction_of_det_one
  rw [boost01_det, h]

theorem boost01_preserves_fourCoordinateSector (a b : ℝ) (P : Bivector4)
    (hP : FourCoordinateSector P) :
    FourCoordinateSector (bivectorAction (boost01 a b) P) := by
  rw [bivectorAction_boost01]
  simp [FourCoordinateSector, boostBivector01, hP.1, hP.2]

end InfoGeometry.Projective.ExteriorKleinOperatorAction
