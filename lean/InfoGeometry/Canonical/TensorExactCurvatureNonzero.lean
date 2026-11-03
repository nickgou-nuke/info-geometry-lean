/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorLimitExactConnection
import InfoGeometry.Examples.RealMatrixModeWitness

/-!
# Nonzero exact-connection curvature in the faithful tensor colimit

The existing dense non-diagonal matrix mode and its adjoint yield a nonzero
curvature.  The finite idempotent cut and its mode are reused unchanged; the
colimit conclusion uses the existing faithful stage map.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorExactCurvatureNonzero

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.TensorStageExactConnection
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.RealStarColimitUniversal
open InfoGeometry.Examples.RealMatrixModeWitness

/-- The curvature at the existing dense cut is the negative commutator of
its off-diagonal mode and the adjoint mode. -/
theorem denseMode_exactCurvature :
    exactCutCurvature 2 p x (star x) = -(x * star x - star x * x) := by
  have hstarLeft : star x * p = star x := by
    simpa only [star_mul, p_isSelfAdjoint.star_eq, star_star] using congrArg star p_mul_x
  have hstarRight : p * star x = 0 := by
    simpa only [star_mul, p_isSelfAdjoint.star_eq, star_zero] using congrArg star x_mul_p
  rw [exactCutCurvature_apply, x_mul_p, p_mul_x, hstarLeft, hstarRight]
  simp only [zero_sub, sub_zero, neg_mul, mul_neg, neg_sub]
  abel

/-- The exact curvature at the dense, noncommuting stage-two witness is nonzero. -/
theorem denseMode_exactCurvature_ne_zero : exactCutCurvature 2 p x (star x) ≠ 0 := by
  rw [denseMode_exactCurvature, neg_ne_zero]
  change ⁅x, star x⁆ ≠ 0
  exact x_lie_star_x_ne_zero

/-- A nonzero exact curvature remains nonzero at every later tensor stage. -/
theorem bondMap_exactCurvature_ne_zero {n m : ℕ} (hnm : n ≤ m)
    (P X Y : Stage n) (hF : exactCutCurvature n P X Y ≠ 0) :
    exactCutCurvature m (bondMap stageBond n m hnm P)
      (bondMap stageBond n m hnm X) (bondMap stageBond n m hnm Y) ≠ 0 := by
  rw [← bondMap_exactCutCurvature hnm P X Y]
  intro h
  apply hF
  apply bondMap_injective stageBond (fun k => matStageEmbed_injective k) n m hnm
  simpa only [map_zero] using h

/-- The dense non-diagonal witness has nonzero curvature on the whole tail. -/
theorem denseMode_tail_exactCurvature_ne_zero (m : ℕ) (h : 2 ≤ m) :
    exactCutCurvature m (bondMap stageBond 2 m h p)
      (bondMap stageBond 2 m h x) (bondMap stageBond 2 m h (star x)) ≠ 0 :=
  bondMap_exactCurvature_ne_zero h p x (star x) denseMode_exactCurvature_ne_zero

/-- Nonzero curvature survives the faithful inclusion into the actual colimit. -/
theorem denseMode_limitExactCurvature_ne_zero :
    limitExactCurvature (ofStage 2 p) (ofStage 2 x) (ofStage 2 (star x)) ≠ 0 := by
  rw [← ofStage_exactCurvature]
  exact fun h => denseMode_exactCurvature_ne_zero ((ofStage_eq_zero_iff 2 _).mp h)

end InfoGeometry.Canonical.TensorExactCurvatureNonzero

end
