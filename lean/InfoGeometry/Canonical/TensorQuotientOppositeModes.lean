/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorQuotientActionWitness

/-! # Opposite stabilizer weights and nonzero quotient curvature

The two adjoint dense matrix modes give opposite nonzero tangent weights.
Their quotient curvature is the faithfully embedded nonzero commutator.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorQuotientOppositeModes

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.RealStarColimitUniversal
open InfoGeometry.Canonical.TensorCurvatureTangentQuotient
open InfoGeometry.Canonical.TensorIdempotentTangentRange
open InfoGeometry.Canonical.TensorTangentStabilizerAction
open InfoGeometry.Canonical.TensorQuotientCurvatureEquivariance
open InfoGeometry.Canonical.TensorQuotientActionWitness
open InfoGeometry.Examples.RealMatrixModeWitness

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem p_mul_star_x : p * star x = 0 := by
  simpa only [star_mul, p_isSelfAdjoint.star_eq, star_zero] using congrArg star x_mul_p

private theorem star_x_mul_p : star x * p = star x := by
  simpa only [star_mul, p_isSelfAdjoint.star_eq] using congrArg star p_mul_x

/-- The adjoint of the dense mode is a tangent vector in the opposite corner. -/
def denseTangentAdjoint : idempotentTangent (ofStage 2 p) :=
  ⟨ofStage 2 (star x), by
    change ofStage 2 p * ofStage 2 (star x) + ofStage 2 (star x) * ofStage 2 p = _
    rw [← map_mul, ← map_mul, p_mul_star_x, star_x_mul_p, map_zero, zero_add]⟩

/-- The cut stabilizer acts on the adjoint tangent vector with weight `-1`. -/
theorem denseTangentAdjoint_action :
    stabilizerTangentAction (ofStage 2 p) denseCutStabilizer denseTangentAdjoint =
      -denseTangentAdjoint := by
  apply Subtype.ext
  change ofStage 2 p * ofStage 2 (star x) - ofStage 2 (star x) * ofStage 2 p =
    -ofStage 2 (star x)
  rw [← map_mul, ← map_mul, p_mul_star_x, star_x_mul_p, map_zero, zero_sub]

/-- The opposite tangent vector determines an actual quotient class. -/
def denseQuotientAdjoint : LimitDeriv ⧸ (cutEvaluation (ofStage 2 p)).ker :=
  (quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent).symm denseTangentAdjoint

/-- The adjoint tangent vector is nonzero by faithfulness of the colimit map. -/
theorem denseTangentAdjoint_ne_zero : denseTangentAdjoint ≠ 0 := by
  intro h
  have he := congrArg (fun T : idempotentTangent (ofStage 2 p) => (T : Limit)) h
  change ofStage 2 (star x) = 0 at he
  have hx : star x = 0 := (ofStage_eq_zero_iff 2 _).mp he
  apply denseTangent_ne_zero
  have hstar : x = 0 := by simpa only [star_star, star_zero] using congrArg star hx
  apply Subtype.ext
  change ofStage 2 x = 0
  rw [hstar, map_zero]

/-- The opposite quotient class is nonzero. -/
theorem denseQuotientAdjoint_ne_zero : denseQuotientAdjoint ≠ 0 := by
  intro h
  have he := congrArg (quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent) h
  have ht : denseTangentAdjoint = 0 := by simpa [denseQuotientAdjoint] using he
  exact denseTangentAdjoint_ne_zero ht

/-- The stabilizer representation acts with weight `-1` on the opposite
nonzero quotient class. -/
theorem denseQuotientAdjoint_action :
    quotientStabilizerLieHom (ofStage 2 p) denseCut_idempotent denseCutStabilizer
      denseQuotientAdjoint = -denseQuotientAdjoint := by
  rw [quotientStabilizerLieHom_apply]
  apply (quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent).injective
  rw [quotientAction_tangent, map_neg]
  simp only [denseQuotientAdjoint, LinearEquiv.apply_symm_apply, denseTangentAdjoint_action]

/-- The two opposite-weight quotient directions have nonzero curvature,
namely the embedded noncommutative matrix commutator. -/
theorem dense_opposite_quotient_curvature :
    quotientCurvature (ofStage 2 p) denseQuotient denseQuotientAdjoint =
      ofStage 2 (x * star x - star x * x) ∧
    quotientCurvature (ofStage 2 p) denseQuotient denseQuotientAdjoint ≠ 0 := by
  have hEq : quotientCurvature (ofStage 2 p) denseQuotient denseQuotientAdjoint =
      ofStage 2 (x * star x - star x * x) := by
    rw [quotientCurvature_eq_tangent_commutator (ofStage 2 p) denseCut_idempotent]
    change ((quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent)
        ((quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent).symm denseTangent) : Limit) *
      ((quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent)
        ((quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent).symm denseTangentAdjoint) : Limit) -
      ((quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent)
        ((quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent).symm denseTangentAdjoint) : Limit) *
      ((quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent)
        ((quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent).symm denseTangent) : Limit) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    change ofStage 2 x * ofStage 2 (star x) - ofStage 2 (star x) * ofStage 2 x = _
    simp only [map_sub, map_mul]
  refine ⟨hEq, ?_⟩
  rw [hEq]
  intro hz
  apply x_lie_star_x_ne_zero
  change x * star x - star x * x = 0
  exact (ofStage_eq_zero_iff 2 _).mp hz

end InfoGeometry.Canonical.TensorQuotientOppositeModes

end
