/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorQuotientCurvatureEquivariance

/-! # Nontrivial stabilizer representation on the tangent quotient

The dense, nondiagonal finite matrix mode has a faithful colimit image. The
inner derivation of the cut fixes its quotient class as an eigenvector with
nonzero eigenvalue. No scalar or diagonal approximation is used.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorQuotientActionWitness

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.RealStarColimitUniversal
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.TensorLieStabilizerTransport
open InfoGeometry.Canonical.TensorCurvatureTangentQuotient
open InfoGeometry.Canonical.TensorIdempotentTangentRange
open InfoGeometry.Canonical.TensorTangentStabilizerAction
open InfoGeometry.Canonical.TensorQuotientCurvatureEquivariance
open InfoGeometry.Canonical.FrechetPeirceStabilizerWitness
open InfoGeometry.Examples.RealMatrixModeWitness

/-- The faithfully embedded cut remains idempotent. -/
theorem denseCut_idempotent : ofStage 2 p * ofStage 2 p = ofStage 2 p := by
  rw [← map_mul, p_isIdempotentElem]

/-- The dense off-diagonal mode is an actual tangent vector of the colimit cut. -/
def denseTangent : idempotentTangent (ofStage 2 p) :=
  ⟨ofStage 2 x, by
    change ofStage 2 p * ofStage 2 x + ofStage 2 x * ofStage 2 p = ofStage 2 x
    rw [← map_mul, ← map_mul, p_mul_x, x_mul_p, map_zero, add_zero]⟩

/-- The inner derivation of the cut is a member of its actual Lie stabilizer. -/
def denseCutStabilizer : limitCutStabilizer (ofStage 2 p) :=
  ⟨limitInnerLieHom (ofStage 2 p), denseMode_limit_stabilizer_separation.1⟩

/-- The dense tangent vector is a nonzero eigenvector of the stabilizer action. -/
theorem denseTangent_action :
    stabilizerTangentAction (ofStage 2 p) denseCutStabilizer denseTangent = denseTangent := by
  apply Subtype.ext
  change ofStage 2 p * ofStage 2 x - ofStage 2 x * ofStage 2 p = ofStage 2 x
  rw [← map_mul, ← map_mul, p_mul_x, x_mul_p, map_zero, sub_zero]

theorem denseTangent_ne_zero : denseTangent ≠ 0 := by
  intro h
  have he := congrArg (fun T : idempotentTangent (ofStage 2 p) => (T : Limit)) h
  change ofStage 2 x = 0 at he
  exact denseMode_ne_zero ((ofStage_eq_zero_iff 2 x).mp he)

/-- The class corresponding to the dense tangent vector in the quotient. -/
def denseQuotient : LimitDeriv ⧸ (cutEvaluation (ofStage 2 p)).ker :=
  (quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent).symm denseTangent

theorem denseQuotient_ne_zero : denseQuotient ≠ 0 := by
  intro h
  have he := congrArg (quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent) h
  have ht : denseTangent = 0 := by
    simpa [denseQuotient] using he
  exact denseTangent_ne_zero ht

/-- The native quotient representation is genuinely nontrivial: the dense
nonzero class is fixed by a concrete stabilizer element. -/
theorem denseQuotient_action :
    quotientStabilizerLieHom (ofStage 2 p) denseCut_idempotent denseCutStabilizer
      denseQuotient = denseQuotient := by
  rw [quotientStabilizerLieHom_apply]
  apply (quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent).injective
  rw [quotientAction_tangent]
  change stabilizerTangentAction (ofStage 2 p) denseCutStabilizer
      ((quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent)
        ((quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent).symm denseTangent)) = _
  rw [LinearEquiv.apply_symm_apply, denseTangent_action]
  exact ((quotientEquivIdempotentTangent (ofStage 2 p) denseCut_idempotent).apply_symm_apply _).symm

/-- The corresponding represented stabilizer endomorphism is not zero. -/
theorem denseQuotient_representation_ne_zero :
    quotientStabilizerLieHom (ofStage 2 p) denseCut_idempotent denseCutStabilizer ≠ 0 := by
  intro h
  have he := congrArg
    (fun F : Module.End ℝ (LimitDeriv ⧸ (cutEvaluation (ofStage 2 p)).ker) =>
      F denseQuotient) h
  rw [denseQuotient_action] at he
  exact denseQuotient_ne_zero (by simpa using he)

end InfoGeometry.Canonical.TensorQuotientActionWitness

end
