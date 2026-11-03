/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorQuotientOppositeModes

/-! # Cut derivation as an involution on the tangent quotient

For every colimit idempotent, the inner derivation of the cut belongs to its
stabilizer and squares to the identity on the tangent quotient. The previous
dense matrix witness supplies nonzero vectors of both opposite weights.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorQuotientCutInvolution

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.TensorLieStabilizerTransport
open InfoGeometry.Canonical.TensorCurvatureTangentQuotient
open InfoGeometry.Canonical.TensorIdempotentTangentRange
open InfoGeometry.Canonical.TensorTangentStabilizerAction
open InfoGeometry.Canonical.TensorQuotientCurvatureEquivariance
open InfoGeometry.Core.PeirceTangent

/-- The inner derivation of any cut lies in its Lie stabilizer. -/
def cutInnerStabilizer (P : Limit) : limitCutStabilizer P :=
  ⟨limitInnerLieHom P, by
    change P * P - P * P = 0
    exact sub_self _⟩

/-- The cut's inner derivation is an involution on the idempotent tangent
module. -/
theorem cutInner_tangent_involutive (P : Limit) (hP : P * P = P)
    (T : idempotentTangent P) :
    stabilizerTangentAction P (cutInnerStabilizer P)
      (stabilizerTangentAction P (cutInnerStabilizer P) T) = T := by
  apply Subtype.ext
  change P * (P * T.1 - T.1 * P) - (P * T.1 - T.1 * P) * P = T.1
  exact (tangent_iff_adjoint_square_eq_self hP).1 T.2

/-- The same involution acts on the actual vector quotient by the
stabilizer, via the established quotient-to-tangent equivalence. -/
theorem cutInner_quotient_involutive (P : Limit) (hP : P * P = P)
    (u : LimitDeriv ⧸ (cutEvaluation P).ker) :
    quotientStabilizerAction P hP (cutInnerStabilizer P)
      (quotientStabilizerAction P hP (cutInnerStabilizer P) u) = u := by
  apply (quotientEquivIdempotentTangent P hP).injective
  rw [quotientAction_tangent, quotientAction_tangent, cutInner_tangent_involutive P hP]

/-- The involutive stabilizer action is a native linear automorphism. -/
def cutQuotientInvolution (P : Limit) (hP : P * P = P) :
    (LimitDeriv ⧸ (cutEvaluation P).ker) ≃ₗ[ℝ] (LimitDeriv ⧸ (cutEvaluation P).ker) :=
  LinearEquiv.ofInvolutive (quotientStabilizerAction P hP (cutInnerStabilizer P))
    (cutInner_quotient_involutive P hP)

open InfoGeometry.Canonical.TensorQuotientActionWitness
open InfoGeometry.Canonical.TensorQuotientOppositeModes
open InfoGeometry.Examples.RealMatrixModeWitness

/-- Both eigenspaces of the cut involution are witnessed by nonzero dense
matrix modes, whose mutual quotient curvature is nonzero. -/
theorem dense_opposite_weights_and_curvature :
    denseQuotient ≠ 0 ∧ denseQuotientAdjoint ≠ 0 ∧
    cutQuotientInvolution (ofStage 2 p) denseCut_idempotent denseQuotient = denseQuotient ∧
    cutQuotientInvolution (ofStage 2 p) denseCut_idempotent denseQuotientAdjoint =
      -denseQuotientAdjoint ∧
    quotientCurvature (ofStage 2 p) denseQuotient denseQuotientAdjoint ≠ 0 := by
  have hCut : cutInnerStabilizer (ofStage 2 p) = denseCutStabilizer := by
    apply Subtype.ext
    rfl
  refine ⟨denseQuotient_ne_zero, denseQuotientAdjoint_ne_zero, ?_, ?_,
    dense_opposite_quotient_curvature.2⟩
  · change quotientStabilizerAction (ofStage 2 p) denseCut_idempotent
      (cutInnerStabilizer (ofStage 2 p)) denseQuotient = denseQuotient
    rw [hCut, ← quotientStabilizerLieHom_apply]
    exact denseQuotient_action
  · change quotientStabilizerAction (ofStage 2 p) denseCut_idempotent
      (cutInnerStabilizer (ofStage 2 p)) denseQuotientAdjoint = -denseQuotientAdjoint
    rw [hCut, ← quotientStabilizerLieHom_apply]
    exact denseQuotientAdjoint_action

end InfoGeometry.Canonical.TensorQuotientCutInvolution

end
