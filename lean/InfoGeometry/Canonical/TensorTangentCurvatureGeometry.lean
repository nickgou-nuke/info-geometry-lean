/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorIdempotentTangentRange
import InfoGeometry.Canonical.TensorExactCurvatureTrace

/-! # Geometry of the idempotent tangent quotient

The commutator of two off-diagonal tangent operators is even and has zero
cyclic trace. A dense matrix witness also proves that the cut stabilizer
need not be a Lie ideal, so the quotient above is only a vector quotient.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorTangentCurvatureGeometry

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.TensorLieStabilizerTransport
open InfoGeometry.Canonical.TensorCurvatureTangentQuotient
open InfoGeometry.Canonical.TensorIdempotentTangentRange
open InfoGeometry.Canonical.TensorExactCurvatureTrace
open InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
open InfoGeometry.Canonical.FrechetPeirceLieStabilizer
open InfoGeometry.Examples.RealMatrixModeWitness

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The descended tangent curvature commutes with the idempotent cut. -/
theorem quotientCurvature_commutes_cut (P : Limit) (hP : P * P = P)
    (u v : LimitDeriv ⧸ (cutEvaluation P).ker) :
    P * quotientCurvature P u v = quotientCurvature P u v * P := by
  let X : Limit := quotientEquivIdempotentTangent P hP u
  let Y : Limit := quotientEquivIdempotentTangent P hP v
  have hX : oddGrade P X = X := (tangent_iff_oddGrade P X hP).1
    (quotientEquivIdempotentTangent P hP u).property
  have hY : oddGrade P Y = Y := (tangent_iff_oddGrade P Y hP).1
    (quotientEquivIdempotentTangent P hP v).property
  rw [quotientCurvature_eq_tangent_commutator P hP]
  change P * (X * Y - Y * X) = (X * Y - Y * X) * P
  rw [← hX, ← hY]
  unfold oddGrade
  peirce_nf hP

/-- The actual normalized colimit trace annihilates all tangent quotient
curvatures by cyclicity. -/
theorem quotientCurvature_trace_zero (P : Limit)
    (u v : LimitDeriv ⧸ (cutEvaluation P).ker) :
    normalizedTraceLimit (quotientCurvature P u v) = 0 := by
  unfold quotientCurvature
  rw [map_sub, normalizedTraceLimit_cyclic, sub_self]

/-- The stabilizer of the dense cut is not closed under brackets with all
ambient derivations; this is an explicit obstruction to a quotient Lie algebra. -/
theorem dense_cut_stabilizer_not_ideal :
    ∃ D E : LimitDeriv, D ∈ limitCutStabilizer (ofStage 2 p) ∧
      ⁅D, E⁆ ∉ limitCutStabilizer (ofStage 2 p) := by
  refine ⟨limitInnerLieHom (ofStage 2 p), limitInnerLieHom (ofStage 2 x),
    denseMode_limit_stabilizer_separation.1, ?_⟩
  have hbracket : ⁅limitInnerLieHom (ofStage 2 p), limitInnerLieHom (ofStage 2 x)⁆ =
      limitInnerLieHom (ofStage 2 x) := by
    rw [← limitInnerLieHom.map_lie]
    congr 1
    rw [Ring.lie_def, ← map_mul, ← map_mul, ← map_sub, p_mul_x, x_mul_p, sub_zero]
  rw [hbracket]
  exact denseMode_limit_stabilizer_separation.2

end InfoGeometry.Canonical.TensorTangentCurvatureGeometry

end
