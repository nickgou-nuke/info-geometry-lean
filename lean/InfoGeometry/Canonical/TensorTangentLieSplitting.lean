/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorTangentCurvatureGeometry

/-! # Canonical splitting of idempotent tangent directions

The evaluation map has a canonical linear right inverse given by inner
Leibniz derivations. The brackets of two lifted tangent directions lie in
the cut stabilizer; this does not assert that the stabilizer is an ideal.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorTangentLieSplitting

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.TensorLieStabilizerTransport
open InfoGeometry.Canonical.TensorCurvatureTangentQuotient
open InfoGeometry.Canonical.TensorIdempotentTangentRange
open InfoGeometry.Core.PeirceTangent

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The canonical inner Leibniz derivation lifting a tangent direction. -/
def tangentLift (P : Limit) : idempotentTangent P →ₗ[ℝ] LimitDeriv where
  toFun T := limitInnerLieHom (T.1 * P - P * T.1)
  map_add' T U := by
    change limitInnerLieHom ((T.1 + U.1) * P - P * (T.1 + U.1)) = _
    have h : (T.1 + U.1) * P - P * (T.1 + U.1) =
        (T.1 * P - P * T.1) + (U.1 * P - P * U.1) := by noncomm_ring
    rw [h, map_add]
  map_smul' r T := by
    change limitInnerLieHom ((r • T.1) * P - P * (r • T.1)) = _
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, map_smul]
    rfl

/-- The lifted derivation evaluates to the original tangent vector. -/
theorem cutEvaluation_tangentLift (P : Limit) (hP : P * P = P)
    (T : idempotentTangent P) : cutEvaluation P (tangentLift P T) = T.1 := by
  exact tangent_has_inner_generator P T.1 hP T.2

/-- The canonical lift is injective. -/
theorem tangentLift_injective (P : Limit) (hP : P * P = P) :
    Function.Injective (tangentLift P) := by
  intro T U h
  apply Subtype.ext
  calc
    T.1 = cutEvaluation P (tangentLift P T) := (cutEvaluation_tangentLift P hP T).symm
    _ = cutEvaluation P (tangentLift P U) := congrArg (cutEvaluation P) h
    _ = U.1 := cutEvaluation_tangentLift P hP U

/-- Every derivation splits into a cut-stabilizing derivation and the
canonical inner lift of its tangent value at the cut. -/
theorem derivation_eq_stabilizer_add_tangentLift (P : Limit) (hP : P * P = P)
    (D : LimitDeriv) :
    ∃ (S : LimitDeriv) (T : idempotentTangent P), S ∈ limitCutStabilizer P ∧
      D = S + tangentLift P T := by
  let T : idempotentTangent P := ⟨cutEvaluation P D, cutEvaluation_mem_tangent P hP D⟩
  refine ⟨D - tangentLift P T, T, ?_, ?_⟩
  · change cutEvaluation P (D - tangentLift P T) = 0
    rw [map_sub, cutEvaluation_tangentLift P hP T]
    change cutEvaluation P D - cutEvaluation P D = 0
    exact sub_self _
  · exact (sub_add_cancel D (tangentLift P T)).symm

/-- Commutators of odd Peirce operators stabilize the cut. -/
theorem tangent_commutator_stabilizes (P X Y : Limit) (hP : P * P = P)
    (hX : X ∈ idempotentTangent P) (hY : Y ∈ idempotentTangent P) :
    (X * Y - Y * X) * P = P * (X * Y - Y * X) := by
  have hXodd := (tangent_iff_oddGrade P X hP).1 hX
  have hYodd := (tangent_iff_oddGrade P Y hP).1 hY
  rw [← hXodd, ← hYodd]
  unfold oddGrade
  peirce_nf hP

/-- The Lie bracket of two canonical inner lifts belongs to the stabilizer. -/
theorem bracket_tangentLifts_mem_stabilizer (P : Limit) (hP : P * P = P)
    (T U : idempotentTangent P) :
    ⁅tangentLift P T, tangentLift P U⁆ ∈ limitCutStabilizer P := by
  change ⁅limitInnerLieHom (T.1 * P - P * T.1),
    limitInnerLieHom (U.1 * P - P * U.1)⁆ ∈ limitCutStabilizer P
  rw [← limitInnerLieHom.map_lie]
  change ((T.1 * P - P * T.1) * (U.1 * P - P * U.1) -
    (U.1 * P - P * U.1) * (T.1 * P - P * T.1)) * P -
    P * ((T.1 * P - P * T.1) * (U.1 * P - P * U.1) -
      (U.1 * P - P * U.1) * (T.1 * P - P * T.1)) = 0
  apply sub_eq_zero.mpr
  exact tangent_commutator_stabilizes P _ _ hP
    (commutator_tangent hP T.1) (commutator_tangent hP U.1)

end InfoGeometry.Canonical.TensorTangentLieSplitting

end
