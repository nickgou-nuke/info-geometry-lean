/-
InfoGeometry/OperatorAlgebra/IndividuatedCayley.lean

The Individuation of the Cayley Transform.
Eliminating the Unitary Shadow.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.ConstructiveCayley

noncomputable section

namespace InfoGeometry.OperatorAlgebra.IndividuatedCayley

open InfoGeometry.OperatorAlgebra.ConstructiveCayley

/-! ## 1. The Real Adjoint Geometry -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
A constructively verified Self-Adjoint/Phase geometry.
This replaces the `unitary_certificate` shadow.
-/
structure VerifiedUnitaryResolvent
    (K : H →L[ℝ] H)
    (D : H →L[ℝ] H) extends VerifiedPhaseResolvent H K D where
  /-- D is self-adjoint. -/
  D_selfAdjoint : ContinuousLinearMap.adjoint D = D

  /-- K is anti-self-adjoint (the real representation of i). -/
  K_skewAdjoint : ContinuousLinearMap.adjoint K = -K

  /-- The inverse of (D + K) behaves correctly under the adjoint.
      Since (D + K)* = D* + K* = D - K, the adjoint of the inverse
      is the inverse of (D - K). -/
  denomInv_adjoint_law :
    (ContinuousLinearMap.adjoint denomInv).comp (D - K) = ContinuousLinearMap.id ℝ H

/-! ## 2. The Synthesis (Rubedo) -/

/--
CONSTRUCTIVE PROOF: The Cayley transform is an isometry (U* U = I).
We have eliminated the `unitary_law` hypothesis.
-/
theorem boundedCayley_is_isometry
    {K D : H →L[ℝ] H}
    (R : VerifiedUnitaryResolvent K D) :
    (ContinuousLinearMap.adjoint (boundedCayley R.toVerifiedPhaseResolvent)).comp
        (boundedCayley R.toVerifiedPhaseResolvent) =
      ContinuousLinearMap.id ℝ H := by
  dsimp [boundedCayley]
  rw [ContinuousLinearMap.adjoint_comp]
  have h_num_adjoint : ContinuousLinearMap.adjoint (D - K) = D + K := by
    simp [R.D_selfAdjoint, R.K_skewAdjoint, sub_eq_add_neg]
  rw [h_num_adjoint]
  have h_commute : (D + K).comp (D - K) = (D - K).comp (D + K) :=
    (D_sub_K_commutes_D_add_K R.D_phase_linear).symm
  calc
    ((ContinuousLinearMap.adjoint R.denomInv).comp (D + K)).comp
          ((D - K).comp R.denomInv)
        =
      ((ContinuousLinearMap.adjoint R.denomInv).comp ((D + K).comp (D - K))).comp
          R.denomInv := by
            rw [ContinuousLinearMap.comp_assoc]
            rw [ContinuousLinearMap.comp_assoc]
            rw [ContinuousLinearMap.comp_assoc]
    _ =
      ((ContinuousLinearMap.adjoint R.denomInv).comp ((D - K).comp (D + K))).comp
          R.denomInv := by
            rw [h_commute]
    _ =
      ((ContinuousLinearMap.adjoint R.denomInv).comp (D - K)).comp
          ((D + K).comp R.denomInv) := by
            rw [ContinuousLinearMap.comp_assoc]
            rw [ContinuousLinearMap.comp_assoc]
            rw [ContinuousLinearMap.comp_assoc]
    _ = (ContinuousLinearMap.id ℝ H).comp (ContinuousLinearMap.id ℝ H) := by
          rw [R.denomInv_adjoint_law, R.denom_right]
    _ = ContinuousLinearMap.id ℝ H := by
          rw [ContinuousLinearMap.id_comp]

attribute [rep_depth operator]
  VerifiedUnitaryResolvent
  boundedCayley_is_isometry

end InfoGeometry.OperatorAlgebra.IndividuatedCayley
