/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.RealFockBoundedCoordinateAction
import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # Actual completed coordinate actions on real Fock space

Pending native dependency: RealFockBoundedCoordinateAction. These are Mathlib
completions of the proved bounded native colimit actions. All later-stage
readbacks retain the transported fixed mode. No CAR or adjoint theorem is
asserted here, and no replacement carrier or action is introduced.
-/
noncomputable section
namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace
attribute [local instance] fockInfinityInnerProductCore fockInfinityPreInnerProductCore
  fockInfinityNormedAddCommGroup fockInfinityInnerProductSpace fockInfinityNormedSpace
  fockInfinityUniformContinuousConstSMul
attribute [local instance] fockInfinityMetricUniformSpace fockInfinityMetricTopology

local notation "ofC" => DirectLimit.Algebra.of SplitClNNAlg
  (fun m n h => splitCliffordMap m n h)

/-- Completion of the actual bounded creation action. -/
def fockCompletedCreationCLM (m : ℕ) (i : Fin m) :
    RealFockCompletion →L[ℝ] RealFockCompletion :=
  (fockInfinityCreationCLM m i).completion

/-- Completion of the actual bounded contraction action. -/
def fockCompletedContractionCLM (m : ℕ) (i : Fin m) :
    RealFockCompletion →L[ℝ] RealFockCompletion :=
  (fockInfinityContractionCLM m i).completion

/-- Completed creation agrees with its original action on all algebraic vectors. -/
theorem fockCompletedCreationCLM_coe (m : ℕ) (i : Fin m) (ψ : FockInfinity) :
    fockCompletedCreationCLM m i (ψ : RealFockCompletion) =
      (fockInfinityCreationCLM m i ψ : RealFockCompletion) :=
  ContinuousLinearMap.completion_apply_coe (fockInfinityCreationCLM m i) ψ

/-- Completed contraction agrees with the original action on all algebraic vectors. -/
theorem fockCompletedContractionCLM_coe (m : ℕ) (i : Fin m) (ψ : FockInfinity) :
    fockCompletedContractionCLM m i (ψ : RealFockCompletion) =
      (fockInfinityContractionCLM m i ψ : RealFockCompletion) :=
  ContinuousLinearMap.completion_apply_coe (fockInfinityContractionCLM m i) ψ

/-- Exact creation readback on every later finite stage. -/
theorem fockCompletedCreationCLM_stage (m n : ℕ) (h : m ≤ n)
    (i : Fin m) (ψ : FockStage n) :
    fockCompletedCreationCLM m i (fockStageToCompletion n ψ) =
      fockStageToCompletion n (fockExtActionCLM n (fockModeShift m n h i) ψ) := by
  have ha : ofC n (splitCliffordMap m n h (fockCreationGenerator m i)) =
      ofC m (fockCreationGenerator m i) :=
    DirectLimit.Algebra.of_f (f := fun j k hjk => splitCliffordMap j k hjk)
      h (fockCreationGenerator m i)
  simp only [fockStageToCompletion_apply, fockCompletedCreationCLM_coe]
  apply congrArg (fun x : FockInfinity => (x : RealFockCompletion))
  rw [fockInfinityCreationCLM_apply, ← ha, splitCliffordFockAction_of,
    towerSpinorRep_transported_creation]

/-- Exact contraction readback on every later finite stage. -/
theorem fockCompletedContractionCLM_stage (m n : ℕ) (h : m ≤ n)
    (i : Fin m) (ψ : FockStage n) :
    fockCompletedContractionCLM m i (fockStageToCompletion n ψ) =
      fockStageToCompletion n (fockIntActionCLM n (fockModeShift m n h i) ψ) := by
  have ha : ofC n (splitCliffordMap m n h (fockContractionGenerator m i)) =
      ofC m (fockContractionGenerator m i) :=
    DirectLimit.Algebra.of_f (f := fun j k hjk => splitCliffordMap j k hjk)
      h (fockContractionGenerator m i)
  simp only [fockStageToCompletion_apply, fockCompletedContractionCLM_coe]
  apply congrArg (fun x : FockInfinity => (x : RealFockCompletion))
  rw [fockInfinityContractionCLM_apply, ← ha, splitCliffordFockAction_of,
    towerSpinorRep_transported_contraction]

/-- Creation remains contractive on every vector of the actual completion. -/
theorem fockCompletedCreationCLM_norm_apply_le (m : ℕ) (i : Fin m)
    (ψ : RealFockCompletion) : ‖fockCompletedCreationCLM m i ψ‖ ≤ ‖ψ‖ := by
  induction ψ using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (fockCompletedCreationCLM m i).continuous.norm continuous_norm
  | ih ψ =>
      simpa only [fockCompletedCreationCLM_coe, UniformSpace.Completion.norm_coe,
        fockInfinityCreationCLM_apply] using splitCliffordFockAction_creation_norm_le m i ψ

/-- Contraction remains contractive on every vector of the actual completion. -/
theorem fockCompletedContractionCLM_norm_apply_le (m : ℕ) (i : Fin m)
    (ψ : RealFockCompletion) : ‖fockCompletedContractionCLM m i ψ‖ ≤ ‖ψ‖ := by
  induction ψ using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (fockCompletedContractionCLM m i).continuous.norm continuous_norm
  | ih ψ =>
      simpa only [fockCompletedContractionCLM_coe, UniformSpace.Completion.norm_coe,
        fockInfinityContractionCLM_apply] using splitCliffordFockAction_contraction_norm_le m i ψ

/-- Operator-norm control is derived from the completed pointwise bound. -/
theorem fockCompletedCreationCLM_norm_le (m : ℕ) (i : Fin m) :
    ‖fockCompletedCreationCLM m i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simpa only [one_mul] using fockCompletedCreationCLM_norm_apply_le m i ψ

/-- The completed contraction operator has norm at most one. -/
theorem fockCompletedContractionCLM_norm_le (m : ℕ) (i : Fin m) :
    ‖fockCompletedContractionCLM m i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simpa only [one_mul] using fockCompletedContractionCLM_norm_apply_le m i ψ

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
