/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.RealFockCompletedCoordinateAction
import InfoGeometry.Clifford.FiniteFockCLMReflexivePair
import InfoGeometry.Clifford.FiniteRealFockAdjoint
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Same-mode CAR and adjoints on the actual real Fock completion

The actual finite laws pass through the existing stage isometries and completion density. This is
same-mode closure only; cross-mode CAR requires the separate index-coherence
extension. No new action, finite owner, or carrier is introduced.
-/
noncomputable section
namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace
attribute [local instance] fockInfinityInnerProductCore fockInfinityPreInnerProductCore
  fockInfinityNormedAddCommGroup fockInfinityInnerProductSpace fockInfinityNormedSpace
  fockInfinityUniformContinuousConstSMul fockInfinityMetricUniformSpace fockInfinityMetricTopology

/-- Two algebraic vectors have simultaneous representatives above any birth stage. -/
theorem fockInfinity_exists_common_stage_ge (m : ℕ) (x y : FockInfinity) :
    ∃ n, ∃ _h : m ≤ n, ∃ a b : FockStage n,
      x = fockToInfinity n a ∧ y = fockToInfinity n b := by
  obtain ⟨n, a, ha⟩ := DirectLimit.exists_eq_mk (f := fun i j h => fockStageMap i j h) x
  obtain ⟨p, b, hb⟩ := DirectLimit.exists_eq_mk (f := fun i j h => fockStageMap i j h) y
  have ha' : x = fockToInfinity n a := ha
  have hb' : y = fockToInfinity p b := hb
  let k := max m (max n p)
  have hmk : m ≤ k := le_max_left _ _
  have hnk : n ≤ k := (le_max_left n p).trans (le_max_right m (max n p))
  have hpk : p ≤ k := (le_max_right n p).trans (le_max_right m (max n p))
  refine ⟨k, hmk, fockStageMap n k hnk a, fockStageMap p k hpk b, ?_, ?_⟩
  · exact ha'.trans (fockToInfinity_transition hnk a).symm
  · exact hb'.trans (fockToInfinity_transition hpk b).symm

/-- Creation square-zero readback above the fixed mode's birth stage. -/
theorem fockCompletedCreation_square_stage (m n : ℕ) (h : m ≤ n)
    (i : Fin m) (x : FockStage n) :
    fockCompletedCreationCLM m i (fockCompletedCreationCLM m i
      (fockStageToCompletion n x)) = 0 := by
  rw [fockCompletedCreationCLM_stage m n h, fockCompletedCreationCLM_stage m n h]
  have hz := congrArg (fun T : FockStage n →L[ℝ] FockStage n => T x)
    (fockExtActionCLM_sq_zero n (fockModeShift m n h i))
  change fockExtActionCLM n (fockModeShift m n h i)
    (fockExtActionCLM n (fockModeShift m n h i) x) = 0 at hz
  rw [hz, map_zero]

/-- Contraction square-zero readback above the fixed mode's birth stage. -/
theorem fockCompletedContraction_square_stage (m n : ℕ) (h : m ≤ n)
    (i : Fin m) (x : FockStage n) :
    fockCompletedContractionCLM m i (fockCompletedContractionCLM m i
      (fockStageToCompletion n x)) = 0 := by
  rw [fockCompletedContractionCLM_stage m n h, fockCompletedContractionCLM_stage m n h]
  have hz := congrArg (fun T : FockStage n →L[ℝ] FockStage n => T x)
    (fockIntActionCLM_sq_zero n (fockModeShift m n h i))
  change fockIntActionCLM n (fockModeShift m n h i)
    (fockIntActionCLM n (fockModeShift m n h i) x) = 0 at hz
  rw [hz, map_zero]

/-- The completed anticommutator is the full identity on every later finite stage. -/
theorem fockCompleted_CAR_stage (m n : ℕ) (h : m ≤ n) (i : Fin m) (x : FockStage n) :
    fockCompletedContractionCLM m i (fockCompletedCreationCLM m i (fockStageToCompletion n x)) +
      fockCompletedCreationCLM m i (fockCompletedContractionCLM m i (fockStageToCompletion n x)) =
        fockStageToCompletion n x := by
  simp only [fockCompletedCreationCLM_stage m n h, fockCompletedContractionCLM_stage m n h]
  rw [← map_add]
  have he := congrArg (fun T : FockStage n →L[ℝ] FockStage n => T x)
    (fock_coordinate_CLM_CAR n (fockModeShift m n h i))
  change fockIntActionCLM n (fockModeShift m n h i)
      (fockExtActionCLM n (fockModeShift m n h i) x) +
    fockExtActionCLM n (fockModeShift m n h i)
      (fockIntActionCLM n (fockModeShift m n h i) x) = x at he
  rw [he]

/-- Actual completed creation is square-zero, by density of algebraic vectors. -/
theorem fockCompletedCreationCLM_sq_zero (m : ℕ) (i : Fin m) :
    fockCompletedCreationCLM m i * fockCompletedCreationCLM m i = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change fockCompletedCreationCLM m i (fockCompletedCreationCLM m i x) = 0
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq ((fockCompletedCreationCLM m i).continuous.comp
      (fockCompletedCreationCLM m i).continuous) continuous_const
  | ih x =>
      obtain ⟨n, h, a, _, ha, _⟩ := fockInfinity_exists_common_stage_ge m x x
      rw [ha, ← fockStageToCompletion_apply]
      exact fockCompletedCreation_square_stage m n h i a

/-- Actual completed contraction is square-zero. -/
theorem fockCompletedContractionCLM_sq_zero (m : ℕ) (i : Fin m) :
    fockCompletedContractionCLM m i * fockCompletedContractionCLM m i = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change fockCompletedContractionCLM m i (fockCompletedContractionCLM m i x) = 0
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq ((fockCompletedContractionCLM m i).continuous.comp
      (fockCompletedContractionCLM m i).continuous) continuous_const
  | ih x =>
      obtain ⟨n, h, a, _, ha, _⟩ := fockInfinity_exists_common_stage_ge m x x
      rw [ha, ← fockStageToCompletion_apply]
      exact fockCompletedContraction_square_stage m n h i a

/-- The fixed-vector equation of two composed continuous operators is closed. -/
theorem fockCompletion_anticommutator_fixed_isClosed
    (S T : RealFockCompletion →L[ℝ] RealFockCompletion) :
    IsClosed {x : RealFockCompletion | S (T x) + T (S x) = x} := by
  have hsum : Continuous (fun x : RealFockCompletion => S (T x) + T (S x)) :=
    (S.continuous.comp T.continuous).add (T.continuous.comp S.continuous)
  exact isClosed_eq hsum (continuous_id : Continuous (fun x : RealFockCompletion => x))

/-- Same-mode CAR holds on the entire actual completed carrier. -/
theorem fockCompleted_sameMode_CAR (m : ℕ) (i : Fin m) :
    fockCompletedContractionCLM m i * fockCompletedCreationCLM m i +
      fockCompletedCreationCLM m i * fockCompletedContractionCLM m i = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change fockCompletedContractionCLM m i (fockCompletedCreationCLM m i x) +
    fockCompletedCreationCLM m i (fockCompletedContractionCLM m i x) = x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact fockCompletion_anticommutator_fixed_isClosed
        (fockCompletedContractionCLM m i) (fockCompletedCreationCLM m i)
  | ih x =>
      obtain ⟨n, h, a, _, ha, _⟩ := fockInfinity_exists_common_stage_ge m x x
      rw [ha, ← fockStageToCompletion_apply]
      exact fockCompleted_CAR_stage m n h i a

/-- The actual completed stage isometry preserves the finite adjoint identity. -/
theorem fockCompleted_creation_contraction_inner_stage (m n : ℕ) (h : m ≤ n)
    (i : Fin m) (x y : FockStage n) :
    inner ℝ (fockCompletedCreationCLM m i (fockStageToCompletion n x))
        (fockStageToCompletion n y) =
      inner ℝ (fockStageToCompletion n x)
        (fockCompletedContractionCLM m i (fockStageToCompletion n y)) := by
  rw [fockCompletedCreationCLM_stage m n h, fockCompletedContractionCLM_stage m n h,
    fockStageToCompletion_inner, fockStageToCompletion_inner]
  exact fock_extAction_intAction_inner n (fockModeShift m n h i) x y

/-- The two-variable inner-adjoint equation defines a closed subset of the product. -/
theorem fockCompletion_inner_adjoint_isClosed
    (S T : RealFockCompletion →L[ℝ] RealFockCompletion) :
    IsClosed {p : RealFockCompletion × RealFockCompletion |
      inner ℝ (S p.1) p.2 = inner ℝ p.1 (T p.2)} := by
  have hleft : Continuous (fun p : RealFockCompletion × RealFockCompletion =>
      inner ℝ (S p.1) p.2) :=
    (S.continuous.comp continuous_fst).inner continuous_snd
  have hright : Continuous (fun p : RealFockCompletion × RealFockCompletion =>
      inner ℝ p.1 (T p.2)) :=
    continuous_fst.inner (T.continuous.comp continuous_snd)
  exact isClosed_eq hleft hright

/-- Two-variable completion density gives the genuine Hilbert adjoint identity. -/
theorem fockCompleted_creation_contraction_inner (m : ℕ) (i : Fin m)
    (x y : RealFockCompletion) :
    inner ℝ (fockCompletedCreationCLM m i x) y =
      inner ℝ x (fockCompletedContractionCLM m i y) := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
      exact fockCompletion_inner_adjoint_isClosed
        (fockCompletedCreationCLM m i) (fockCompletedContractionCLM m i)
  | ih x y =>
      obtain ⟨n, h, a, b, ha, hb⟩ := fockInfinity_exists_common_stage_ge m x y
      rw [ha, hb, ← fockStageToCompletion_apply, ← fockStageToCompletion_apply]
      exact fockCompleted_creation_contraction_inner_stage m n h i a b

/-- The adjoint of completed contraction is the actual completed creation map. -/
theorem fockCompletedContractionCLM_adjoint (m : ℕ) (i : Fin m) :
    (fockCompletedContractionCLM m i).adjoint = fockCompletedCreationCLM m i := by
  exact ((ContinuousLinearMap.eq_adjoint_iff
    (fockCompletedCreationCLM m i) (fockCompletedContractionCLM m i)).2
      (fockCompleted_creation_contraction_inner m i)).symm

/-- Adjoint involution identifies the adjoint of creation with actual contraction. -/
theorem fockCompletedCreationCLM_adjoint (m : ℕ) (i : Fin m) :
    (fockCompletedCreationCLM m i).adjoint = fockCompletedContractionCLM m i := by
  have he := congrArg (fun T : RealFockCompletion →L[ℝ] RealFockCompletion => T.adjoint)
    (fockCompletedContractionCLM_adjoint m i)
  simpa only [ContinuousLinearMap.adjoint_adjoint] using he.symm

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
