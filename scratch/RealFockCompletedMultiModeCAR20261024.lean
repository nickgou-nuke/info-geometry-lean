/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.RealFockModeCoherence
import InfoGeometry.Clifford.RealFockCompletedSameModeCAR

/-! # Cross-mode CAR for the actual completed Fock operators

Pending native helper imports. Birth-stage changes identify operators through
their existing Clifford colimit elements. The cross-mode equality test compares
transported indices, not raw indices from different finite stages.
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
  fockInfinityUniformContinuousConstSMul fockInfinityMetricUniformSpace fockInfinityMetricTopology

local notation "ofC" => DirectLimit.Algebra.of SplitClNNAlg
  (fun m n h => splitCliffordMap m n h)

/-- Equality on every stage above a fixed cutoff determines a completed CLM. -/
theorem fockCompletedCLM_ext_on_stages_ge (m : ℕ)
    (S T : RealFockCompletion →L[ℝ] RealFockCompletion)
    (he : ∀ n, m ≤ n → ∀ x : FockStage n,
      S (fockStageToCompletion n x) = T (fockStageToCompletion n x)) : S = T := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq S.continuous T.continuous
  | ih x =>
      obtain ⟨n, h, a, _, ha, _⟩ := fockInfinity_exists_common_stage_ge m x x
      rw [ha, ← fockStageToCompletion_apply]
      exact he n h a

/-- Creations of any two modes born in the same stage anticommute. -/
theorem fockCompleted_creation_cross (m : ℕ) (i j : Fin m) :
    fockCompletedCreationCLM m i * fockCompletedCreationCLM m j +
      fockCompletedCreationCLM m j * fockCompletedCreationCLM m i = 0 := by
  apply fockCompletedCLM_ext_on_stages_ge m
  intro n h x
  change fockCompletedCreationCLM m i (fockCompletedCreationCLM m j (fockStageToCompletion n x)) +
    fockCompletedCreationCLM m j (fockCompletedCreationCLM m i (fockStageToCompletion n x)) = 0
  simp only [fockCompletedCreationCLM_stage m n h]
  rw [← map_add, fockExtActionCLM_cross_apply, map_zero]

/-- Contractions of any two modes born in the same stage anticommute. -/
theorem fockCompleted_contraction_cross (m : ℕ) (i j : Fin m) :
    fockCompletedContractionCLM m i * fockCompletedContractionCLM m j +
      fockCompletedContractionCLM m j * fockCompletedContractionCLM m i = 0 := by
  apply fockCompletedCLM_ext_on_stages_ge m
  intro n h x
  change fockCompletedContractionCLM m i (fockCompletedContractionCLM m j (fockStageToCompletion n x)) +
    fockCompletedContractionCLM m j (fockCompletedContractionCLM m i (fockStageToCompletion n x)) = 0
  simp only [fockCompletedContractionCLM_stage m n h]
  rw [← map_add, fockIntActionCLM_cross_apply, map_zero]

/-- Mixed CAR detects equality of modes in a common birth stage. -/
theorem fockCompleted_mixed_cross (m : ℕ) (i j : Fin m) :
    fockCompletedContractionCLM m i * fockCompletedCreationCLM m j +
      fockCompletedCreationCLM m j * fockCompletedContractionCLM m i =
        if i = j then 1 else 0 := by
  apply fockCompletedCLM_ext_on_stages_ge m
  intro n h x
  change fockCompletedContractionCLM m i (fockCompletedCreationCLM m j (fockStageToCompletion n x)) +
    fockCompletedCreationCLM m j (fockCompletedContractionCLM m i (fockStageToCompletion n x)) =
      (if i = j then (1 : RealFockCompletion →L[ℝ] RealFockCompletion) else 0) (fockStageToCompletion n x)
  simp only [fockCompletedCreationCLM_stage m n h, fockCompletedContractionCLM_stage m n h]
  rw [← map_add, fock_coordinate_cross_CAR_apply]
  by_cases hij : i = j
  · subst j; simp
  · have hshift : fockModeShift m n h i ≠ fockModeShift m n h j :=
      fun he => hij (fockModeShift_injective m n h he)
    simp [hij, hshift]

/-- Changing birth stage along the native transition does not change creation. -/
theorem fockCompletedCreationCLM_shift (m n : ℕ) (h : m ≤ n) (i : Fin m) :
    fockCompletedCreationCLM m i = fockCompletedCreationCLM n (fockModeShift m n h i) := by
  have ha : ofC n (fockCreationGenerator n (fockModeShift m n h i)) =
      ofC m (fockCreationGenerator m i) := by
    rw [← splitCliffordMap_creation m n h i]
    exact DirectLimit.Algebra.of_f (f := fun j k hjk => splitCliffordMap j k hjk)
      h (fockCreationGenerator m i)
  apply ContinuousLinearMap.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq (fockCompletedCreationCLM m i).continuous
        (fockCompletedCreationCLM n (fockModeShift m n h i)).continuous
  | ih x =>
      simp only [fockCompletedCreationCLM_coe, fockInfinityCreationCLM_apply, ha]

/-- Changing birth stage along the same transition does not change contraction. -/
theorem fockCompletedContractionCLM_shift (m n : ℕ) (h : m ≤ n) (i : Fin m) :
    fockCompletedContractionCLM m i = fockCompletedContractionCLM n (fockModeShift m n h i) := by
  have ha : ofC n (fockContractionGenerator n (fockModeShift m n h i)) =
      ofC m (fockContractionGenerator m i) := by
    rw [← splitCliffordMap_contraction m n h i]
    exact DirectLimit.Algebra.of_f (f := fun j k hjk => splitCliffordMap j k hjk)
      h (fockContractionGenerator m i)
  apply ContinuousLinearMap.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq (fockCompletedContractionCLM m i).continuous
        (fockCompletedContractionCLM n (fockModeShift m n h i)).continuous
  | ih x =>
      simp only [fockCompletedContractionCLM_coe, fockInfinityContractionCLM_apply, ha]

/-- Creations born at different stages anticommute on the actual completed carrier. -/
theorem fockCompleted_creation_different_birth (m n k : ℕ) (hmk : m ≤ k) (hnk : n ≤ k)
    (i : Fin m) (j : Fin n) :
    fockCompletedCreationCLM m i * fockCompletedCreationCLM n j +
      fockCompletedCreationCLM n j * fockCompletedCreationCLM m i = 0 := by
  rw [fockCompletedCreationCLM_shift m k hmk i, fockCompletedCreationCLM_shift n k hnk j]
  exact fockCompleted_creation_cross k _ _

/-- Contractions born at different stages anticommute as well. -/
theorem fockCompleted_contraction_different_birth (m n k : ℕ) (hmk : m ≤ k) (hnk : n ≤ k)
    (i : Fin m) (j : Fin n) :
    fockCompletedContractionCLM m i * fockCompletedContractionCLM n j +
      fockCompletedContractionCLM n j * fockCompletedContractionCLM m i = 0 := by
  rw [fockCompletedContractionCLM_shift m k hmk i, fockCompletedContractionCLM_shift n k hnk j]
  exact fockCompleted_contraction_cross k _ _

/-- Mixed CAR compares different birth modes only after actual common-stage transport. -/
theorem fockCompleted_mixed_different_birth (m n k : ℕ) (hmk : m ≤ k) (hnk : n ≤ k)
    (i : Fin m) (j : Fin n) :
    fockCompletedContractionCLM m i * fockCompletedCreationCLM n j +
      fockCompletedCreationCLM n j * fockCompletedContractionCLM m i =
        if fockModeShift m k hmk i = fockModeShift n k hnk j then 1 else 0 := by
  rw [fockCompletedContractionCLM_shift m k hmk i, fockCompletedCreationCLM_shift n k hnk j]
  exact fockCompleted_mixed_cross k _ _

/-- The mixed-CAR identity operator coefficient is independent of the common upper stage. -/
theorem fockCompleted_mixed_coefficient_independent (m n k l : ℕ)
    (hmk : m ≤ k) (hnk : n ≤ k) (hml : m ≤ l) (hnl : n ≤ l) (i : Fin m) (j : Fin n) :
    (if fockModeShift m k hmk i = fockModeShift n k hnk j then
      (1 : RealFockCompletion →L[ℝ] RealFockCompletion) else 0) =
    (if fockModeShift m l hml i = fockModeShift n l hnl j then 1 else 0) := by
  simp only [fockModeShift_eq_iff_common m n k l hmk hnk hml hnl i j]

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
