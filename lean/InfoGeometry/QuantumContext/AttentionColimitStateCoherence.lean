/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AttentionTowerCompatibility
import InfoGeometry.QuantumContext.MatrixStageSelectedFunctional

/-!
# Coherence of selected attention functionals on the matrix direct limit

If adjacent finite density matrices are related by the actual dyadic matrix
successor embedding, their selected-stage weighted-trace functionals agree on
the algebraic direct-limit carrier. The attention specialization uses the
duplicated-logit transport already proved on the full matrix tower.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.AttentionColimitStateCoherence

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.QuantumContext.AttentionStageColimitState
open InfoGeometry.QuantumContext.AttentionTowerCompatibility
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional

/-- A selected-stage functional is unchanged when its matrix weight is moved
to a later stage by the actual tower embedding. -/
theorem selectedStageColimitFunctional_transport_eq
    {k n : ℕ} (h : k ≤ n) (Dk : MatrixStage k) :
    selectedStageColimitFunctional n (concreteMap h Dk) =
      selectedStageColimitFunctional k Dk := by
  unfold selectedStageColimitFunctional
  apply colimitFunctional_eq_of_stage_eq
    (selectedStageFunctional n (concreteMap h Dk))
    (selectedStageFunctional k Dk)
    (selectedStageFunctional_compatible n (concreteMap h Dk))
    (selectedStageFunctional_compatible k Dk)
  intro m A
  let t := m + (n + k + 2)
  have hmt : m ≤ t := by
    dsimp [t]
    omega
  have hnt : n ≤ t := by
    dsimp [t]
    omega
  have hkt : k ≤ t := by
    dsimp [t]
    omega
  have hnotn : ¬ t ≤ n := by
    dsimp [t]
    omega
  have hnotk : ¬ t ≤ k := by
    dsimp [t]
    omega
  have hcomp := congrArg (fun f => f Dk) (concreteMap_comp h hnt)
  have hcomp' : concreteMap hnt (concreteMap h Dk) =
      concreteMap (le_trans h hnt) Dk := by
    simpa only [StarAlgHom.comp_apply] using hcomp
  have hproof : le_trans h hnt = hkt := Subsingleton.elim _ _
  rw [hproof] at hcomp'
  have hweight : rawMap hnt (concreteMap h Dk) = rawMap hkt Dk := by
    simpa only [rawMap] using hcomp'
  have hmid :
      selectedStageFunctional n (concreteMap h Dk) t (rawMap hmt A) =
        selectedStageFunctional k Dk t (rawMap hmt A) := by
    simp [selectedStageFunctional, hnotn, hnotk, weightedMatrixTrace,
      LinearMap.comp_apply, LinearMap.mulRight_apply, hweight]
  calc
    selectedStageFunctional n (concreteMap h Dk) m A =
        selectedStageFunctional n (concreteMap h Dk) t (rawMap hmt A) :=
          (selectedStageFunctional_compatible n (concreteMap h Dk) hmt A).symm
    _ = selectedStageFunctional k Dk t (rawMap hmt A) := hmid
    _ = selectedStageFunctional k Dk m A :=
          selectedStageFunctional_compatible k Dk hmt A

/-- Adjacent selected-stage weighted-trace functionals on the algebraic
matrix direct limit agree whenever their weights are related by the successor
*-algebra embedding. -/
theorem selectedStageColimitFunctional_succ_eq
    (k : ℕ) (Dk : MatrixStage k) (Dk1 : MatrixStage (k + 1))
    (hstep : Dk1 = concreteStep k Dk) :
    selectedStageColimitFunctional (k + 1) Dk1 =
      selectedStageColimitFunctional k Dk := by
  unfold selectedStageColimitFunctional
  apply colimitFunctional_eq_of_stage_eq
    (selectedStageFunctional (k + 1) Dk1)
    (selectedStageFunctional k Dk)
    (selectedStageFunctional_compatible (k + 1) Dk1)
    (selectedStageFunctional_compatible k Dk)
  intro n A
  let t := n + (k + 2)
  have hnt : n ≤ t := by
    dsimp [t]
    omega
  have hk1t : k + 1 ≤ t := by
    dsimp [t]
    omega
  have hkt : k ≤ t := le_trans (Nat.le_succ k) hk1t
  have hnotk : ¬ t ≤ k := by
    dsimp [t]
    omega
  have hnotk1 : ¬ t ≤ k + 1 := by
    dsimp [t]
    omega
  have hstepMap : concreteStep k Dk =
      rawMap (Nat.le.step (le_refl k)) Dk := by
    change concreteData.step k Dk =
      map concreteData (Nat.le.step (le_refl k)) Dk
    rw [map_succ concreteData (le_refl k), map_id]
    rfl
  have hweight : rawMap hk1t Dk1 = rawMap hkt Dk := by
    rw [hstep, hstepMap]
    have hcomp := congrArg (fun f => f Dk)
      (concreteMap_comp (Nat.le.step (le_refl k)) hk1t)
    have hcomp' : concreteMap hk1t
        (concreteMap (Nat.le.step (le_refl k)) Dk) =
          concreteMap (le_trans (Nat.le.step (le_refl k)) hk1t) Dk := by
      simpa only [StarAlgHom.comp_apply] using hcomp
    have hproof : le_trans (Nat.le.step (le_refl k)) hk1t = hkt :=
      Subsingleton.elim _ _
    rw [hproof] at hcomp'
    simpa only [rawMap] using hcomp'
  have hmid :
      selectedStageFunctional (k + 1) Dk1 t (rawMap hnt A) =
        selectedStageFunctional k Dk t (rawMap hnt A) := by
    simp [selectedStageFunctional, hnotk1, hnotk, weightedMatrixTrace,
      LinearMap.comp_apply, LinearMap.mulRight_apply, hweight]
  calc
    selectedStageFunctional (k + 1) Dk1 n A =
        selectedStageFunctional (k + 1) Dk1 t (rawMap hnt A) :=
          (selectedStageFunctional_compatible (k + 1) Dk1 hnt A).symm
    _ = selectedStageFunctional k Dk t (rawMap hnt A) := hmid
    _ = selectedStageFunctional k Dk n A :=
          selectedStageFunctional_compatible k Dk hnt A

/-- With duplicated logits, the selected attention functionals at adjacent
stages define the same linear functional on the algebraic matrix direct
limit. -/
theorem attentionColimitFunctional_lift_compatible (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    selectedStageColimitFunctional (k + 1)
        (attentionStageDensity (k + 1) (liftLogits k logits) β) =
      selectedStageColimitFunctional k (attentionStageDensity k logits β) := by
  exact selectedStageColimitFunctional_succ_eq k
    (attentionStageDensity k logits β)
    (attentionStageDensity (k + 1) (liftLogits k logits) β)
    (attentionStageDensity_lift_compatible k logits β)

end InfoGeometry.QuantumContext.AttentionColimitStateCoherence

end noncomputable section
