/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.CarrierInnerModularFlow
import InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamilyPositivity

/-!
# Invariance of the selected colimit state under a fixed-seed inner action

The selected finite attention density determines a compatible family of full
matrix weights. The fixed-seed inner action preserves the resulting functional
on the entire algebraic direct limit. The proof represents each observable at
a common finite stage above both its own stage and the selected seed stage.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.CarrierInnerModularState

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.QuantumContext.AttentionStageColimitState
open InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow
open InfoGeometry.QuantumContext.CarrierInnerModularFlow
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional
open InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamily
open InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamilyPositivity

private theorem selectedFamily_eq_rawMap (k n : ℕ) (Dk : MatrixStage k)
    (hkn : k ≤ n) :
    selectedMatrixFamily k Dk n = rawMap hkn Dk := by
  by_cases h : n = k
  · subst n
    rw [selectedMatrixFamily_at_selected]
    simp [rawMap, concreteMap_id]
  · have hlt : k < n := Nat.lt_of_le_of_ne hkn (Ne.symm h)
    simp [selectedMatrixFamily, not_le_of_gt hlt]

private theorem trace_weighted_inner_conjugation
    (n : ℕ) (D U X Uinv : MatrixStage n)
    (hcomm : D * U = U * D)
    (hleft : Uinv * U = 1) :
    matrixTraceFunctional n (U * X * Uinv * D) =
      matrixTraceFunctional n (X * D) := by
  rw [matrixTraceFunctional_apply, matrixTraceFunctional_apply]
  congr 1
  calc
    Matrix.trace (U * X * Uinv * D) =
        Matrix.trace (U * (X * Uinv * D)) := by simp only [mul_assoc]
    _ = Matrix.trace ((X * Uinv * D) * U) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (X * Uinv * (D * U)) := by simp only [mul_assoc]
    _ = Matrix.trace (X * Uinv * (U * D)) := by rw [hcomm]
    _ = Matrix.trace (X * ((Uinv * U) * D)) := by simp only [mul_assoc]
    _ = Matrix.trace (X * D) := by rw [hleft, one_mul]

private theorem selectedFunctional_stage_readout
    (k n : ℕ) (Dk : MatrixStage k) (A : MatrixStage n) :
    selectedStageColimitFunctional k Dk (stageInjection n A) =
      matrixTraceFunctional n (A * selectedMatrixFamily k Dk n) := by
  change colimitFunctional (selectedStageFunctional k Dk)
      (selectedStageFunctional_compatible k Dk) (stageInjection n A) = _
  rw [colimitFunctional_stage]
  rw [selectedStageFunctional_eq_weightedSelectedFamily]
  exact weightedStageFunctional_apply (selectedMatrixFamily k Dk) n A

/-- The selected-stage state is invariant under the fixed-seed inner action on
every element of the genuine matrix direct-limit carrier. -/
theorem attentionColimitFunctional_carrierInnerAction_invariant
    (k : ℕ) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ)
    (x : InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier) :
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (carrierModularFlow k logits β t x) =
      selectedStageColimitFunctional k (attentionStageDensity k logits β) x := by
  induction x using DirectLimit.induction with
  | _ n A =>
      let m := max k n
      have hkm : k ≤ m := le_max_left k n
      have hnm : n ≤ m := le_max_right k n
      let U : MatrixStage m := rawMap hkm (modularUnitary logits β t)
      let Uinv : MatrixStage m := rawMap hkm (modularUnitary logits β (-t))
      let X : MatrixStage m := rawMap hnm A
      let D : MatrixStage m := selectedMatrixFamily k
        (attentionStageDensity k logits β) m
      have hD : D = rawMap hkm (attentionStageDensity k logits β) := by
        dsimp [D]
        exact selectedFamily_eq_rawMap k m _ hkm
      have hcomm : D * U = U * D := by
        rw [hD]
        dsimp [U]
        rw [← map_mul, ← map_mul,
          attentionStageDensity_comm_modularUnitary]
      have hleft : Uinv * U = 1 := by
        dsimp [U, Uinv]
        rw [← map_mul, modularUnitary_neg_mul, map_one]
      have hcarrier :
          carrierModularFlow k logits β t (stageInjection n A) =
            stageInjection m (U * X * Uinv) := by
        rw [show carrierModularFlow k logits β t (stageInjection n A) =
          carrierModularUnitary k logits β t * stageInjection n A *
            carrierModularUnitary k logits β (-t) by rfl]
        rw [show carrierModularUnitary k logits β t =
          stageInjection m U by
            dsimp [U, carrierModularUnitary]
            exact (stageInjection_transition hkm _).symm]
        rw [show carrierModularUnitary k logits β (-t) =
          stageInjection m Uinv by
            dsimp [Uinv, carrierModularUnitary]
            exact (stageInjection_transition hkm _).symm]
        rw [← stageInjection_transition hnm A]
        rw [← stageInjection_mul, ← stageInjection_mul]
      change selectedStageColimitFunctional k (attentionStageDensity k logits β)
          (carrierModularFlow k logits β t (stageInjection n A)) =
        selectedStageColimitFunctional k (attentionStageDensity k logits β)
          (stageInjection n A)
      rw [hcarrier]
      rw [← stageInjection_transition hnm A]
      change selectedStageColimitFunctional k (attentionStageDensity k logits β)
          (stageInjection m (U * X * Uinv)) =
        selectedStageColimitFunctional k (attentionStageDensity k logits β)
          (stageInjection m X)
      rw [selectedFunctional_stage_readout, selectedFunctional_stage_readout]
      dsimp [U, X, Uinv, D]
      exact trace_weighted_inner_conjugation m
        (selectedMatrixFamily k (attentionStageDensity k logits β) m)
        (rawMap hkm (modularUnitary logits β t))
        (rawMap hnm A)
        (rawMap hkm (modularUnitary logits β (-t)))
        hcomm hleft

end InfoGeometry.QuantumContext.CarrierInnerModularState

end
