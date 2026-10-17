/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.CarrierInnerModularState

/-!
# Algebraic KMS boundary identity on the attention matrix direct limit

For a fixed finite attention seed, its scaled density and explicit inverse
embed into the noncommutative matrix direct limit. The selected colimit
functional satisfies the corresponding algebraic trace-cycling boundary
identity for arbitrary carrier elements. This is an algebraic identity; no
analytic continuation or completed operator-algebra claim is made.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.CarrierInnerKMSBoundary

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.QuantumContext.AttentionStageColimitState
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional
open InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamily
open InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamilyPositivity
open InfoGeometry.QuantumContext.CarrierInnerModularState

/-- The explicit inverse of the dimension-scaled finite attention density. -/
def attentionStageDensityInv (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) : MatrixStage k :=
  Matrix.diagonal (fun i =>
    ((2 ^ k : ℂ) * (softmaxWeight logits β i : ℂ))⁻¹)

private theorem attentionStageDensityInv_mul (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    attentionStageDensityInv k logits β *
      attentionStageDensity k logits β = 1 := by
  dsimp [attentionStageDensityInv, attentionStageDensity]
  rw [Matrix.diagonal_mul_diagonal]
  have hdiag :
      (fun i => ((2 ^ k : ℂ) * (softmaxWeight logits β i : ℂ))⁻¹ *
        ((2 ^ k : ℂ) * (softmaxWeight logits β i : ℂ))) = fun _ => 1 := by
    funext i
    apply inv_mul_cancel₀
    apply mul_ne_zero
    · norm_cast
      exact pow_ne_zero k (by norm_num)
    · exact_mod_cast (ne_of_gt (softmaxWeight_pos logits β i))
  rw [hdiag]
  exact Matrix.diagonal_one

private theorem complex_matrix_trace_kms
    (n : ℕ) (ρ ρinv A B : MatrixStage n)
    (hinv : ρinv * ρ = 1) :
    Matrix.trace (ρ * A * (ρ * B * ρinv)) =
      Matrix.trace (ρ * B * A) := by
  calc
    Matrix.trace (ρ * A * (ρ * B * ρinv)) =
        Matrix.trace ((ρ * A * ρ * B) * ρinv) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (ρinv * (ρ * A * ρ * B)) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((ρinv * ρ) * (A * ρ * B)) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (1 * (A * ρ * B)) := by rw [hinv]
    _ = Matrix.trace (A * (ρ * B)) := by
          rw [Matrix.one_mul, Matrix.mul_assoc]
    _ = Matrix.trace ((ρ * B) * A) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (ρ * B * A) := by
          simp only [Matrix.mul_assoc]

private theorem selectedFunctional_stage_readout
    (k n : ℕ) (Dk : MatrixStage k) (A : MatrixStage n) :
    selectedStageColimitFunctional k Dk (stageInjection n A) =
      matrixTraceFunctional n (A * selectedMatrixFamily k Dk n) := by
  change colimitFunctional (selectedStageFunctional k Dk)
      (selectedStageFunctional_compatible k Dk) (stageInjection n A) = _
  rw [colimitFunctional_stage]
  rw [selectedStageFunctional_eq_weightedSelectedFamily]
  exact weightedStageFunctional_apply (selectedMatrixFamily k Dk) n A

private theorem selectedFamily_eq_rawMap (k n : ℕ) (Dk : MatrixStage k)
    (hkn : k ≤ n) :
    selectedMatrixFamily k Dk n = rawMap hkn Dk := by
  by_cases h : n = k
  · subst n
    rw [selectedMatrixFamily_at_selected]
    simp [rawMap, concreteMap_id]
  · have hlt : k < n := Nat.lt_of_le_of_ne hkn (Ne.symm h)
    simp [selectedMatrixFamily, not_le_of_gt hlt]

private theorem weighted_trace_kms
    (n : ℕ) (ρ ρinv A B : MatrixStage n)
    (hinv : ρinv * ρ = 1) :
    matrixTraceFunctional n (A * (ρ * B * ρinv) * ρ) =
      matrixTraceFunctional n (B * A * ρ) := by
  rw [matrixTraceFunctional_apply, matrixTraceFunctional_apply]
  congr 1
  calc
    Matrix.trace (A * (ρ * B * ρinv) * ρ) =
        Matrix.trace ((A * (ρ * B * ρinv)) * ρ) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (ρ * (A * (ρ * B * ρinv))) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (ρ * A * (ρ * B * ρinv)) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (ρ * B * A) := complex_matrix_trace_kms n ρ ρinv A B hinv
    _ = Matrix.trace (ρ * (B * A)) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((B * A) * ρ) := by
          rw [Matrix.trace_mul_comm]

/-- The selected attention colimit functional satisfies the algebraic KMS
boundary trace-cycling identity on arbitrary elements of the full matrix
direct-limit carrier. -/
theorem attentionColimitFunctional_carrier_kms_boundary
    (k : ℕ) (logits : Fin (2 ^ k) → ℝ) (β : ℝ)
    (x y : InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier) :
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (x * (stageInjection k (attentionStageDensity k logits β) * y *
          stageInjection k (attentionStageDensityInv k logits β))) =
      selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (y * x) := by
  induction x, y using DirectLimit.induction₂ with
  | _ n A B =>
      let m := max k n
      have hkm : k ≤ m := le_max_left k n
      have hnm : n ≤ m := le_max_right k n
      let X : MatrixStage m := rawMap hnm A
      let Y : MatrixStage m := rawMap hnm B
      let ρ : MatrixStage m := rawMap hkm (attentionStageDensity k logits β)
      let ρinv : MatrixStage m := rawMap hkm (attentionStageDensityInv k logits β)
      have hinv : ρinv * ρ = 1 := by
        dsimp [ρinv, ρ]
        rw [← map_mul, attentionStageDensityInv_mul, map_one]
      have hX : stageInjection n A = stageInjection m X := by
        dsimp [X]
        exact (stageInjection_transition hnm A).symm
      have hY : stageInjection n B = stageInjection m Y := by
        dsimp [Y]
        exact (stageInjection_transition hnm B).symm
      have hρ :
          stageInjection k (attentionStageDensity k logits β) =
            stageInjection m ρ := by
        dsimp [ρ]
        exact (stageInjection_transition hkm _).symm
      have hρinv :
          stageInjection k (attentionStageDensityInv k logits β) =
            stageInjection m ρinv := by
        dsimp [ρinv]
        exact (stageInjection_transition hkm _).symm
      change selectedStageColimitFunctional k
          (attentionStageDensity k logits β)
          (stageInjection n A *
            (stageInjection k (attentionStageDensity k logits β) *
              stageInjection n B *
              stageInjection k (attentionStageDensityInv k logits β))) =
        selectedStageColimitFunctional k (attentionStageDensity k logits β)
          (stageInjection n B * stageInjection n A)
      rw [hX, hY, hρ, hρinv]
      have hprod :
          stageInjection m (X * (ρ * Y * ρinv)) =
            stageInjection m X *
              (stageInjection m ρ * stageInjection m Y *
                stageInjection m ρinv) := by
        simp only [map_mul]
      have hprod' :
          stageInjection m (Y * X) =
            stageInjection m Y * stageInjection m X := by
        exact (stageInjection m).map_mul Y X
      rw [← hprod, ← hprod']
      rw [selectedFunctional_stage_readout,
        selectedFunctional_stage_readout]
      dsimp [X, Y, ρ, ρinv]
      rw [selectedFamily_eq_rawMap k m
        (attentionStageDensity k logits β) hkm]
      exact weighted_trace_kms m
        (rawMap hkm (attentionStageDensity k logits β))
        (rawMap hkm (attentionStageDensityInv k logits β))
        (rawMap hnm A) (rawMap hnm B) hinv

end InfoGeometry.QuantumContext.CarrierInnerKMSBoundary

end
