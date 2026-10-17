/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.CarrierInnerKMSBoundary
import InfoGeometry.QuantumContext.AttentionGNSWeightedAdjoint
import Mathlib.Tactic.NoncommRing

/-!
# Selected-state algebraic GNS-pairing identity on the matrix direct limit

For one fixed finite attention seed and one fixed full matrix `C` at that
seed stage, congruence by the image of `C` satisfies an explicit algebraic
weighted GNS-pairing identity for the selected colimit functional. The
statement is about the existing algebraic direct limit of full complex matrix
stages; it does not assert a bounded Hilbert-space adjoint. It also does not
assert that either map is a channel or that the pairing map is the standard
CPTP Petz recovery map.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.AttentionSelectedColimitGNSAdjoint

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.QuantumContext.AttentionStageColimitState
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.CarrierInnerKMSBoundary
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional
open InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamily
open InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamilyPositivity

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

private theorem attentionStageDensityInv_mul_local (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    attentionStageDensityInv k logits β *
      attentionStageDensity k logits β = 1 := by
  dsimp [attentionStageDensityInv, attentionStageDensity]
  rw [Matrix.diagonal_mul_diagonal]
  have hdiag :
      (fun i => ((2 ^ k : ℂ) * (AttentionKMSState.softmaxWeight logits β i : ℂ))⁻¹ *
        ((2 ^ k : ℂ) * (AttentionKMSState.softmaxWeight logits β i : ℂ))) = fun _ => 1 := by
    funext i
    apply inv_mul_cancel₀
    apply mul_ne_zero
    · norm_cast
      exact pow_ne_zero k (by norm_num)
    · exact_mod_cast (ne_of_gt (AttentionKMSState.softmaxWeight_pos logits β i))
  rw [hdiag]
  exact Matrix.diagonal_one

private theorem complex_matrix_gns_congruence_adjoint
    (n : ℕ) (C ρ ρinv X Y : MatrixStage n)
    (hinv : ρinv * ρ = 1) :
    Matrix.trace (star (star C * X * C) * Y * ρ) =
      Matrix.trace (star X * (C * Y * ρ * star C * ρinv) * ρ) := by
  have hleft :
      Matrix.trace (star C * star X * C * Y * ρ) =
        Matrix.trace (star X * C * Y * ρ * star C) := by
    calc
      Matrix.trace (star C * star X * C * Y * ρ) =
          Matrix.trace ((star C * star X * C * Y) * ρ) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (ρ * (star C * star X * C * Y)) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((ρ * star C) * (star X * C * Y)) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((star X * C * Y) * (ρ * star C)) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace (star X * C * Y * ρ * star C) := by
            simp only [Matrix.mul_assoc]
  have hright :
      Matrix.trace (star X * (C * Y * ρ * star C * ρinv) * ρ) =
        Matrix.trace (star X * C * Y * ρ * star C) := by
    calc
      Matrix.trace (star X * (C * Y * ρ * star C * ρinv) * ρ) =
          Matrix.trace ((star X * C * Y * ρ * star C) * (ρinv * ρ)) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((star X * C * Y * ρ * star C) * 1) := by rw [hinv]
      _ = Matrix.trace (star X * C * Y * ρ * star C) := by simp
  calc
    Matrix.trace (star (star C * X * C) * Y * ρ) =
        Matrix.trace (star C * star X * C * Y * ρ) := by
          simp only [star_mul, star_star]
          congr 1
          noncomm_ring
    _ = Matrix.trace (star X * C * Y * ρ * star C) := hleft
    _ = Matrix.trace (star X * (C * Y * ρ * star C * ρinv) * ρ) := hright.symm

/--
For a fixed selected softmax density at stage `k`, let `C` be any full
complex matrix at that stage. On the full noncommutative direct-limit carrier,
congruence `x ↦ C* x C` and the map `y ↦ C y ρ C* ρ⁻¹` satisfy the algebraic
weighted GNS-pairing identity. This is not a bounded Hilbert-space adjoint
claim.

The inverse is the explicit diagonal inverse of the selected finite density;
the formula transports to every common upper stage through the actual tower
maps. No compatibility of independently varying logits or matrices is
assumed.
-/
theorem attentionSelectedColimit_congruence_pairing_adjointIdentity
    (k : ℕ) (logits : Fin (2 ^ k) → ℝ) (β : ℝ)
    (C : MatrixStage k)
    (x y : InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier) :
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (star (stageInjection k C) * star x * stageInjection k C * y) =
      selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (star x * (stageInjection k C * y *
          stageInjection k (attentionStageDensity k logits β) *
          star (stageInjection k C) *
          stageInjection k (attentionStageDensityInv k logits β))) := by
  induction x, y using DirectLimit.induction₂ with
  | _ n A B =>
      let m := max k n
      have hkm : k ≤ m := le_max_left k n
      have hnm : n ≤ m := le_max_right k n
      let X : MatrixStage m := rawMap hnm A
      let Y : MatrixStage m := rawMap hnm B
      let C' : MatrixStage m := rawMap hkm C
      let ρ : MatrixStage m := rawMap hkm (attentionStageDensity k logits β)
      let ρinv : MatrixStage m := rawMap hkm
        (attentionStageDensityInv k logits β)
      have hinv : ρinv * ρ = 1 := by
        dsimp [ρinv, ρ]
        rw [← map_mul, attentionStageDensityInv_mul_local, map_one]
      have hX : stageInjection n A = stageInjection m X := by
        dsimp [X]
        exact (stageInjection_transition hnm A).symm
      have hY : stageInjection n B = stageInjection m Y := by
        dsimp [Y]
        exact (stageInjection_transition hnm B).symm
      have hC : stageInjection k C = stageInjection m C' := by
        dsimp [C']
        exact (stageInjection_transition hkm C).symm
      have hρ : stageInjection k (attentionStageDensity k logits β) =
          stageInjection m ρ := by
        dsimp [ρ]
        exact (stageInjection_transition hkm _).symm
      have hρinv : stageInjection k (attentionStageDensityInv k logits β) =
          stageInjection m ρinv := by
        dsimp [ρinv]
        exact (stageInjection_transition hkm _).symm
      change selectedStageColimitFunctional k (attentionStageDensity k logits β)
          (star (stageInjection k C) * star (stageInjection n A) *
            stageInjection k C * stageInjection n B) =
        selectedStageColimitFunctional k (attentionStageDensity k logits β)
          (star (stageInjection n A) *
            (stageInjection k C * stageInjection n B *
              stageInjection k (attentionStageDensity k logits β) *
              star (stageInjection k C) *
              stageInjection k (attentionStageDensityInv k logits β)))
      rw [hX, hY, hC, hρ, hρinv]
      have hleft :
          star (stageInjection m C') * star (stageInjection m X) *
            stageInjection m C' * stageInjection m Y =
          stageInjection m (star (star C' * X * C') * Y) := by
        calc
          star (stageInjection m C') * star (stageInjection m X) *
              stageInjection m C' * stageInjection m Y =
            stageInjection m (star C' * star X * C' * Y) := by
                rw [← stageInjection_star m C', ← stageInjection_star m X]
                simp only [← stageInjection_mul]
          _ = stageInjection m (star (star C' * X * C') * Y) := by
                congr 1
                simp only [star_mul, star_star]
                noncomm_ring
      have hright :
          star (stageInjection m X) *
            (stageInjection m C' * stageInjection m Y *
              stageInjection m ρ * star (stageInjection m C') *
              stageInjection m ρinv) =
          stageInjection m
            (star X * (C' * Y * ρ * star C' * ρinv)) := by
        simp only [map_mul, map_star]
      rw [hleft, hright]
      rw [selectedFunctional_stage_readout,
        selectedFunctional_stage_readout]
      rw [selectedFamily_eq_rawMap k m
        (attentionStageDensity k logits β) hkm]
      change matrixTraceFunctional m
          (star (star C' * X * C') * Y * rawMap hkm
            (attentionStageDensity k logits β)) =
        matrixTraceFunctional m
          (star X * (C' * Y * rawMap hkm (attentionStageDensity k logits β) *
            star C' * ρinv) * rawMap hkm (attentionStageDensity k logits β))
      rw [matrixTraceFunctional_apply, matrixTraceFunctional_apply]
      dsimp [C', X, Y, ρ, ρinv]
      exact congrArg (fun z : ℂ => (1 / (2 ^ m : ℂ)) * z)
        (complex_matrix_gns_congruence_adjoint m
          (rawMap hkm C)
          (rawMap hkm (attentionStageDensity k logits β))
          (rawMap hkm (attentionStageDensityInv k logits β))
          (rawMap hnm A) (rawMap hnm B) hinv)

end InfoGeometry.QuantumContext.AttentionSelectedColimitGNSAdjoint

end
