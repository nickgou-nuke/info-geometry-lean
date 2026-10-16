/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
import InfoGeometry.QuantumContext.MatrixStageWeightedFunctionalColimit

/-!
# Extending a finite full-matrix functional to the tower colimit

Given a weighted trace functional at a selected matrix stage, this module
extends it to every stage: lower observables are pushed forward to the selected
stage, and higher weights are transported by the existing matrix embeddings.
The result descends through the existing categorical direct limit.  The
construction stays on the full noncommutative matrix carriers.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MatrixStageSelectedFunctional

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet

/-- A normalized trace paired with an arbitrary full-matrix weight. -/
def weightedMatrixTrace (n : ℕ) (D : MatrixStage n) :
    MatrixStage n →ₗ[ℂ] ℂ :=
  matrixTraceFunctional n ∘ₗ LinearMap.mulRight ℂ D

/-- The functional at stage `n` induced by a chosen full-matrix weight at
stage `k`.  Below `k` it evaluates the observable after the tower embedding;
above `k` it pairs with the embedded density. -/
def selectedStageFunctional (k : ℕ) (Dk : MatrixStage k) : StageFunctional :=
  fun n => if h : n ≤ k then
    (weightedMatrixTrace k Dk).comp (rawMap h).toAlgHom.toLinearMap
  else
    weightedMatrixTrace n (rawMap (Nat.le_of_not_ge h) Dk)

private theorem concreteStep_eq_rawMap_succ (n : ℕ) :
    concreteStep n = rawMap (Nat.le.step (le_refl n)) := by
  change concreteData.step n = map concreteData (Nat.le.step (le_refl n))
  rw [map_succ concreteData (le_refl n), map_id]
  rfl

/-- Compatibility at a single successor stage for the selected functional. -/
theorem selectedStageFunctional_step (k : ℕ) (Dk : MatrixStage k)
    (n : ℕ) (A : MatrixStage n) :
    selectedStageFunctional k Dk (n + 1) (concreteStep n A) =
      selectedStageFunctional k Dk n A := by
  by_cases hlow : n < k
  · have hn : n ≤ k := Nat.le_of_lt hlow
    have hn1 : n + 1 ≤ k := Nat.succ_le_of_lt hlow
    have hmap : rawMap hn1 (concreteStep n A) = rawMap hn A := by
      have hcomp := congrArg (fun f => f A)
        (concreteMap_comp (Nat.le.step (le_refl n)) hn1)
      have hstep : concreteStep n A =
          concreteMap (Nat.le.step (le_refl n)) A := by
        change concreteData.step n A = map concreteData (Nat.le.step (le_refl n)) A
        rw [map_succ concreteData (le_refl n), map_id]
        rfl
      have hmaps : concreteMap hn1
          (concreteMap (Nat.le.step (le_refl n)) A) =
          concreteMap (le_trans (Nat.le.step (le_refl n)) hn1) A := by
        simpa only [StarAlgHom.comp_apply] using hcomp
      change concreteMap hn1 (concreteStep n A) = concreteMap hn A
      have hmaps' : concreteMap hn1 (concreteStep n A) =
          concreteMap (le_trans (Nat.le.step (le_refl n)) hn1) A := by
        rw [hstep]
        exact hmaps
      simpa only [rawMap] using hmaps'
    simp [selectedStageFunctional, hn1, hn, hmap]
  · by_cases heq : n = k
    · subst k
      have hmap : rawMap (Nat.le_succ n) Dk = concreteStep n Dk := by
        have hproof : Nat.le_succ n = Nat.le.step (le_refl n) :=
          Subsingleton.elim _ _
        rw [hproof, ← concreteStep_eq_rawMap_succ]
      rw [selectedStageFunctional, dite_eq_right (by omega),
        selectedStageFunctional, dite_eq_left (by omega)]
      simp only [LinearMap.comp_apply, weightedMatrixTrace,
        LinearMap.mulRight_apply]
      have hraw : ((rawMap (le_refl n)).toAlgHom.toLinearMap) A = A := by
        simp [rawMap, concreteMap_id]
      rw [hraw]
      rw [hmap]
      calc
        matrixTraceFunctional (n + 1)
            (concreteStep n A * concreteStep n Dk) =
            matrixTraceFunctional (n + 1) (concreteStep n (A * Dk)) := by
              exact congrArg (matrixTraceFunctional (n + 1))
                ((concreteStep n).map_mul A Dk).symm
        _ = matrixTraceFunctional n (A * Dk) := by
              simpa [matrixTraceState, concreteData] using
                concreteData.trace_compatible n (A * Dk)
    · have hkn : k ≤ n := by omega
      have hkn1 : k ≤ n + 1 := Nat.le_trans hkn (Nat.le_succ n)
      have hmap : rawMap hkn1 Dk = concreteStep n (rawMap hkn Dk) := by
        have hs := map_succ concreteData hkn
        have hproof : hkn1 = Nat.le.step hkn := Subsingleton.elim _ _
        rw [hproof]
        change map concreteData (Nat.le.step hkn) Dk = _
        exact congrArg (fun f => f Dk) hs
      rw [selectedStageFunctional, dite_eq_right (by omega),
        selectedStageFunctional, dite_eq_right (by omega)]
      simp only [weightedMatrixTrace]
      rw [hmap]
      calc
        matrixTraceFunctional (n + 1)
            (concreteStep n A * concreteStep n (rawMap hkn Dk)) =
            matrixTraceFunctional (n + 1)
              (concreteStep n (A * rawMap hkn Dk)) := by
                exact congrArg (matrixTraceFunctional (n + 1))
                  ((concreteStep n).map_mul A (rawMap hkn Dk)).symm
        _ = matrixTraceFunctional n (A * rawMap hkn Dk) := by
                simpa [matrixTraceState, concreteData] using
                  concreteData.trace_compatible n (A * rawMap hkn Dk)

/-- A selected-stage functional is compatible with every transition in the
matrix tower. -/
theorem selectedStageFunctional_compatible (k : ℕ) (Dk : MatrixStage k) :
    Compatible (selectedStageFunctional k Dk) := by
  intro i j hij A
  induction hij with
  | refl => simp [rawMap, concreteMap_id]
  | @step j hij ih =>
      rw [show rawMap (Nat.le.step hij) A =
        concreteStep j (rawMap hij A) by
          simpa [rawMap, concreteData, concreteMap,
            InfoGeometry.Canonical.CuntzMatrixTraceTower.map_succ] using
            congrArg (fun f => f A)
              (InfoGeometry.Canonical.CuntzMatrixTraceTower.map_succ
                concreteData hij)]
      exact (selectedStageFunctional_step k Dk j (rawMap hij A)).trans ih

/-- The functional induced by the selected finite matrix on the categorical
direct limit of the full matrix tower. -/
def selectedStageColimitFunctional (k : ℕ) (Dk : MatrixStage k) :
    InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier →ₗ[ℂ] ℂ :=
  colimitFunctional (selectedStageFunctional k Dk)
    (selectedStageFunctional_compatible k Dk)

@[simp]
theorem selectedStageColimitFunctional_stage (k : ℕ) (Dk : MatrixStage k)
    (A : MatrixStage k) :
    selectedStageColimitFunctional k Dk (stageInjection k A) =
      matrixTraceFunctional k (A * Dk) := by
  change colimitFunctional (selectedStageFunctional k Dk)
    (selectedStageFunctional_compatible k Dk) (stageInjection k A) = _
  rw [colimitFunctional_stage]
  simp [selectedStageFunctional, weightedMatrixTrace, rawMap, concreteMap_id]

/-- A weight with normalized trace one induces a unital functional on the direct
limit. -/
theorem selectedStageColimitFunctional_one (k : ℕ) (Dk : MatrixStage k)
    (hD : matrixTraceFunctional k Dk = 1) :
    selectedStageColimitFunctional k Dk (1 :
      InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier) = 1 := by
  change colimitFunctional (selectedStageFunctional k Dk)
    (selectedStageFunctional_compatible k Dk)
    (1 : InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier) = 1
  have hstage : selectedStageFunctional k Dk k (1 : MatrixStage k) = 1 := by
    simpa [selectedStageFunctional, weightedMatrixTrace, rawMap,
      concreteMap_id] using hD
  have hreadout := colimitFunctional_stage
    (selectedStageFunctional k Dk) (selectedStageFunctional_compatible k Dk)
    k (1 : MatrixStage k)
  rw [DirectLimit.one_def k]
  simpa [stageInjection] using hreadout.trans hstage

end InfoGeometry.QuantumContext.MatrixStageSelectedFunctional

end
