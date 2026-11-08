/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MatrixStagePartialTrace
import InfoGeometry.QuantumContext.MatrixStageSelectedFunctional
import InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge

/-!
# Compatible full-matrix families from a selected tower stage

Given an arbitrary full matrix at stage `k`, construct a family across the
existing matrix tower. Below `k`, use the owned normalized partial trace;
above `k`, use the owned full-matrix embeddings. The family satisfies the
neighboring partial-trace compatibility law and therefore feeds the existing
canonical quotient-colimit functional. No positivity, Hermitian, or state
claim is made for an arbitrary selected matrix.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamily

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
open InfoGeometry.QuantumContext.MatrixStagePartialTrace
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional

/-- Restrict a selected full matrix to an earlier stage by tracing out one
matrix factor at each recursive step. -/
def restrictMatrixByPartialTrace (n k : ℕ) (Dk : MatrixStage k) (hnk : n ≤ k) :
    MatrixStage n :=
  if h : n = k then cast (congrArg MatrixStage h.symm) Dk
  else normalizedPartialTraceStep n
    (restrictMatrixByPartialTrace (n + 1) k Dk (by omega))
termination_by k - n
decreasing_by omega

/-- At the selected stage, recursive restriction returns the selected matrix. -/
theorem restrictMatrixByPartialTrace_eq (n k : ℕ) (Dk : MatrixStage k)
    (hnk : n ≤ k) (h : n = k) :
    restrictMatrixByPartialTrace n k Dk hnk =
      cast (congrArg MatrixStage h.symm) Dk := by
  rw [restrictMatrixByPartialTrace.eq_1]
  simp [h]

/-- Below the selected stage, restriction is one normalized partial-trace
step applied to the next member of the family. -/
theorem restrictMatrixByPartialTrace_succ (n k : ℕ) (hn : n < k)
    (Dk : MatrixStage k) :
    restrictMatrixByPartialTrace n k Dk (Nat.le_of_lt hn) =
      normalizedPartialTraceStep n
        (restrictMatrixByPartialTrace (n + 1) k Dk (by omega)) := by
  rw [restrictMatrixByPartialTrace.eq_1]
  rw [dite_eq_right (Nat.ne_of_lt hn)]

/-- Extend a selected full matrix to all stages by partial trace below its
stage and by the existing embeddings above it. -/
def selectedMatrixFamily (k : ℕ) (Dk : MatrixStage k) :
    ∀ n : ℕ, MatrixStage n := fun n =>
  if h : n ≤ k then restrictMatrixByPartialTrace n k Dk h
  else rawMap (Nat.le_of_not_ge h) Dk

/-- The family reads back the selected matrix at stage `k`. -/
theorem selectedMatrixFamily_at_selected (k : ℕ) (Dk : MatrixStage k) :
    selectedMatrixFamily k Dk k = Dk := by
  rw [selectedMatrixFamily, dite_eq_left (le_rfl : k ≤ k)]
  simpa using restrictMatrixByPartialTrace_eq k k Dk le_rfl rfl

/-- The successor law below the selected stage. -/
theorem selectedMatrixFamily_below_compatible (n k : ℕ) (hn : n < k)
    (Dk : MatrixStage k) :
    selectedMatrixFamily k Dk n =
      normalizedPartialTraceStep n (selectedMatrixFamily k Dk (n + 1)) := by
  have hn1 : n + 1 ≤ k := by omega
  rw [selectedMatrixFamily, dite_eq_left (Nat.le_of_lt hn),
      selectedMatrixFamily, dite_eq_left hn1]
  exact restrictMatrixByPartialTrace_succ n k hn Dk

/-- Above the selected stage, the composed embedding agrees with one
successor embedding. -/
theorem rawMap_successor (k n : ℕ) (hkn : k ≤ n) (Dk : MatrixStage k) :
    rawMap (Nat.le_trans hkn (Nat.le_succ n)) Dk =
      concreteStep n (rawMap hkn Dk) := by
  have hindex : Nat.le_trans hkn (Nat.le_succ n) = Nat.le.step hkn :=
    Subsingleton.elim _ _
  rw [hindex]
  have hmap := congrArg (fun f => f Dk) (map_succ concreteData hkn)
  simpa [rawMap, concreteData, concreteMap] using hmap

/-- The successor law above the selected stage follows from the partial
trace left-inverse theorem for the full-matrix embedding. -/
theorem selectedMatrixFamily_above_compatible (k n : ℕ) (hn : k < n)
    (Dk : MatrixStage k) :
    selectedMatrixFamily k Dk n =
      normalizedPartialTraceStep n (selectedMatrixFamily k Dk (n + 1)) := by
  have hkn : k ≤ n := Nat.le_of_lt hn
  have hkn1 : k ≤ n + 1 := Nat.le_trans hkn (Nat.le_succ n)
  have hraw := rawMap_successor k n hkn Dk
  rw [selectedMatrixFamily, dite_eq_right (not_le_of_gt hn),
      selectedMatrixFamily, dite_eq_right (not_le_of_gt (Nat.lt_succ_of_lt hn))]
  have hraw_rhs : rawMap
      (Nat.le_of_not_ge (not_le_of_gt (Nat.lt_succ_of_lt hn))) Dk =
      rawMap hkn1 Dk := by
    congr 1
  rw [hraw_rhs, hraw, normalizedPartialTraceStep_concreteStep]

/-- At the selected stage, compatibility follows from the partial-trace
left-inverse law applied to the first embedded successor. -/
theorem selectedMatrixFamily_boundary_compatible (k : ℕ) (Dk : MatrixStage k) :
    selectedMatrixFamily k Dk k =
      normalizedPartialTraceStep k (selectedMatrixFamily k Dk (k + 1)) := by
  rw [selectedMatrixFamily_at_selected]
  have hraw : rawMap (Nat.le_succ k) Dk = concreteStep k Dk := by
    have hraw' := rawMap_successor k k le_rfl Dk
    have hself : rawMap (le_rfl : k ≤ k) Dk = Dk := by
      simp [rawMap, concreteMap_id]
    rw [hself] at hraw'
    exact hraw'
  rw [show selectedMatrixFamily k Dk (k + 1) = rawMap (Nat.le_succ k) Dk by
        simp [selectedMatrixFamily]]
  rw [hraw, normalizedPartialTraceStep_concreteStep]

/-- The selected full-matrix family satisfies the owner’s exact neighboring
normalized-partial-trace compatibility predicate. -/
theorem selectedMatrixFamily_partialTraceCompatible (k : ℕ)
    (Dk : MatrixStage k) : PartialTraceCompatible (selectedMatrixFamily k Dk) := by
  intro n
  by_cases hlow : n < k
  · exact selectedMatrixFamily_below_compatible n k hlow Dk
  · by_cases hup : k < n
    · exact selectedMatrixFamily_above_compatible k n hup Dk
    · have heq : n = k := by omega
      subst n
      exact selectedMatrixFamily_boundary_compatible k Dk

/-- Normalized trace is constant across the selected family. This follows
from the trace-adjoint compatibility already owned by the partial-trace
module; it does not assert positivity. -/
theorem selectedMatrixFamily_trace_eq_selected (k n : ℕ) (Dk : MatrixStage k) :
    matrixTraceFunctional n (selectedMatrixFamily k Dk n) =
      matrixTraceFunctional k Dk := by
  have hweighted : WeightedCompatible (selectedMatrixFamily k Dk) :=
    weightedStageFunctional_compatible_of_partialTraceCompatible
      (selectedMatrixFamily k Dk) (selectedMatrixFamily_partialTraceCompatible k Dk)
  by_cases hnk : n ≤ k
  · have h := hweighted (i := n) (j := k) hnk (1 : MatrixStage n)
    have hone : rawMap hnk (1 : MatrixStage n) = (1 : MatrixStage k) := by
      simp [rawMap]
    rw [hone] at h
    simpa [weightedStageFunctional_apply, selectedMatrixFamily_at_selected] using h.symm
  · have hkn : k ≤ n := by omega
    have h := hweighted (i := k) (j := n) hkn (1 : MatrixStage k)
    have hone : rawMap hkn (1 : MatrixStage k) = (1 : MatrixStage n) := by
      simp [rawMap]
    rw [hone] at h
    simpa [weightedStageFunctional_apply, selectedMatrixFamily_at_selected] using h

/-- A normalized selected matrix gives a normalized trace at every stage of
the recursively extended family. -/
theorem selectedMatrixFamily_trace_eq_one (k n : ℕ) (Dk : MatrixStage k)
    (hD : matrixTraceFunctional k Dk = 1) :
    matrixTraceFunctional n (selectedMatrixFamily k Dk n) = 1 := by
  rw [selectedMatrixFamily_trace_eq_selected]
  exact hD

/-- The selected family induces the existing functional on the canonical
BitWord matrix quotient colimit. -/
def selectedMatrixFamilyColimitFunctional (k : ℕ) (Dk : MatrixStage k) :
    MatrixStageLimit → ℂ :=
  partialTraceCompatibleColimitFunctional (selectedMatrixFamily k Dk)
    (selectedMatrixFamily_partialTraceCompatible k Dk)

/-- Finite-stage readout for the functional induced by the selected family. -/
@[simp]
theorem selectedMatrixFamilyColimitFunctional_stage (k n : ℕ)
    (Dk : MatrixStage k) (A : InfoGeometry.Canonical.ComplexMatrixStage.Stage n) :
    selectedMatrixFamilyColimitFunctional k Dk
      (canonicalStageHom n A) =
        matrixTraceFunctional n
          (stageStarAlgEquiv n A * selectedMatrixFamily k Dk n) := by
  exact partialTraceCompatibleColimitFunctional_stage
    (selectedMatrixFamily k Dk) (selectedMatrixFamily_partialTraceCompatible k Dk)
    n A

/-- The induced quotient-colimit functional is unital when the selected
full matrix has normalized trace one. -/
theorem selectedMatrixFamilyColimitFunctional_one (k : ℕ) (Dk : MatrixStage k)
    (hD : matrixTraceFunctional k Dk = 1) :
    selectedMatrixFamilyColimitFunctional k Dk (1 : MatrixStageLimit) = 1 := by
  rw [← map_one (canonicalStageHom k), selectedMatrixFamilyColimitFunctional_stage]
  simpa [selectedMatrixFamily_at_selected] using hD

end InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamily

end
