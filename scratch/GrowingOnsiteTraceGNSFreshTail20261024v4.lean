/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GrowingOnsiteTraceGNSFamily
import InfoGeometry.Canonical.FilteredCompatibleOperatorNorm
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Fresh-tail action survives the native trace-GNS completion

Faithfulness of the actual finite trace detects nonzero representative vectors.
The existing isometric stage inclusion preserves them in the completed Hilbert
colimit. Geometric weights give nonzero fresh action at every stage and the
proved stage and completed operator norm bounds two, for the same growing onsite family.
The family owner import is a pending native dependency of this draft.
-/
noncomputable section
open scoped ComplexOrder

namespace InfoGeometry.Canonical.GrowingOnsiteTraceGNSFreshTail

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CuntzMatrixTowerInstantiation CantorBernoulliCStarMatrixTraceState
open GrowingOnsiteMatrixHamiltonian GrowingOnsiteMatrixNorm GrowingOnsiteTraceGNSFamily
open FilteredIsometricHilbertCompletion

private abbrev matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))
private abbrev matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))
private abbrev matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))
attribute [local instance] matrixStageCStarFamily matrixStageOrderFamily matrixStageStarOrderFamily

local notation "E" => GNSStage CStarMatrixStage cstarMatrixInductiveSystem cstarMatrixTraceStateFamily
local notation "S" => filteredGNSIsometricDirectSystem CStarMatrixStage
  cstarMatrixInductiveSystem cstarMatrixTraceStateFamily

/-- Native completion preserves the seminorm detected by a faithful positive functional. -/
private theorem faithful_toGNS_ne_zero {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ)
    (hfaith : ∀ a : A, f (star a * a) = 0 → a = 0)
    (a : A) (ha : a ≠ 0) : (f.toPreGNS a : f.GNS) ≠ 0 := by
  intro hzero
  have hn : ‖(f.toPreGNS a : f.PreGNS)‖ = 0 := by
    have h := congrArg (fun z : f.GNS => ‖z‖) hzero
    simpa only [UniformSpace.Completion.norm_coe, norm_zero] using h
  have hs := f.preGNS_norm_sq (f.toPreGNS a)
  have hf : f (star a * a) = 0 := by
    simpa only [PositiveLinearMap.ofPreGNS_toPreGNS, hn, Complex.ofReal_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0)] using hs.symm
  exact ha (hfaith a hf)

/-- Faithful trace, not representation injectivity alone, detects these vectors. -/
theorem traceGNS_representative_ne_zero (n : ℕ) (A : CStarMatrixStage n) (hA : A ≠ 0) :
    ((cstarMatrixTraceState n).functional.toPreGNS A :
      (cstarMatrixTraceState n).functional.GNS) ≠ 0 := by
  exact faithful_toGNS_ne_zero (cstarMatrixTraceState n).functional
    (fun a ha => (cstarMatrixTraceState_faithful n a).mp ha) A hA

/-- Existing fresh switch matrix transported through the native type-copy equivalence. -/
def cstarTailX (n : ℕ) : CStarMatrixStage (n + 1) :=
  CStarMatrix.ofMatrixStarAlgEquiv (tailX n)

theorem cstar_fresh_commutator_ne_zero (w : ℕ → ℝ) (n : ℕ) (hw : w n ≠ 0) :
    cstarOnsiteHamiltonian w (n + 1) * cstarTailX n -
      cstarTailX n * cstarOnsiteHamiltonian w (n + 1) ≠ 0 := by
  intro hz
  apply onsite_fresh_tail_action_ne_zero w n hw
  have hraw := congrArg
    (CStarMatrix.ofMatrixStarAlgEquiv :
      MatrixStage (n + 1) ≃⋆ₐ[ℂ] CStarMatrixStage (n + 1)).symm hz
  change onsiteHamiltonian w (n + 1) * tailX n -
    tailX n * onsiteHamiltonian w (n + 1) = 0 at hraw
  exact hraw

/-- The growing stage operator acts nontrivially on the actual fresh-tail vector. -/
theorem onsiteStageOperator_fresh_ne_zero (w : ℕ → ℝ) (n : ℕ) (hw : w n ≠ 0) :
    onsiteStageOperator w (n + 1)
      ((cstarMatrixTraceState (n + 1)).functional.toPreGNS (cstarTailX n) :
        (cstarMatrixTraceState (n + 1)).functional.GNS) ≠ 0 := by
  change (cstarMatrixTraceState (n + 1)).functional.tracialCommutatorGNS
    (cstarTrace_cyclic (n + 1)) (cstarOnsiteHamiltonian w (n + 1))
    ((cstarMatrixTraceState (n + 1)).functional.toPreGNS (cstarTailX n) :
        (cstarMatrixTraceState (n + 1)).functional.GNS) ≠ 0
  rw [PositiveLinearMap.tracialCommutatorGNS_toPreGNS]
  exact traceGNS_representative_ne_zero (n + 1) _ (cstar_fresh_commutator_ne_zero w n hw)

/-- Native isometric inclusion carries nonzero fresh action into the same Hilbert colimit. -/
theorem onsiteCompletedOperator_fresh_ne_zero (w : ℕ → ℝ)
    (hw : Summable (fun j => |w j|)) (n : ℕ) (hwn : w n ≠ 0) :
    onsiteCompletedOperator w hw
      (stageToHilbertDirectLimit E S (n + 1)
        ((cstarMatrixTraceState (n + 1)).functional.toPreGNS (cstarTailX n) :
        (cstarMatrixTraceState (n + 1)).functional.GNS)) ≠ 0 := by
  let x : E (n + 1) :=
    ((cstarMatrixTraceState (n + 1)).functional.toPreGNS (cstarTailX n) :
      (cstarMatrixTraceState (n + 1)).functional.GNS)
  have hread := onsiteCompletedOperator_stage w hw (n + 1) x
  change onsiteCompletedOperator w hw (stageToHilbertDirectLimit E S (n + 1) x) =
    stageToHilbertDirectLimit E S (n + 1) (onsiteStageOperator w (n + 1) x) at hread
  have hne : onsiteStageOperator w (n + 1) x ≠ 0 :=
    onsiteStageOperator_fresh_ne_zero w n hwn
  intro hz
  have hz' : onsiteCompletedOperator w hw
      (stageToHilbertDirectLimit E S (n + 1) x) = 0 := hz
  have himg : stageToHilbertDirectLimit E S (n + 1)
      (onsiteStageOperator w (n + 1) x) = 0 := hread.symm.trans hz'
  apply hne
  apply (stageToHilbertDirectLimit E S (n + 1)).injective
  simpa only [map_zero] using himg

/-- Nonterminating weights for the genuine growing onsite recursion. -/
def geometricWeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

theorem geometricWeight_pos (n : ℕ) : 0 < geometricWeight n := by
  exact pow_pos (by norm_num) _

private theorem geometric_abs_formula :
    (fun n => |geometricWeight n|) = (fun n : ℕ => (1 / 2 : ℝ) ^ n * (1 / 2)) := by
  funext n
  rw [abs_of_pos (geometricWeight_pos n)]
  exact pow_succ (1 / 2 : ℝ) n

theorem geometricWeight_abs_summable : Summable (fun n => |geometricWeight n|) := by
  rw [geometric_abs_formula]
  exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_right _

theorem geometricWeight_abs_tsum : (∑' n, |geometricWeight n|) = 1 := by
  rw [geometric_abs_formula, tsum_mul_right]
  rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

theorem geometric_onsiteStageOperator_norm_le_two (n : ℕ) :
    ‖onsiteStageOperator geometricWeight n‖ ≤ 2 := by
  simpa only [geometricWeight_abs_tsum, mul_one] using
    onsiteStageOperator_norm_le geometricWeight geometricWeight_abs_summable n

/-- The actual summable onsite family bounds its completed operator norm. -/
theorem onsiteCompletedOperator_norm_le (w : ℕ → ℝ)
    (hw : Summable (fun j => |w j|)) :
    ‖onsiteCompletedOperator w hw‖ ≤ 2 * ∑' j, |w j| := by
  have hbound : 0 ≤ (onsiteCompatibleOperatorFamily w hw).bound := by
    change 0 ≤ 2 * ∑' j, |w j|
    exact mul_nonneg (by norm_num) (tsum_nonneg (fun j => abs_nonneg (w j)))
  exact FilteredCompatibleOperatorColimit.completedOperator_norm_le E S
    (onsiteCompatibleOperatorFamily w hw) hbound

/-- Bound two for the same completed operator with nonzero fresh action at every stage. -/
theorem geometric_completedOperator_norm_le_two :
    ‖onsiteCompletedOperator geometricWeight geometricWeight_abs_summable‖ ≤ 2 := by
  simpa only [geometricWeight_abs_tsum, mul_one] using
    onsiteCompletedOperator_norm_le geometricWeight geometricWeight_abs_summable

/-- Infinitely many fresh nonzero actions for one and the same completed operator. -/
theorem geometric_completed_fresh_ne_zero (n : ℕ) :
    onsiteCompletedOperator geometricWeight geometricWeight_abs_summable
      (stageToHilbertDirectLimit E S (n + 1)
        ((cstarMatrixTraceState (n + 1)).functional.toPreGNS (cstarTailX n) :
        (cstarMatrixTraceState (n + 1)).functional.GNS)) ≠ 0 :=
  onsiteCompletedOperator_fresh_ne_zero geometricWeight geometricWeight_abs_summable
    n (ne_of_gt (geometricWeight_pos n))

end InfoGeometry.Canonical.GrowingOnsiteTraceGNSFreshTail
