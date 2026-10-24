/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredCompatibleOperatorColimit
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Symmetry and self-adjointness of the existing bounded completed operator.
Only density is used on the completion; exact finite-stage coverage is not assumed.
-/

noncomputable section
namespace InfoGeometry.Canonical.FilteredCompatibleOperatorColimit

open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

universe u
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable (E : I → Type u) [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, InnerProductSpace ℂ (E i)]
variable (sys : IsometricDirectSystem E) (T : CompatibleOperatorFamily E sys)

/-- Two finite-stage vectors can be compared at a common upper stage. -/
theorem completedOperator_inner_stage
    (hsym : ∀ i, LinearMap.IsSymmetric (T.op i).toLinearMap)
    (i j : I) (x : E i) (y : E j) :
    inner ℂ (completedOperator E sys T (stageToHilbertDirectLimit E sys i x))
        (stageToHilbertDirectLimit E sys j y) =
      inner ℂ (stageToHilbertDirectLimit E sys i x)
        (completedOperator E sys T (stageToHilbertDirectLimit E sys j y)) := by
  obtain ⟨m, him, hjm⟩ := exists_ge_ge i j
  rw [← stageToHilbertDirectLimit_transition E sys him x,
    ← stageToHilbertDirectLimit_transition E sys hjm y]
  rw [completedOperator_stage, completedOperator_stage]
  rw [(stageToHilbertDirectLimit E sys m).inner_map_map,
    (stageToHilbertDirectLimit E sys m).inner_map_map]
  exact hsym m (sys.map him x) (sys.map hjm y)

/-- Stage symmetry extends to the existing Hilbert completion by continuity. -/
theorem completedOperator_isSymmetric
    (hsym : ∀ i, LinearMap.IsSymmetric (T.op i).toLinearMap) :
    LinearMap.IsSymmetric (completedOperator E sys T).toLinearMap := by
  intro x y
  have hd := dense_iUnion_range_stageToHilbertDirectLimit E sys
  have heq :
      (fun z => inner ℂ (completedOperator E sys T z) y) =
        (fun z => inner ℂ z (completedOperator E sys T y)) := by
    apply Continuous.ext_on hd
    · exact (completedOperator E sys T).continuous.inner continuous_const
    · exact continuous_id.inner continuous_const
    · intro z hz
      have heq' :
          (fun w => inner ℂ (completedOperator E sys T z) w) =
            (fun w => inner ℂ z (completedOperator E sys T w)) := by
        apply Continuous.ext_on hd
        · exact continuous_const.inner continuous_id
        · exact continuous_const.inner (completedOperator E sys T).continuous
        · intro w hw
          rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
          rcases hi with ⟨a, rfl⟩
          rcases Set.mem_iUnion.mp hw with ⟨j, hj⟩
          rcases hj with ⟨b, rfl⟩
          exact completedOperator_inner_stage E sys T hsym i j a b
      exact congrFun heq' y
  exact congrFun heq x

/-- Stagewise self-adjointness implies self-adjointness of the constructed
bounded completed operator. No completed-operator property is an input. -/
theorem completedOperator_selfAdjoint [∀ i, CompleteSpace (E i)]
    (hsa : ∀ i, IsSelfAdjoint (T.op i)) :
    IsSelfAdjoint (completedOperator E sys T) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  apply completedOperator_isSymmetric E sys T
  intro i
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hsa i)

end InfoGeometry.Canonical.FilteredCompatibleOperatorColimit
