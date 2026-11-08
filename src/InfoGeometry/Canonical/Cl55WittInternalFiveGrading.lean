/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl55WittFullLieClosure
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The internal five-lane decomposition of the generated Witt Lie algebra

The already constructed lanes are independent because they belong to distinct
eigenspaces of the actual number commutator. Their sum is the existing Lie
span, not the full stage-five associative algebra. This file constructs the
internal direct sum and proves the dimension of that sum is 55.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55WittInternalFiveGrading

open scoped DirectSum BigOperators

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Canonical.Cl55WittFullLieClosure

instance : Fintype WittLane where
  elems := {.negTwo, .negOne, .zero, .posOne, .posTwo}
  complete i := by cases i <;> simp

theorem lane_degree_real_injective :
    Function.Injective (fun i : WittLane => (i.degree : ℝ)) := by
  intro i j h
  cases i <;> cases j <;> first | rfl | norm_num [WittLane.degree] at h

theorem laneSpace_le_grade (i : WittLane) :
    laneSpace i ≤ gradeSubmodule i.degree := by
  cases i
  · exact wittNegTwo_le_gradeSubmodule
  · exact wittNegOne_le_gradeSubmodule
  · exact wittZero_le_gradeSubmodule
  · exact wittPosOne_le_gradeSubmodule
  · exact wittPosTwo_le_gradeSubmodule

theorem laneSpace_le_eigenspace (i : WittLane) :
    laneSpace i ≤ Module.End.eigenspace numberAdjoint (i.degree : ℝ) := by
  intro X hX
  apply Module.End.mem_eigenspace_iff.mpr
  exact laneSpace_le_grade i hX

/-- Full independence, stronger than pairwise trivial intersections. -/
theorem laneSpace_independent : iSupIndep laneSpace :=
  ((Module.End.eigenspaces_iSupIndep numberAdjoint).comp
    lane_degree_real_injective).mono laneSpace_le_eigenspace

theorem iSup_laneSpace_eq : (⨆ i, laneSpace i) = wittFiveGrade := by
  rw [← wittFiveGradeSpan_eq_wittFiveGrade]
  apply le_antisymm
  · exact iSup_le laneSpace_le_span
  · apply Submodule.span_le.mpr
    rintro X ⟨i, hi⟩
    exact (le_iSup laneSpace i) hi

/-- The actual homogeneous lanes as submodules of the generated Lie carrier. -/
def internalLane (i : WittLane) : Submodule ℝ wittFiveGrade :=
  (laneSpace i).comap wittFiveGrade.subtype

@[simp] theorem internalLane_map (i : WittLane) :
    (internalLane i).map wittFiveGrade.subtype = laneSpace i := by
  rw [internalLane, Submodule.map_comap_subtype,
    inf_of_le_right (laneSpace_le_wittFiveGrade i)]

theorem internalLane_independent : iSupIndep internalLane := by
  let e : Submodule ℝ wittFiveGrade ≃o Set.Iic wittFiveGrade := wittFiveGrade.mapIic
  have he : e ∘ internalLane =
      fun i => (⟨laneSpace i, laneSpace_le_wittFiveGrade i⟩ : Set.Iic wittFiveGrade) := by
    ext i X
    exact SetLike.ext_iff.mp (internalLane_map i) X
  rw [← iSupIndep_map_orderIso_iff e, he]
  exact iSupIndep.of_coe_Iic_comp laneSpace_independent

theorem iSup_internalLane_eq_top : (⨆ i, internalLane i) = ⊤ := by
  apply Submodule.map_injective_of_injective wittFiveGrade.subtype_injective
  rw [Submodule.map_iSup]
  simp only [internalLane_map, Submodule.map_top, Submodule.range_subtype,
    iSup_laneSpace_eq]

/-- Existence and uniqueness of all five homogeneous components. -/
theorem wittFiveGrade_isInternal : DirectSum.IsInternal internalLane :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    internalLane_independent iSup_internalLane_eq_top

/-- Concrete decomposition equivalence; its inverse extracts the five lanes. -/
def wittFiveGradeDecomposition :
    (⨁ i : WittLane, internalLane i) ≃ₗ[ℝ] wittFiveGrade :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap internalLane) wittFiveGrade_isInternal

/-- Restricting the ambient carrier does not alter any homogeneous lane. -/
def internalLaneEquiv (i : WittLane) : internalLane i ≃ₗ[ℝ] laneSpace i where
  toFun X := ⟨X.1.1, X.2⟩
  invFun X := ⟨⟨X.1, laneSpace_le_wittFiveGrade i X.2⟩, X.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def laneDimension : WittLane → ℕ
  | .negTwo => 10
  | .negOne => 5
  | .zero => 25
  | .posOne => 5
  | .posTwo => 10

theorem laneSpace_finrank (i : WittLane) :
    Module.finrank ℝ (laneSpace i) = laneDimension i := by
  cases i
  · exact wittNegTwo_finrank_eq_ten
  · exact wittNegOne_finrank_eq_five
  · exact wittZero_finrank_eq_twentyFive
  · exact wittPosOne_finrank_eq_five
  · exact wittPosTwo_finrank_eq_ten

theorem wittFiveGrade_finrank : Module.finrank ℝ wittFiveGrade = 55 := by
  haveI : ∀ i : WittLane, Module.Free ℝ (internalLane i) :=
    fun i => Module.Free.of_divisionRing ℝ (internalLane i)
  haveI : ∀ i : WittLane, Module.Finite ℝ (internalLane i) := fun _ => inferInstance
  calc
    Module.finrank ℝ wittFiveGrade =
        Module.finrank ℝ (⨁ i : WittLane, internalLane i) :=
      wittFiveGradeDecomposition.finrank_eq.symm
    _ = ∑ i : WittLane, Module.finrank ℝ (internalLane i) :=
      Module.finrank_directSum ℝ (fun i : WittLane => ↥(internalLane i))
    _ = ∑ i : WittLane, laneDimension i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (internalLaneEquiv i).finrank_eq.trans (laneSpace_finrank i)
    _ = 55 := by decide

end InfoGeometry.Canonical.Cl55WittInternalFiveGrading
