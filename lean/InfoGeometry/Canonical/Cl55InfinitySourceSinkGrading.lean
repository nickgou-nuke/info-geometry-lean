/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl55InfinityWittBoundary
import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Infinity CAR endpoints and native source/sink degrees

The existing infinity/origin representatives are precisely native CAR mode `4`.
They have number-operator degrees `+1` and `-1`; adjoining a second creation or
annihilation mode gives nonzero degree `+2` or `-2` words.  Here source and sink
name these two algebraic degree sectors, without an analytic flow claim.

The local boundary involution `infinityGrading55` is a different grading
element: its adjoint weights on the same endpoints are `+2` and `-2`.
The native number grading is an integer grading; the five displayed degrees
describe the selected linear and quadratic words, not all of `Cl55`.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.Cl55InfinityWittBoundary
open InfoGeometry.OperatorAlgebra

@[simp] theorem infinityClifford55_eq_creation55 :
    infinityClifford55 = creation55 4 := by
  simp only [infinityClifford55, infinityVector55, n_bar_vec,
    creation55, map_smul]

@[simp] theorem originClifford55_eq_annihilation55 :
    originClifford55 = annihilation55 4 := by
  simp only [originClifford55, originVector55, n_vec,
    annihilation55, map_smul]

theorem infinityClifford55_mem_grade_one :
    infinityClifford55 ∈ cl55GradeSubmodule 1 := by
  rw [infinityClifford55_eq_creation55]
  exact creation55_mem_grade_one 4

theorem originClifford55_mem_grade_neg_one :
    originClifford55 ∈ cl55GradeSubmodule (-1) := by
  rw [originClifford55_eq_annihilation55]
  exact annihilation55_mem_grade_neg_one 4

theorem infinityProjector55_mem_grade_zero :
    infinityProjector55 ∈ cl55GradeSubmodule 0 := by
  exact grade_mul infinityClifford55_mem_grade_one
    originClifford55_mem_grade_neg_one

theorem originProjector55_mem_grade_zero :
    originProjector55 ∈ cl55GradeSubmodule 0 := by
  exact grade_mul originClifford55_mem_grade_neg_one
    infinityClifford55_mem_grade_one

theorem infinityGrading55_mem_grade_zero :
    infinityGrading55 ∈ cl55GradeSubmodule 0 := by
  exact grade_sub infinityProjector55_mem_grade_zero
    originProjector55_mem_grade_zero

/-- A retained positive quadratic word in the native Clifford algebra. -/
def sourcePair55 (i : Fin 5) : Cl55 :=
  infinityClifford55 * creation55 i

/-- A retained negative quadratic word in the native Clifford algebra. -/
def sinkPair55 (i : Fin 5) : Cl55 :=
  originClifford55 * annihilation55 i

theorem sourcePair55_mem_grade_two (i : Fin 5) :
    sourcePair55 i ∈ cl55GradeSubmodule 2 := by
  exact grade_mul infinityClifford55_mem_grade_one
    (creation55_mem_grade_one i)

theorem sinkPair55_mem_grade_neg_two (i : Fin 5) :
    sinkPair55 i ∈ cl55GradeSubmodule (-2) := by
  exact grade_mul originClifford55_mem_grade_neg_one
    (annihilation55_mem_grade_neg_one i)

theorem sourcePair55_mul_sinkPair55_mem_grade_zero (i j : Fin 5) :
    sourcePair55 i * sinkPair55 j ∈ cl55GradeSubmodule 0 := by
  exact grade_mul (sourcePair55_mem_grade_two i)
    (sinkPair55_mem_grade_neg_two j)

theorem sinkPair55_mul_sourcePair55_mem_grade_zero (i j : Fin 5) :
    sinkPair55 i * sourcePair55 j ∈ cl55GradeSubmodule 0 := by
  exact grade_mul (sinkPair55_mem_grade_neg_two i)
    (sourcePair55_mem_grade_two j)

theorem sourcePair55_sinkPair55_commutator_mem_grade_zero (i j : Fin 5) :
    sourcePair55 i * sinkPair55 j - sinkPair55 j * sourcePair55 i ∈
      cl55GradeSubmodule 0 := by
  exact grade_commutator (sourcePair55_mem_grade_two i)
    (sinkPair55_mem_grade_neg_two j)

private theorem car_product_ne_zero
    {A : Type*} [Ring A] [Nontrivial A] {c d a b : A}
    (hac : a * c + c * a = 1)
    (had : a * d + d * a = 0)
    (hbd : b * d + d * b = 1) : c * d ≠ 0 := by
  intro hcd
  have hd : d = 0 := by
    calc
      d = (a * c + c * a) * d := by rw [hac, one_mul]
      _ = a * (c * d) + c * (a * d + d * a) - (c * d) * a := by
        noncomm_ring
      _ = 0 := by rw [hcd, had]; simp
  have h01 : (0 : A) = 1 := by simpa [hd] using hbd
  exact zero_ne_one h01

theorem sourcePair55_ne_zero (i : Fin 5) (hi : i ≠ 4) :
    sourcePair55 i ≠ 0 := by
  unfold sourcePair55
  rw [infinityClifford55_eq_creation55]
  apply car_product_ne_zero
    (a := annihilation55 4) (b := annihilation55 i)
  · exact annihilation55_creation55_anticommutator 4
  · simpa [Ne.symm hi] using
      annihilation55_creation55_anticommutator_eq 4 i
  · exact annihilation55_creation55_anticommutator i

theorem sinkPair55_ne_zero (i : Fin 5) (hi : i ≠ 4) :
    sinkPair55 i ≠ 0 := by
  unfold sinkPair55
  rw [originClifford55_eq_annihilation55]
  apply car_product_ne_zero
    (a := creation55 4) (b := creation55 i)
  · simpa only [add_comm] using annihilation55_creation55_anticommutator 4
  · simpa [hi, add_comm] using
      annihilation55_creation55_anticommutator_eq i 4
  · simpa only [add_comm] using annihilation55_creation55_anticommutator i

theorem source_sink_nonzero_witness :
    sourcePair55 0 ≠ 0 ∧ sinkPair55 0 ≠ 0 := by
  exact ⟨sourcePair55_ne_zero 0 (by decide),
    sinkPair55_ne_zero 0 (by decide)⟩

@[simp] theorem sourcePair55_same_mode_zero : sourcePair55 4 = 0 := by
  simp only [sourcePair55, infinityClifford55_eq_creation55, creation55_sq]

@[simp] theorem sinkPair55_same_mode_zero : sinkPair55 4 = 0 := by
  simp only [sinkPair55, originClifford55_eq_annihilation55, annihilation55_sq]

theorem infinityClifford55_involute :
    CliffordAlgebra.involute infinityClifford55 = -infinityClifford55 := by
  exact CliffordAlgebra.involute_ι infinityVector55

theorem originClifford55_involute :
    CliffordAlgebra.involute originClifford55 = -originClifford55 := by
  exact CliffordAlgebra.involute_ι originVector55

theorem creation55_involute (i : Fin 5) :
    CliffordAlgebra.involute (creation55 i) = -(creation55 i) := by
  simp only [creation55, map_smul, CliffordAlgebra.involute_ι, smul_neg]

theorem annihilation55_involute (i : Fin 5) :
    CliffordAlgebra.involute (annihilation55 i) = -(annihilation55 i) := by
  simp only [annihilation55, map_smul, CliffordAlgebra.involute_ι, smul_neg]

theorem sourcePair55_involute (i : Fin 5) :
    CliffordAlgebra.involute (sourcePair55 i) = sourcePair55 i := by
  rw [sourcePair55, map_mul, infinityClifford55_involute,
    creation55_involute, neg_mul_neg]

theorem sinkPair55_involute (i : Fin 5) :
    CliffordAlgebra.involute (sinkPair55 i) = sinkPair55 i := by
  rw [sinkPair55, map_mul, originClifford55_involute,
    annihilation55_involute, neg_mul_neg]

/-- The local boundary involution has twice the endpoint number weight. -/
theorem infinityClifford55_local_grade_two :
    HasOperatorGrade infinityGrading55 infinityClifford55 2 := by
  unfold HasOperatorGrade
  rw [infinityGrading55_mul_infinityClifford55,
    infinityClifford55_mul_infinityGrading55]
  norm_num <;> module

theorem originClifford55_local_grade_neg_two :
    HasOperatorGrade infinityGrading55 originClifford55 (-2) := by
  unfold HasOperatorGrade
  rw [infinityGrading55_mul_originClifford55,
    originClifford55_mul_infinityGrading55]
  norm_num <;> module

end InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading
