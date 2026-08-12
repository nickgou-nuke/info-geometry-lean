import Mathlib
import InfoGeometry.Clifford.Cl55ThreeColorChiralGenerators

/-!
# Finite colour-summed chiral operators in `Cl(5,5)`

The existing `Cl55ThreeColorChiralGenerators` owner provides the three
component chiral operator vectors.  This file packages their finite sums and
records the resulting operatorial supercharge algebra.  It is a readout on
the native `Cl55` carrier; it does not identify that carrier with the
split-octonion Zorn carrier.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.OperatorAlgebra

/-- The unweighted positive-chirality colour sum. -/
def chiralPlusSum : Cl55 := ∑ i : Fin 3, chiralPlus55 i

/-- The unweighted negative-chirality colour sum. -/
def chiralMinusSum : Cl55 := ∑ i : Fin 3, chiralMinus55 i

theorem chiralPlusSum_mem_grade_one :
    chiralPlusSum ∈ cl55GradeSubmodule 1 := by
  exact Submodule.sum_mem _ (fun i _ => chiralPlus55_mem_grade_one i)

theorem chiralMinusSum_mem_grade_neg_one :
    chiralMinusSum ∈ cl55GradeSubmodule (-1) := by
  exact Submodule.sum_mem _ (fun i _ => chiralMinus55_mem_grade_neg_one i)

theorem chiralPlusSum_sq : chiralPlusSum * chiralPlusSum = 0 := by
  simp only [chiralPlusSum, Fin.sum_univ_three, add_mul, mul_add,
    chiralPlus55_sq]
  have h01 := chiralPlus55_anticommutator (0 : Fin 3) 1
  have h02 := chiralPlus55_anticommutator (0 : Fin 3) 2
  have h12 := chiralPlus55_anticommutator (1 : Fin 3) 2
  calc
    _ = (chiralPlus55 0 * chiralPlus55 1 + chiralPlus55 1 * chiralPlus55 0) +
        (chiralPlus55 0 * chiralPlus55 2 + chiralPlus55 2 * chiralPlus55 0) +
        (chiralPlus55 1 * chiralPlus55 2 + chiralPlus55 2 * chiralPlus55 1) := by abel
    _ = 0 := by rw [h01, h02, h12]; simp

theorem chiralMinusSum_sq : chiralMinusSum * chiralMinusSum = 0 := by
  simp only [chiralMinusSum, Fin.sum_univ_three, add_mul, mul_add,
    chiralMinus55_sq]
  have h01 := chiralMinus55_anticommutator (0 : Fin 3) 1
  have h02 := chiralMinus55_anticommutator (0 : Fin 3) 2
  have h12 := chiralMinus55_anticommutator (1 : Fin 3) 2
  calc
    _ = (chiralMinus55 0 * chiralMinus55 1 + chiralMinus55 1 * chiralMinus55 0) +
        (chiralMinus55 0 * chiralMinus55 2 + chiralMinus55 2 * chiralMinus55 0) +
        (chiralMinus55 1 * chiralMinus55 2 + chiralMinus55 2 * chiralMinus55 1) := by abel
    _ = 0 := by rw [h01, h02, h12]; simp

theorem chiralMinusSum_plusSum_anticommutator :
    chiralMinusSum * chiralPlusSum + chiralPlusSum * chiralMinusSum =
      (3 : Cl55) := by
  simp only [chiralMinusSum, chiralPlusSum, Fin.sum_univ_three,
    add_mul, mul_add]
  have h00 := chiralMinus55_plus55_anticommutator (0 : Fin 3) 0
  have h11 := chiralMinus55_plus55_anticommutator (1 : Fin 3) 1
  have h22 := chiralMinus55_plus55_anticommutator (2 : Fin 3) 2
  have h01 := chiralMinus55_plus55_anticommutator (0 : Fin 3) 1
  have h02 := chiralMinus55_plus55_anticommutator (0 : Fin 3) 2
  have h10 := chiralMinus55_plus55_anticommutator (1 : Fin 3) 0
  have h12 := chiralMinus55_plus55_anticommutator (1 : Fin 3) 2
  have h20 := chiralMinus55_plus55_anticommutator (2 : Fin 3) 0
  have h21 := chiralMinus55_plus55_anticommutator (2 : Fin 3) 1
  norm_num at h00 h11 h22 h01 h10
  simp at h02 h12 h20 h21
  calc
    _ = (chiralMinus55 0 * chiralPlus55 0 + chiralPlus55 0 * chiralMinus55 0) +
        (chiralMinus55 1 * chiralPlus55 1 + chiralPlus55 1 * chiralMinus55 1) +
        (chiralMinus55 2 * chiralPlus55 2 + chiralPlus55 2 * chiralMinus55 2) +
        (chiralMinus55 0 * chiralPlus55 1 + chiralPlus55 1 * chiralMinus55 0) +
        (chiralMinus55 0 * chiralPlus55 2 + chiralPlus55 2 * chiralMinus55 0) +
        (chiralMinus55 1 * chiralPlus55 0 + chiralPlus55 0 * chiralMinus55 1) +
        (chiralMinus55 1 * chiralPlus55 2 + chiralPlus55 2 * chiralMinus55 1) +
        (chiralMinus55 2 * chiralPlus55 0 + chiralPlus55 0 * chiralMinus55 2) +
        (chiralMinus55 2 * chiralPlus55 1 + chiralPlus55 1 * chiralMinus55 2) := by abel
    _ = 3 := by
      rw [h00, h11, h22, h01, h02, h10, h12, h20, h21]
      norm_num

theorem chiralPlusSum_mul_minusSum_mem_grade_zero :
    chiralPlusSum * chiralMinusSum ∈ cl55GradeSubmodule 0 := by
  exact grade_mul
    chiralPlusSum_mem_grade_one chiralMinusSum_mem_grade_neg_one

theorem chiralMinusSum_mul_plusSum_mem_grade_zero :
    chiralMinusSum * chiralPlusSum ∈ cl55GradeSubmodule 0 := by
  exact grade_mul
    chiralMinusSum_mem_grade_neg_one chiralPlusSum_mem_grade_one

theorem chiralPlusSum_minusSum_commutator_mem_grade_zero :
    chiralPlusSum * chiralMinusSum -
        chiralMinusSum * chiralPlusSum ∈ cl55GradeSubmodule 0 := by
  exact cl55_mixed_commutator_mem_grade_zero
    chiralPlusSum_mem_grade_one chiralMinusSum_mem_grade_neg_one

/-- The first-order colour-summed chiral Dirac operator. -/
def chiralDiracSum : Cl55 := chiralPlusSum + chiralMinusSum

theorem chiralDiracSum_sq : chiralDiracSum * chiralDiracSum = (3 : Cl55) := by
  simp only [chiralDiracSum, add_mul, mul_add, chiralPlusSum_sq,
    chiralMinusSum_sq, zero_add, add_zero]
  simpa [add_comm] using chiralMinusSum_plusSum_anticommutator

end InfoGeometry.Clifford.Clifford55
