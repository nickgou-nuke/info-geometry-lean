import InfoGeometry.CyclotomicSplitting.AlgebraicPolarization

namespace InfoGeometry.CyclotomicSplitting.Tests

open Matrix

example : (∑ index ∈ Finset.range 2, (-1 : ℤ) ^ index) = 0 :=
  cyclotomic_sum_vanishing 2 (-1) (by norm_num) (by norm_num)

example : (∑ index ∈ Finset.range 0, (2 : ℤ) ^ index) = 0 :=
  cyclotomic_sum_vanishing 0 2 (by norm_num) (by norm_num)

example : (∑ index ∈ Finset.range 2, (1 : ℚ) ^ index) ≠ 0 := by norm_num

def involution : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

theorem involution_sq : involution ^ 2 = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [involution, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem involution_ne_one : involution ≠ 1 := by
  intro equal
  have entry := congrArg (fun operator : Matrix (Fin 2) (Fin 2) ℚ => operator 1 1) equal
  norm_num [involution] at entry

theorem involution_sum_not_zero :
    (∑ index ∈ Finset.range 2, involution ^ index) ≠ 0 := by
  intro equal
  have entry := congrArg (fun operator : Matrix (Fin 2) (Fin 2) ℚ => operator 0 0) equal
  norm_num [Finset.sum_range_succ, involution] at entry

example : (1 - involution) * (∑ index ∈ Finset.range 2, involution ^ index) = 0 :=
  InfoGeometry.Algebra.CyclotomicOperatorProjectors.root_of_unity_geometric_sum_annihilates
    involution_sq

#print axioms cyclotomic_sum_vanishing
#print axioms triangular_root_identity
#print axioms idempotent_eq_zero_or_one
#print axioms involution_sum_not_zero

end InfoGeometry.CyclotomicSplitting.Tests
