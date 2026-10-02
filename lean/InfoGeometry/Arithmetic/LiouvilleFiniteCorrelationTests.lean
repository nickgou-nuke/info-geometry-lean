import InfoGeometry.Arithmetic.LiouvilleFiniteCorrelation

namespace InfoGeometry.Arithmetic.LiouvilleFiniteCorrelationTests

open LiouvilleFiniteCorrelation BostConnesSystem
open scoped BigOperators

example (samples : Finset ℕ+) :
    (∑ index ∈ samples, liouville index * liouville (index.val + 0)) =
      (samples.card : ℤ) := by
  simpa using liouville_self_correlation samples

example (shift : ℕ) :
    (∑ index ∈ (∅ : Finset ℕ+),
      liouville index * liouville (index.val + shift)) = 0 := by
  simp

example :
    (∑ index ∈ Finset.univ (α := Fin 2),
      (1 : ℤ) * (if index = 0 then 1 else -1)) = 0 := by
  norm_num [Fin.sum_univ_two]

example (index : ℕ+) (shift : ℕ) :
    liouville index * liouville (index.val + shift) ≠ 0 := by
  simpa using liouville_correlation_ne_zero_of_odd_card
    {index} shift (by simp)

#print axioms finite_correlation_dependencies
#print axioms multiplicativity_and_counting_incomparable
#print axioms cancellation_is_additional_dependency
#print axioms finite_sign_correlation
#print axioms liouville_correlation_count
#print axioms liouville_self_correlation
#print axioms liouville_correlation_zero_iff
#print axioms liouville_correlation_abs_le
#print axioms liouville_correlation_ne_zero_of_odd_card

end InfoGeometry.Arithmetic.LiouvilleFiniteCorrelationTests
