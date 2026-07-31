import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace InfoGeometry.Combinatorics.BinaryQuadraticResidueBound

theorem square_root_bound_23_implies_ge_six {d : ℕ}
    (hbound : 23 ≤ d ^ 2 - d + 1) : 6 ≤ d := by
  by_contra h
  have hd : d ≤ 5 := by omega
  interval_cases d <;> norm_num at hbound

theorem square_root_bound_23_odd_implies_ge_seven {d : ℕ}
    (hbound : 23 ≤ d ^ 2 - d + 1) (hodd : Odd d) : 7 ≤ d := by
  have hsix : 6 ≤ d := square_root_bound_23_implies_ge_six hbound
  by_contra h
  have hd : d ≤ 6 := by omega
  rcases hodd with ⟨k, hk⟩
  interval_cases d <;> omega

end InfoGeometry.Combinatorics.BinaryQuadraticResidueBound
