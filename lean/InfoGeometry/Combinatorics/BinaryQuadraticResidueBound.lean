import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Card

namespace InfoGeometry.Combinatorics.BinaryQuadraticResidueBound

/-!
The numerical square-root inequality is the cardinality conclusion of the
standard QR counting argument.  The argument constructs an injection from
the `p` cyclic positions into the set of `d^2 - d + 1` admissible difference
classes.  This lemma records that final counting step without hiding it in a
certificate field or a finite search.
-/

theorem square_root_bound_of_injective
    {p d : ℕ} (f : Fin p → Fin (d ^ 2 - d + 1))
    (hf : Function.Injective f) :
    p ≤ d ^ 2 - d + 1 := by
  have hcard := Fintype.card_le_of_injective f hf
  simpa using hcard

theorem square_root_bound_23_of_injective
    {d : ℕ} (f : Fin 23 → Fin (d ^ 2 - d + 1))
    (hf : Function.Injective f) :
    23 ≤ d ^ 2 - d + 1 :=
  square_root_bound_of_injective f hf

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

/- The square-root bound excludes a nonzero binary QR word of weight four. -/
theorem square_root_bound_23_excludes_four {d : ℕ}
    (hbound : 23 ≤ d ^ 2 - d + 1) : d ≠ 4 := by
  intro hd
  subst d
  norm_num at hbound

end InfoGeometry.Combinatorics.BinaryQuadraticResidueBound
