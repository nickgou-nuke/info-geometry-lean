import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Omega.Folding.FiberGaugeVolumeDoublingV2DigitSum

namespace Omega.Conclusion

open scoped BigOperators

private lemma list_nat_le_sum (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases hx
  | cons h t ih =>
      rw [List.sum_cons]
      cases hx with
      | head => omega
      | tail _ hx' =>
          have := ih hx'
          omega

private lemma basePDigitSum_two_one_le {n : ℕ} (hn : 0 < n) :
    1 ≤ Omega.Folding.basePDigitSum 2 n := by
  rw [Omega.Folding.basePDigitSum]
  have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt hn)
  have hmem := List.getLast_mem hnil
  have hpos : 0 < (Nat.digits 2 n).getLast hnil :=
    Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 (Nat.ne_of_gt hn))
  have hle := list_nat_le_sum (Nat.digits 2 n) ((Nat.digits 2 n).getLast hnil) hmem
  omega

/-- Paper label: `cor:fiber-gauge-volume-doubling-v2-lowerbound`. -/
theorem paper_fiber_gauge_volume_doubling_v2_lowerbound (m : ℕ) :
    (Finset.univ : Finset (Omega.X m)).sum
        (fun x : Omega.X m => Omega.Folding.basePDigitSum 2 (Omega.X.fiberMultiplicity x)) ≥
      Fintype.card (Omega.X m) := by
  calc
    Fintype.card (Omega.X m) = ∑ x : Omega.X m, 1 := by simp
    _ ≤ ∑ x : Omega.X m, Omega.Folding.basePDigitSum 2 (Omega.X.fiberMultiplicity x) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact basePDigitSum_two_one_le (Omega.X.fiberMultiplicity_pos x)

end Omega.Conclusion
