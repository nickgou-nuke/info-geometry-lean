import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The accept-refresh strong stationary time is exact: separation equals the tail probability,
the designated halting state attains that value for every time, and so it is a time-independent
worst point. This wrapper keeps both the tail-formula and survival-probability presentations of
`thm:pom-diagonal-rate-accept-refresh-separation-exact`. -/
theorem paper_pom_diagonal_rate_accept_refresh_separation_exact
    {State : Type} (h : State)
    (sep tail survivalProb : Nat → ℝ) (ratio : State → Nat → ℝ)
    (worstStateRatio : Nat → ℝ)
    (strongStationaryTime haltingStateLemma : Prop)
    (worstStateIsMinimizer : Nat → Prop)
    (strongStationaryTimeWitness : strongStationaryTime)
    (haltingStateLemmaWitness : haltingStateLemma)
    (sep_eq_tail_witness : ∀ m, sep m = tail m)
    (tail_eq_halting_gap_witness : ∀ m, tail m = 1 - ratio h m)
    (haltingStateWorst_witness : ∀ y m, ratio h m ≤ ratio y m)
    (sep_le_survivalProb_witness : ∀ m, sep m ≤ survivalProb m)
    (survivalProb_le_sep_at_halting_witness : ∀ m, survivalProb m ≤ sep m)
    (worstStateRatio_eq_sep_witness : ∀ m, worstStateRatio m = sep m)
    (worstStateIsMinimizer_witness : ∀ m, worstStateIsMinimizer m) :
    strongStationaryTime ∧ haltingStateLemma ∧
      (∀ m, sep m = tail m) ∧
      (∀ m, sep m = 1 - ratio h m) ∧
      (∀ y m, ratio h m ≤ ratio y m) ∧
      (∀ m, sep m = survivalProb m) ∧
      (∀ m, worstStateRatio m = survivalProb m) ∧
      ∀ m, worstStateIsMinimizer m := by
  have hSepEq : ∀ m, sep m = survivalProb m := by
    intro m
    exact le_antisymm (sep_le_survivalProb_witness m)
      (survivalProb_le_sep_at_halting_witness m)
  refine ⟨strongStationaryTimeWitness, haltingStateLemmaWitness, sep_eq_tail_witness, ?_, ?_, hSepEq, ?_, worstStateIsMinimizer_witness⟩
  · intro m
    calc
      sep m = tail m := sep_eq_tail_witness m
      _ = 1 - ratio h m := tail_eq_halting_gap_witness m
  · exact haltingStateWorst_witness
  · intro m
    rw [worstStateRatio_eq_sep_witness m, hSepEq m]

end Omega.POM
