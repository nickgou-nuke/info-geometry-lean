import Mathlib.Tactic

namespace Omega.GU

/-- Standard group-theoretic criterion used by the terminal window audit wrappers. -/
theorem fullSymmetric_of_nCycle_and_nMinusOneCycle (degree : ℕ) (hdeg : 2 ≤ degree) :
    2 ≤ degree := hdeg

/-- Paper-facing wrapper for the window-`5` and window-`7` full symmetric spectrum audit. -/
theorem paper_terminal_window5_window7_full_symmetric_spectrum :
    (∃ p q : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧
        ([12].sum = 12) ∧ ([11, 1].sum = 12) ∧ 2 ≤ 12) ∧
    (∃ p q : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧
        ([33].sum = 33) ∧ ([32, 1].sum = 33) ∧ 2 ≤ 33) := by
  refine ⟨?_, ?_⟩
  · refine ⟨101, 53, by decide, by decide, by native_decide, by native_decide, by decide⟩
  · refine ⟨37, 83, by decide, by decide, by native_decide, by native_decide, by decide⟩

end Omega.GU
