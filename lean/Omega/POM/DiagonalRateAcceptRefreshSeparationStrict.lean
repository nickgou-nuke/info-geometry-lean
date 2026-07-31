import Mathlib.Tactic
import Omega.POM.DiagonalRateAcceptRefreshSeparationExact

namespace Omega.POM

/-- Paper label: `cor:pom-diagonal-rate-accept-refresh-separation-strict`.
Away from the unique halting state, the exact minimizer from the accept-refresh package is strict.
-/
theorem paper_pom_diagonal_rate_accept_refresh_separation_strict
    {State : Type} (h : State) (ratio : State → Nat → ℝ)
    (haltingStateWorst_witness : ∀ y m, ratio h m ≤ ratio y m)
    (ratio_eq_at_halting_witness : ∀ {y m}, ratio h m = ratio y m → y = h) :
    ∀ y m, y ≠ h -> ratio h m < ratio y m := by
  intro y m hy
  have hle : ratio h m ≤ ratio y m := haltingStateWorst_witness y m
  have hne : ratio h m ≠ ratio y m := by
    intro heq
    exact hy (ratio_eq_at_halting_witness heq)
  exact lt_of_le_of_ne hle hne

end Omega.POM
