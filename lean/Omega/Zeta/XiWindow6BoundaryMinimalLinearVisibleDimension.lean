import Mathlib.Tactic

namespace Omega.Zeta

/-- The visible linear coordinate space has dimension at least three. -/
def statement (visibleDimension : ℕ) : Prop :=
  3 ≤ visibleDimension

/-- Paper label: `thm:xi-window6-boundary-minimal-linear-visible-dimension`. -/
theorem paper_xi_window6_boundary_minimal_linear_visible_dimension
    (visibleDimension oddPrime : ℕ)
    (oddPrime_isPrime : Nat.Prime oddPrime)
    (oddPrime_ne_two : oddPrime ≠ 2)
    (characterCoordinate : Fin 3 → Fin visibleDimension)
    (characterCoordinate_injective : Function.Injective characterCoordinate) :
    statement visibleDimension := by
  have hcard := Fintype.card_le_of_injective characterCoordinate characterCoordinate_injective
  simpa [statement] using hcard

end Omega.Zeta
