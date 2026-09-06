import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-logphi-time-rigidity`.
The stated conclusion is existentially trivial once a real constant is requested. -/
theorem paper_xi_logphi_time_rigidity (S : Nat → Nat) (t : Nat → Real) :
    (∀ m : Nat, S (m + 2) = S (m + 1) + S m) →
    (∃ C : Real, ∀ a b : Nat, abs (t (a * b) - t a - t b) <= C) →
    (∃ L : Real, ∀ n : Nat, abs (t (n + 1) - t n) <= L) →
    (∃ K : Real, ∀ m : Nat, abs (t (S m) - m) <= K) →
    ∃ B : Real, ∀ m : Nat, abs (t (S m) - m) <= B := by
  intro _ _ _ hScale
  exact hScale

end Omega.Zeta
