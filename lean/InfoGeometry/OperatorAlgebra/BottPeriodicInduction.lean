import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation

namespace InfoGeometry.OperatorAlgebra.BottPeriodicInduction

/--
Bott-periodic recurrence on even degrees:
if a property is closed under `n ↦ n+2`, then it propagates along all even
degrees from degree `0`.
-/
@[rep_depth thermo]
theorem bott_periodic_induction_even
    (P : ℕ → Prop)
    (h0 : P 0)
    (hstep : ∀ n, P n → P (n + 2)) :
    ∀ k, P (2 * k) := by
  intro k
  induction k with
  | zero =>
      simpa using h0
  | succ k ih =>
      have hk : P (2 * k) := ih
      have hnext : P (2 * k + 2) := hstep (2 * k) hk
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

/--
Full Bott-periodic recurrence:
if a property is closed under `n ↦ n+2`, then seeds at degrees `0` and `1`
propagate to all degrees.
-/
@[rep_depth thermo]
theorem bott_periodic_induction_all
    (P : ℕ → Prop)
    (h0 : P 0)
    (h1 : P 1)
    (hstep : ∀ n, P n → P (n + 2)) :
    ∀ n, P n := by
  intro n
  rcases Nat.even_or_odd n with hEven | hOdd
  · rcases hEven with ⟨k, hk⟩
    rw [hk]
    simpa [two_mul] using bott_periodic_induction_even P h0 hstep k
  · rcases hOdd with ⟨k, hk⟩
    rw [hk]
    have hoddStep : ∀ m, P (m + 1) → P (m + 1 + 2) := by
      intro m hm
      simpa [Nat.add_assoc] using hstep (m + 1) hm
    have hprop : ∀ k, P (2 * k + 1) := by
      intro k
      induction k with
      | zero =>
          simpa using h1
      | succ k ih =>
          have hnext : P (2 * k + 1 + 2) := hoddStep (2 * k) (by simpa [Nat.add_assoc] using ih)
          simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
    simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hprop k


end InfoGeometry.OperatorAlgebra.BottPeriodicInduction
