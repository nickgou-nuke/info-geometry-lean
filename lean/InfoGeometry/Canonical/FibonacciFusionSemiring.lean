import InfoGeometry.Algebra.GrothendieckRing
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.Basic

/-!
# Fibonacci Fusion Semiring

This file defines the Fibonacci fusion semiring $N[\tau] / (\tau^2 = \tau + 1)$.
It provides the `CommSemiring` instance for `ℕ × ℕ` representing `a + b\tau`.
Finally, it applies this to form the Grothendieck ring of the Fibonacci fusion semiring.
-/

namespace InfoGeometry.Canonical

/-- The Fibonacci fusion semiring, representing `a + b\tau` with `a, b \in \mathbb{N}`. -/
abbrev FibFusionSemiring : Type := ℕ × ℕ

/-- Multiplication in the Fibonacci fusion semiring:
(a + b\tau)(c + d\tau) = ac + (ad + bc)\tau + bd\tau^2
= ac + (ad + bc)\tau + bd(\tau + 1)
= (ac + bd) + (ad + bc + bd)\tau
-/
def fibMul (x y : FibFusionSemiring) : FibFusionSemiring :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

instance : CommSemiring FibFusionSemiring :=
  { (inferInstance : AddCommMonoid (ℕ × ℕ)) with
    mul := fibMul
    left_distrib := sorry
    right_distrib := sorry
    zero_mul := sorry
    mul_zero := sorry
    mul_assoc := sorry
    one := (1, 0)
    one_mul := sorry
    mul_one := sorry
    mul_comm := sorry
    npow := fun n x => Nat.recOn n (1, 0) (fun _ p => fibMul x p)
    npow_zero := fun x => rfl
    npow_succ := fun n x => sorry
    natCast := fun n => (n, 0)
    natCast_zero := rfl
    natCast_succ := fun n => rfl
  }

abbrev FibonacciFusionRing := Grothendieck FibFusionSemiring

end InfoGeometry.Canonical
