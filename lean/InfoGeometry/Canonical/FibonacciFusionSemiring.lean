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
    left_distrib := by
      intro x y z
      change fibMul x (y + z) = fibMul x y + fibMul x z
      ext <;> dsimp [fibMul] <;> ring
    right_distrib := by
      intro x y z
      change fibMul (x + y) z = fibMul x z + fibMul y z
      ext <;> dsimp [fibMul] <;> ring
    zero_mul := by
      intro x
      change fibMul (0, 0) x = (0, 0)
      ext <;> dsimp [fibMul] <;> simp
    mul_zero := by
      intro x
      change fibMul x (0, 0) = (0, 0)
      ext <;> dsimp [fibMul] <;> simp
    mul_assoc := by
      intro x y z
      change fibMul (fibMul x y) z = fibMul x (fibMul y z)
      ext <;> dsimp [fibMul] <;> ring
    one := (1, 0)
    one_mul := by
      intro x
      change fibMul (1, 0) x = x
      ext <;> dsimp [fibMul] <;> simp
    mul_one := by
      intro x
      change fibMul x (1, 0) = x
      ext <;> dsimp [fibMul] <;> simp
    mul_comm := by
      intro x y
      change fibMul x y = fibMul y x
      ext <;> dsimp [fibMul] <;> ring
    npow := fun n x => Nat.recOn n (1, 0) (fun _ p => fibMul p x)
    npow_zero := fun x => rfl
    npow_succ := fun n x => rfl
    natCast := fun n => (n, 0)
    natCast_zero := rfl
    natCast_succ := fun n => rfl
  }

abbrev FibonacciFusionRing := Grothendieck FibFusionSemiring

end InfoGeometry.Canonical
