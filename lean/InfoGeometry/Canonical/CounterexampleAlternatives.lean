import Mathlib

/-!
# Canonical alternatives to counterexample-driven claims

The repository contains many finite witnesses showing that a stronger slogan
is false.  This owner file records general algebraic replacements.  The
statements use arbitrary associative rings or additive groups, rather than
scalar diagonal models.
-/

namespace InfoGeometry.Canonical.CounterexampleAlternatives

variable {A B : Type*}

theorem peirce_corner_square_zero
    [Semiring A] (p q x : A) (hqp : q * p = 0) :
    (p * x * q) * (p * x * q) = 0 := by
  calc
    (p * x * q) * (p * x * q) = p * x * (q * p) * x * q := by
      simp only [mul_assoc]
    _ = 0 := by rw [hqp, mul_zero, zero_mul, zero_mul]

theorem ring_hom_preserves_associator
    [Ring A] [Ring B]
    (f : A →+* B) (x y z : A) :
    f ((x * y) * z - x * (y * z)) =
      (f x * f y) * f z - f x * (f y * f z) := by
  simp only [map_sub, map_mul]

theorem cycle_sum_zero_of_potential
    [AddCommGroup A] (u v w : A) :
    ((v - u) + (w - v) + (u - w)) = 0 := by
  abel

theorem mp_range_idempotent
    [Semiring A] (x m : A) (hxm : x * m * x = x) :
    (x * m) * (x * m) = x * m := by
  calc
    (x * m) * (x * m) = (x * m * x) * m := by simp only [mul_assoc]
    _ = x * m := by rw [hxm]

theorem jordan_plus_lie_recovers_mul
    [Ring A] (x y : A) :
    (x * y + y * x + (x * y - y * x)) = 2 • (x * y) := by
  module

end InfoGeometry.Canonical.CounterexampleAlternatives
