import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# The finite sixth-potent cyclotomic hull

This owner records the ring-theoretic identity `x^6 - x = x (x^5 - 1)` and
the inversion-stable fifth-root sector.  It does not assert a number-field
Galois representation or an analytic Fibonacci-category symmetry.
-/

namespace InfoGeometry.Arithmetic.CyclotomicFiveNPotentGaloisBridge

variable {K : Type*} [CommRing K] [IsDomain K]

def p6 (x : K) : K := x ^ 6 - x

theorem p6_factorization (x : K) :
    p6 x = x * (x ^ 5 - 1) := by
  dsimp [p6]
  ring

theorem mem_six_potent_hull_iff (x : K) :
    p6 x = 0 ↔ x = 0 ∨ x ^ 5 = 1 := by
  rw [p6_factorization, mul_eq_zero, sub_eq_zero]

theorem six_potent_of_pow_five_eq_one {x : K} (hx : x ^ 5 = 1) :
    x ^ 6 = x := by
  calc
    x ^ 6 = x ^ 5 * x := by ring
    _ = 1 * x := by rw [hx]
    _ = x := by rw [one_mul]

theorem fifth_root_square_is_fifth_root {x : K} (hx : x ^ 5 = 1) :
    (x ^ 2) ^ 5 = 1 := by
  calc
    (x ^ 2) ^ 5 = (x ^ 5) ^ 2 := by ring
    _ = 1 ^ 2 := by rw [hx]
    _ = 1 := by ring

theorem fifth_root_fourth_is_fifth_root {x : K} (hx : x ^ 5 = 1) :
    ((x ^ 2) ^ 4) ^ 5 = 1 := by
  calc
    ((x ^ 2) ^ 4) ^ 5 = ((x ^ 5) ^ 2) ^ 4 := by ring
    _ = (1 ^ 2) ^ 4 := by rw [hx]
    _ = 1 := by ring

theorem twist_fourth_mul_twist_eq_one {x : K} (hx : x ^ 5 = 1) :
    (x ^ 2) ^ 4 * (x ^ 2) = 1 := by
  calc
    (x ^ 2) ^ 4 * (x ^ 2) = (x ^ 5) ^ 2 := by ring
    _ = 1 := by rw [hx]; ring

theorem fibonacci_twist_mem_p6_hull {x : K} (hx : x ^ 5 = 1) :
    p6 (x ^ 2) = 0 := by
  rw [mem_six_potent_hull_iff]
  exact Or.inr (fifth_root_square_is_fifth_root hx)

theorem cyclotomic_inversion_mem_p6_hull {x : K} (hx : x ^ 5 = 1) :
    p6 ((x ^ 2) ^ 4) = 0 := by
  rw [mem_six_potent_hull_iff]
  exact Or.inr (fifth_root_fourth_is_fifth_root hx)

end InfoGeometry.Arithmetic.CyclotomicFiveNPotentGaloisBridge
