import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic

namespace InfoGeometry.Exceptional.CyclotomicIntegerClock

open Polynomial

theorem cyclotomic_twelve (Scalar : Type*) [CommRing Scalar] :
    cyclotomic 12 Scalar = X ^ 4 - X ^ 2 + 1 := by
  rw [show 12 = 6 * 2 by norm_num,
    ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide) Scalar,
    expand_eq_comp_X_pow, cyclotomic_six]
  simp
  ring

theorem cyclotomic_twelve_factorization :
    cyclotomic 12 ℤ * (X ^ 2 + 1) * (X ^ 6 - 1) = X ^ 12 - 1 := by
  rw [cyclotomic_twelve]
  ring

theorem cyclotomic_twelve_degree (Scalar : Type*) [CommRing Scalar] [Nontrivial Scalar] :
    (cyclotomic 12 Scalar).natDegree = 4 := by
  rw [natDegree_cyclotomic]
  decide

theorem pow_six_of_quartic {Carrier : Type*} [Ring Carrier]
    (operator : Carrier) (annihilates : operator ^ 4 - operator ^ 2 + 1 = 0) :
    operator ^ 6 = -1 := by
  have factorization :
      (operator ^ 4 - operator ^ 2 + 1) * (operator ^ 2 + 1) =
        operator ^ 6 + 1 := by noncomm_ring
  have vanishes : operator ^ 6 + 1 = 0 := by
    rw [← factorization, annihilates, zero_mul]
  exact eq_neg_of_add_eq_zero_left vanishes

theorem pow_twelve_of_quartic {Carrier : Type*} [Ring Carrier]
    (operator : Carrier) (annihilates : operator ^ 4 - operator ^ 2 + 1 = 0) :
    operator ^ 12 = 1 := by
  rw [show 12 = 6 * 2 by norm_num, pow_mul,
    pow_six_of_quartic operator annihilates]
  simp

def clock : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, -1;
     1, 0, 0,  0;
     0, 1, 0,  1;
     0, 0, 1,  0]

theorem clock_quartic : clock ^ 4 - clock ^ 2 + 1 = 0 := by
  decide

theorem clock_half_period : clock ^ 6 = -1 :=
  pow_six_of_quartic clock clock_quartic

theorem clock_period : clock ^ 12 = 1 :=
  pow_twelve_of_quartic clock clock_quartic

theorem clock_order : orderOf clock = 12 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) clock_period
  intro prime prime_is_prime divides
  have bound : prime ≤ 12 := Nat.le_of_dvd (by decide) divides
  have possibilities : prime = 2 ∨ prime = 3 := by
    interval_cases prime <;> norm_num at *
  rcases possibilities with rfl | rfl
  · rw [show 12 / 2 = 6 by norm_num, clock_half_period]
    decide
  · decide

theorem clock_power_eq_one_iff (exponent : ℕ) :
    clock ^ exponent = 1 ↔ 12 ∣ exponent := by
  rw [← orderOf_dvd_iff_pow_eq_one, clock_order]

theorem clock_annihilates_cyclotomic :
    aeval clock (cyclotomic 12 ℤ) = 0 := by
  rw [cyclotomic_twelve]
  simpa using clock_quartic

theorem clock_trace : Matrix.trace clock = 0 := by
  decide

theorem clock_sub_one_isUnit : IsUnit (clock - 1) := by
  refine ⟨⟨clock - 1, -(clock ^ 3 + clock ^ 2), ?_, ?_⟩, rfl⟩ <;> decide

theorem clock_not_unipotent : ¬ IsNilpotent (clock - 1) :=
  clock_sub_one_isUnit.not_isNilpotent

end InfoGeometry.Exceptional.CyclotomicIntegerClock
