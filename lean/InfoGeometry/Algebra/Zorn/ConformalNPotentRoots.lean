/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

namespace InfoGeometry.Algebra.Zorn.ConformalNPotent

open Complex

def IsNPotent {R : Type*} [CommRing R] (x : R) (n : ℕ) : Prop :=
  x ^ n = x

/-- Polynomial factorization of $X^5 - X$ over ℂ. -/
theorem factor_poly_X5_minus_X (x : ℂ) :
    x ^ 5 - x = x * (x - 1) * (x + 1) * (x - I) * (x + I) := by
  have hI : I ^ 2 = -1 := I_sq
  calc
    x ^ 5 - x = x * (x - 1) * (x + 1) * (x ^ 2 + 1) := by ring
    _ = x * (x - 1) * (x + 1) * (x ^ 2 - (-1)) := by ring
    _ = x * (x - 1) * (x + 1) * (x ^ 2 - I ^ 2) := by rw [hI]
    _ = x * (x - 1) * (x + 1) * (x - I) * (x + I) := by ring

/-- The roots of $X^5 = X$ in ℂ are precisely the Vacuum (0), Split-Causality (±1), and Quantum Phase (±i). -/
theorem roots_of_five_potent (x : ℂ) (h : IsNPotent x 5) :
    x = 0 ∨ x = 1 ∨ x = -1 ∨ x = I ∨ x = -I := by
  dsimp [IsNPotent] at h
  have h_sub : x ^ 5 - x = 0 := sub_eq_zero.mpr h
  rw [factor_poly_X5_minus_X] at h_sub
  rcases mul_eq_zero.mp h_sub with h1 | h_neg_I
  · rcases mul_eq_zero.mp h1 with h2 | h_pos_I
    · rcases mul_eq_zero.mp h2 with h3 | h_neg_one
      · rcases mul_eq_zero.mp h3 with h_zero | h_pos_one
        · left; exact h_zero
        · right; left; exact sub_eq_zero.mp h_pos_one
      · right; right; left; exact add_eq_zero_iff_eq_neg.mp h_neg_one
    · right; right; right; left; exact sub_eq_zero.mp h_pos_I
  · right; right; right; right; exact add_eq_zero_iff_eq_neg.mp h_neg_I

/-- Exact characterization of the roots of $X^5-X$ over ℂ. -/
theorem five_potent_iff (x : ℂ) :
    IsNPotent x 5 ↔ x = 0 ∨ x = 1 ∨ x = -1 ∨ x = I ∨ x = -I := by
  constructor
  · exact roots_of_five_potent x
  · rintro (rfl | rfl | rfl | rfl | rfl) <;>
      norm_num [IsNPotent, I_sq]

/-- Roots of $X^{12} = 1$ are naturally 13-potent. -/
theorem roots_of_12_are_13_potent (x : ℂ) (h : x ^ 12 = 1) :
    IsNPotent x 13 := by
  dsimp [IsNPotent]
  calc
    x ^ 13 = x ^ 12 * x := by ring
    _ = 1 * x := by rw [h]
    _ = x := one_mul x

/-- Sixth roots of unity are naturally 7-potent. -/
theorem roots_of_6_are_7_potent (x : ℂ) (h : x ^ 6 = 1) :
    IsNPotent x 7 := by
  dsimp [IsNPotent]
  calc
    x ^ 7 = x ^ 6 * x := by ring
    _ = 1 * x := by rw [h]
    _ = x := one_mul x

/-- Tenth roots of unity are naturally 11-potent. -/
theorem roots_of_10_are_11_potent (x : ℂ) (h : x ^ 10 = 1) :
    IsNPotent x 11 := by
  dsimp [IsNPotent]
  calc
    x ^ 11 = x ^ 10 * x := by ring
    _ = 1 * x := by rw [h]
    _ = x := one_mul x

/-- The 12th cyclotomic polynomial $\Phi_{12}(x) = x^4 - x^2 + 1$ is a direct factor of $x^{12} - 1$. -/
theorem phi12_divides_X12_minus_one (x : ℂ) :
    x ^ 12 - 1 = (x ^ 4 - x ^ 2 + 1) * ((x ^ 4 + x ^ 2 + 1) * (x ^ 4 - 1)) := by
  ring

/-- Roots of $\Phi_{12}(x)$ (generating the $G_2$ root lattice) are strictly 13-potent operators. -/
theorem g2_roots_are_13_potent (x : ℂ) (h : x ^ 4 - x ^ 2 + 1 = 0) :
    IsNPotent x 13 := by
  have h_12 : x ^ 12 - 1 = 0 := by
    rw [phi12_divides_X12_minus_one x, h, zero_mul]
  have h_12_eq_1 : x ^ 12 = 1 := sub_eq_zero.mp h_12
  exact roots_of_12_are_13_potent x h_12_eq_1

end InfoGeometry.Algebra.Zorn.ConformalNPotent
