/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.CyclotomicOperatorProjectors

namespace InfoGeometry.Algebra.Zorn.ConformalNPotent

open Complex

def IsNPotent {R : Type*} [CommRing R] (x : R) (n : ℕ) : Prop :=
  x ^ n = x

/-- Over ℂ, an `n`-potent element is either zero or a root of unity.

The field hypothesis is used through `mul_eq_zero`; this statement is not
claimed for arbitrary rings with zero divisors. -/
theorem complex_npotent_iff (x : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    IsNPotent x n ↔ x = 0 ∨ x ^ (n - 1) = 1 := by
  constructor
  · intro hx
    have hfactor : x * (x ^ (n - 1) - 1) = 0 := by
      dsimp [IsNPotent] at hx
      have hs : n - 1 + 1 = n := by omega
      calc
        x * (x ^ (n - 1) - 1) = x ^ (n - 1 + 1) - x := by
          rw [mul_sub, mul_one, pow_succ']
        _ = x ^ n - x := by rw [hs]
        _ = 0 := by rw [hx, sub_self]
    rcases mul_eq_zero.mp hfactor with hx0 | hroot
    · exact Or.inl hx0
    · right
      exact sub_eq_zero.mp hroot
  · rintro (rfl | hroot)
    · have hn0 : n ≠ 0 := by omega
      simp [IsNPotent, hn0]
    · dsimp [IsNPotent]
      have hs : n - 1 + 1 = n := by omega
      calc
        x ^ n = x ^ (n - 1 + 1) := by rw [hs]
        _ = x ^ (n - 1) * x := by rw [pow_succ']; ring
        _ = 1 * x := by rw [hroot]
        _ = x := one_mul x

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
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · norm_num [IsNPotent]
    · norm_num [IsNPotent]
    · norm_num [IsNPotent]
    · change I ^ 5 = I
      rw [show I ^ 5 = I ^ 4 * I by ring]
      rw [show I ^ 4 = 1 by norm_num [I_sq]]
      simp
    · change (-I) ^ 5 = -I
      rw [show (-I) ^ 5 = (-I) ^ 4 * (-I) by ring]
      rw [show (-I) ^ 4 = 1 by norm_num [I_sq]]
      simp

/-- A root of unity of order dividing `m` is `(m+1)`-potent. -/
theorem root_of_unity_succ_potent (x : ℂ) (m : ℕ) (h : x ^ m = 1) :
    IsNPotent x (m + 1) := by
  dsimp [IsNPotent]
  calc
    x ^ (m + 1) = x ^ m * x := by rw [pow_succ]
    _ = 1 * x := by rw [h]
    _ = x := one_mul x

/-- Exact zero/nonzero split for the successor-potent equation over ℂ. -/
theorem root_of_unity_succ_potent_iff (x : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    IsNPotent x (m + 1) ↔ x = 0 ∨ x ^ m = 1 := by
  simpa using (complex_npotent_iff x (n := m + 1) (by omega))

/-- A nontrivial finite-order complex phase has vanishing geometric sum. -/
theorem complex_root_of_unity_geometric_sum_eq_zero
    {u : ℂ} {n : ℕ} (hu : u ^ n = 1) (hune : u ≠ 1) :
    (∑ i ∈ Finset.range n, u ^ i) = 0 := by
  exact InfoGeometry.Algebra.CyclotomicOperatorProjectors.root_of_unity_geometric_sum_eq_zero_of_ne_one hu hune

/-- The low-degree member of the same pattern for the cubic equation. -/
theorem roots_of_2_are_3_potent (x : ℂ) (h : x ^ 2 = 1) :
    IsNPotent x 3 := by
  simpa using root_of_unity_succ_potent x 2 h

/-- The fourth-root case yields the 5-potent equation. -/
theorem roots_of_4_are_5_potent (x : ℂ) (h : x ^ 4 = 1) :
    IsNPotent x 5 := by
  simpa using root_of_unity_succ_potent x 4 h

/-- Roots of $X^{12} = 1$ are naturally 13-potent. -/
theorem roots_of_12_are_13_potent (x : ℂ) (h : x ^ 12 = 1) :
    IsNPotent x 13 := by
  simpa using root_of_unity_succ_potent x 12 h

/-- Sixth roots of unity are naturally 7-potent. -/
theorem roots_of_6_are_7_potent (x : ℂ) (h : x ^ 6 = 1) :
    IsNPotent x 7 := by
  simpa using root_of_unity_succ_potent x 6 h

/-- Tenth roots of unity are naturally 11-potent. -/
theorem roots_of_10_are_11_potent (x : ℂ) (h : x ^ 10 = 1) :
    IsNPotent x 11 := by
  simpa using root_of_unity_succ_potent x 10 h

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
