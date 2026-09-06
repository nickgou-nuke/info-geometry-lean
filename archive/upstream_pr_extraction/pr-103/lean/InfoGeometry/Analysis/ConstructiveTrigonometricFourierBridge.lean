import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Constructive Trigonometric L²(0, 1) Hilbert Orthogonality Bridge

This module formalizes genuine Lebesgue interval integrals for trigonometric modes in Mathlib 4:
1. **Exact L² Energy of the Sine Mode $\sin(2\pi n x)$ on $[0, 1]$**:
   $$\int_0^1 \sin^2(2\pi n x) \, dx = \frac{1}{2} \quad (\forall n \ge 1)$$
2. **Exact L² Energy of the Cosine Mode $\cos(2\pi n x)$ on $[0, 1]$**:
   $$\int_0^1 \cos^2(2\pi n x) \, dx = \frac{1}{2} \quad (\forall n \ge 1)$$
3. **Exact Cross-Orthogonality Between Sine and Cosine Modes**:
   $$\int_0^1 \sin(2\pi n x) \cos(2\pi n x) \, dx = 0 \quad (\forall n \ge 1)$$
-/

noncomputable section

namespace InfoGeometry.Analysis.ConstructiveFourier

open Real intervalIntegral

/-- 🏆 THEOREM 1: Exact L² Energy of Sine Mode on [0, 1] for n ≥ 1 -/
theorem integral_sin_sq_two_pi (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (0:ℝ)..1, sin (2 * π * (n : ℝ) * x) ^ 2 = 1 / 2 := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have h_two_pi_n_ne : 2 * π * (n : ℝ) ≠ 0 := by
    have hpi : 0 < π := Real.pi_pos
    positivity
  have h_comp := integral_comp_mul_left (f := fun u => sin u ^ 2) (a := (0 : ℝ)) (b := (1 : ℝ)) (c := 2 * π * (n : ℝ))
  rw [mul_zero, mul_one] at h_comp
  have h_subst : (∫ x in (0:ℝ)..1, sin (2 * π * (n : ℝ) * x) ^ 2) =
      (2 * π * (n : ℝ))⁻¹ * ∫ u in (0:ℝ)..(2 * π * (n : ℝ)), sin u ^ 2 := by
    have h := h_comp h_two_pi_n_ne
    rw [smul_eq_mul] at h
    exact h
  rw [h_subst, integral_sin_sq]
  have h_sin_2pi_n : sin (2 * π * (n : ℝ)) = 0 := by
    have : 2 * π * (n : ℝ) = (2 * n : ℕ) * π := by
      push_cast
      ring
    rw [this, sin_nat_mul_pi]
  have h_sin_zero : sin (0 : ℝ) = 0 := sin_zero
  rw [h_sin_2pi_n, h_sin_zero]
  have hpi_ne : π ≠ 0 := Real.pi_ne_zero
  have hn_ne : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- 🏆 THEOREM 2: Exact L² Energy of Cosine Mode on [0, 1] for n ≥ 1 -/
theorem integral_cos_sq_two_pi (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (0:ℝ)..1, cos (2 * π * (n : ℝ) * x) ^ 2 = 1 / 2 := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have h_two_pi_n_ne : 2 * π * (n : ℝ) ≠ 0 := by
    have hpi : 0 < π := Real.pi_pos
    positivity
  have h_comp := integral_comp_mul_left (f := fun u => cos u ^ 2) (a := (0 : ℝ)) (b := (1 : ℝ)) (c := 2 * π * (n : ℝ))
  rw [mul_zero, mul_one] at h_comp
  have h_subst : (∫ x in (0:ℝ)..1, cos (2 * π * (n : ℝ) * x) ^ 2) =
      (2 * π * (n : ℝ))⁻¹ * ∫ u in (0:ℝ)..(2 * π * (n : ℝ)), cos u ^ 2 := by
    have h := h_comp h_two_pi_n_ne
    rw [smul_eq_mul] at h
    exact h
  rw [h_subst, integral_cos_sq]
  have h_sin_2pi_n : sin (2 * π * (n : ℝ)) = 0 := by
    have : 2 * π * (n : ℝ) = (2 * n : ℕ) * π := by
      push_cast
      ring
    rw [this, sin_nat_mul_pi]
  have h_sin_zero : sin (0 : ℝ) = 0 := sin_zero
  rw [h_sin_2pi_n, h_sin_zero]
  have hpi_ne : π ≠ 0 := Real.pi_ne_zero
  have hn_ne : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- 🏆 THEOREM 3: Exact Cross Orthogonality Between Sine and Cosine Modes on [0, 1] -/
theorem integral_sin_cos_two_pi_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (0:ℝ)..1, sin (2 * π * (n : ℝ) * x) * cos (2 * π * (n : ℝ) * x) = 0 := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have h_two_pi_n_ne : 2 * π * (n : ℝ) ≠ 0 := by
    have hpi : 0 < π := Real.pi_pos
    positivity
  have h_ident : ∀ x : ℝ, sin (2 * π * (n : ℝ) * x) * cos (2 * π * (n : ℝ) * x) =
      (1 / 2) * sin (4 * π * (n : ℝ) * x) := by
    intro x
    have h2 := sin_two_mul (2 * π * (n : ℝ) * x)
    have h_four : 2 * (2 * π * (n : ℝ) * x) = 4 * π * (n : ℝ) * x := by ring
    rw [h_four] at h2
    linarith
  have h_int_eq : (∫ x in (0:ℝ)..1, sin (2 * π * (n : ℝ) * x) * cos (2 * π * (n : ℝ) * x)) =
      ∫ x in (0:ℝ)..1, (1 / 2) * sin (4 * π * (n : ℝ) * x) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact h_ident x
  rw [h_int_eq, integral_const_mul]
  have h_four_pi_n_ne : 4 * π * (n : ℝ) ≠ 0 := by
    have hpi : 0 < π := Real.pi_pos
    positivity
  have h_comp := integral_comp_mul_left (f := fun u => sin u) (a := (0 : ℝ)) (b := (1 : ℝ)) (c := 4 * π * (n : ℝ))
  rw [mul_zero, mul_one] at h_comp
  have h_sin_int : (∫ x in (0:ℝ)..1, sin (4 * π * (n : ℝ) * x)) =
      (4 * π * (n : ℝ))⁻¹ * ∫ u in (0:ℝ)..(4 * π * (n : ℝ)), sin u := by
    have h := h_comp h_four_pi_n_ne
    rw [smul_eq_mul] at h
    exact h
  have h_sin_eval : (∫ u in (0:ℝ)..(4 * π * (n : ℝ)), sin u) =
      cos 0 - cos (4 * π * (n : ℝ)) := by
    exact integral_sin (a := 0) (b := 4 * π * (n : ℝ))
  have h_cos_zero : cos 0 = 1 := Real.cos_zero
  have h_cos_4pi_n : cos (4 * π * (n : ℝ)) = 1 := by
    have : 4 * π * (n : ℝ) = (2 * n : ℕ) * (2 * π) := by
      push_cast
      ring
    rw [this, cos_nat_mul_two_pi]
  rw [h_sin_int, h_sin_eval, h_cos_zero, h_cos_4pi_n, sub_self, mul_zero, mul_zero]

end InfoGeometry.Analysis.ConstructiveFourier
