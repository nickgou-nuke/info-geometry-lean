import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
open Matrix
open Complex
open Real

set_option linter.unusedSimpArgs false

noncomputable section

namespace FibAnyonThm4

/-!
# Fibonacci F-matrix and R-matrix — Exact Symbolic Formalization
-/

def q : ℂ := Complex.exp (Real.pi * Complex.I / 5)

lemma q_pow_5 : q ^ 5 = -1 := by
  calc
    q ^ 5 = (Complex.exp (Real.pi * Complex.I / 5)) ^ 5 := rfl
    _ = Complex.exp ((5 : ℂ) * (Real.pi * Complex.I / 5)) := by rw [← Complex.exp_nat_mul]; ring_nf
    _ = Complex.exp (Real.pi * Complex.I) := by ring_nf
    _ = -1 := by rw [Complex.exp_mul_I]; simp

lemma h_cyclo : q^4 - q^3 + q^2 - q + 1 = 0 := by
  have h_prod : (q + 1) * (q^4 - q^3 + q^2 - q + 1) = 0 := by
    calc
      (q + 1) * (q^4 - q^3 + q^2 - q + 1) = q^5 + 1 := by ring_nf
      _ = (-1) + 1 := by rw [q_pow_5]
      _ = 0 := by ring_nf
  have h_q_ne_neg_one : q ≠ -1 := by
    intro h
    have h_eq : Real.pi * Complex.I / 5 = (Real.pi/5 : ℝ) * Complex.I := by
      push_cast
      ring_nf
    have h_re : q.re = Real.cos (Real.pi/5) := by
      calc
        q.re = (Complex.exp (Real.pi * Complex.I / 5)).re := by dsimp [q]
        _ = (Complex.exp ((Real.pi/5 : ℝ) * Complex.I)).re := by rw [h_eq]
        _ = Real.cos (Real.pi/5) := by rw [Complex.exp_ofReal_mul_I_re]
    have h_re2 : (-1 : ℂ).re = -1 := rfl
    have h_contra : Real.cos (Real.pi/5) = -1 := by
      rw [← h_re, h, h_re2]
    have hcos_pos : Real.cos (Real.pi/5) > 0 := by
      have h1 : -(Real.pi/2) < Real.pi/5 := by linarith [Real.pi_pos]
      have h2 : Real.pi/5 < Real.pi/2 := by linarith [Real.pi_pos]
      exact Real.cos_pos_of_mem_Ioo ⟨h1, h2⟩
    linarith
  rcases mul_eq_zero.mp h_prod with (hsum | hrest)
  · have hq : q = -1 := by
      calc q = (q + 1) - 1 := by ring_nf
           _ = 0 - 1 := by rw [hsum]
           _ = -1 := by ring_nf
    exact absurd hq h_q_ne_neg_one
  · exact hrest

noncomputable def τ : ℂ := q^2 - q^3
noncomputable def s : ℂ := Real.sqrt ((Real.sqrt 5 - 1) / 2)

lemma h_s_sq : s^2 - (q^2 - q^3) = 0 := by
  -- s² = (√5 - 1)/2 = τ_real, and τ = q² - q³ (proved below via cyclotomic)
  -- We need: (Real.sqrt ((Real.sqrt 5 - 1)/2))² = q² - q³
  have hs_sq_real : (s : ℂ)^2 = ((Real.sqrt 5 - 1)/2 : ℂ) := by
    dsimp [s]
    -- (Real.sqrt x)^2 = x for x ≥ 0
    have h_nonneg : 0 ≤ (Real.sqrt 5 - 1)/2 := by
      have h5_gt_1 : Real.sqrt 5 > 1 := by
        calc Real.sqrt 5 > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
          _ = 1 := by norm_num
      nlinarith
    exact_mod_cast Real.sq_sqrt h_nonneg
  have h_τ_eq : ((Real.sqrt 5 - 1)/2 : ℂ) = q^2 - q^3 := by
    -- This follows from q = exp(πi/5) and the cyclotomic relation
    -- Using q⁴ - q³ + q² - q + 1 = 0, we showed τ = q² - q³
    calc
      ((Real.sqrt 5 - 1)/2 : ℂ) = (q + q⁻¹ - 1 : ℂ) := by
        -- Cross relation: τ = q + q⁻¹ - 1, proved using Re(q) = cos(π/5) = (1+√5)/4
        have h_re_q : (q : ℂ).re = Real.cos (Real.pi / 5) := by
          calc
            (q : ℂ).re = (Complex.exp (Real.pi * Complex.I / 5)).re := rfl
            _ = (Complex.exp ((Real.pi/5 : ℝ) * Complex.I)).re := by
              congr 1; push_cast; ring_nf
            _ = Real.cos (Real.pi / 5) := by simpa using Complex.exp_ofReal_mul_I_re (Real.pi/5)
        have h_cos_val : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := Real.cos_pi_div_five
        have h_norm_sq : Complex.normSq q = 1 := by
          have h_im_q : (q : ℂ).im = Real.sin (Real.pi/5) := by
            calc
              (q : ℂ).im = (Complex.exp (Real.pi * Complex.I / 5)).im := rfl
              _ = (Complex.exp ((Real.pi/5 : ℝ) * Complex.I)).im := by
                congr 1; push_cast; ring_nf
              _ = Real.sin (Real.pi/5) := by simpa using Complex.exp_ofReal_mul_I_im (Real.pi/5)
          calc
            Complex.normSq q = q.re * q.re + q.im * q.im := by rw [Complex.normSq_apply]
            _ = (Real.cos (Real.pi/5))^2 + (Real.sin (Real.pi/5))^2 := by rw [h_re_q, h_im_q]; ring_nf
            _ = 1 := Real.cos_sq_add_sin_sq (Real.pi/5)
        have h_qinv_star : q⁻¹ = star q := by
          have hq_ne_zero : q ≠ 0 := Complex.exp_ne_zero _
          apply mul_right_cancel₀ hq_ne_zero
          calc
            q⁻¹ * q = 1 := by field_simp [hq_ne_zero]
            _ = (Complex.normSq q : ℂ) := by exact_mod_cast h_norm_sq.symm
            _ = (starRingEnd ℂ) q * q := by rw [Complex.normSq_eq_conj_mul_self]
            _ = star q * q := by simp
        have h_q_plus_qinv_re : (q + q⁻¹ : ℂ).re = (1 + Real.sqrt 5) / 2 := by
          calc
            (q + q⁻¹ : ℂ).re = (q : ℂ).re + (q⁻¹ : ℂ).re := by simp
            _ = (q : ℂ).re + (star q : ℂ).re := by rw [h_qinv_star]
            _ = (q : ℂ).re + (q : ℂ).re := by simp
            _ = 2 * (q : ℂ).re := by ring_nf
            _ = 2 * Real.cos (Real.pi/5) := by rw [h_re_q]
            _ = (1 + Real.sqrt 5) / 2 := by rw [h_cos_val]; ring_nf
        have h_q_plus_qinv_im : (q + q⁻¹ : ℂ).im = 0 := by
          calc
            (q + q⁻¹ : ℂ).im = (q : ℂ).im + (q⁻¹ : ℂ).im := by simp
            _ = (q : ℂ).im + (star q : ℂ).im := by rw [h_qinv_star]
            _ = (q : ℂ).im + (-(q : ℂ).im) := by simp
            _ = 0 := by ring_nf
        apply Complex.ext
        · calc
            ((Real.sqrt 5 - 1)/2 : ℂ).re = (Real.sqrt 5 - 1)/2 := by simp
            _ = (1 + Real.sqrt 5)/2 - 1 := by ring_nf
            _ = (q + q⁻¹ : ℂ).re - 1 := by rw [h_q_plus_qinv_re]
            _ = (q + q⁻¹ - 1 : ℂ).re := by simp
        · calc
            ((Real.sqrt 5 - 1)/2 : ℂ).im = 0 := by simp
            _ = (q + q⁻¹ : ℂ).im := by rw [h_q_plus_qinv_im]
            _ = (q + q⁻¹ - 1 : ℂ).im := by simp
      _ = q^2 - q^3 := by
        have h_qinv_neg_q4 : q⁻¹ = -(q^4) := by
          have hq_ne_zero : q ≠ 0 := Complex.exp_ne_zero _
          field_simp [hq_ne_zero]
          rw [q_pow_5]
          ring_nf
        calc
          q + q⁻¹ - 1 = q + (-(q^4)) - 1 := by rw [h_qinv_neg_q4]
          _ = q - q^4 - 1 := by ring_nf
          _ = q^2 - q^3 := by
            -- Add the cyclotomic identity times 0:
            -- (q⁴ - q³ + q² - q + 1) = 0
            -- so q - q⁴ - 1 = q² - q³
            apply sub_eq_zero.mp
            calc
              (q - q^4 - 1) - (q^2 - q^3) = -(q^4 - q^3 + q^2 - q + 1) := by ring_nf
              _ = -0 := by rw [h_cyclo]
              _ = 0 := by ring_nf
  rw [hs_sq_real, h_τ_eq, sub_self]

noncomputable def F : Matrix (Fin 2) (Fin 2) ℂ := !![τ, s; s, -τ]
noncomputable def R : Matrix (Fin 2) (Fin 2) ℂ := !![q^4, 0; 0, -q^2]
noncomputable def R_prime : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -q^2]

noncomputable def B : Matrix (Fin 2) (Fin 2) ℂ := F * R * F
noncomputable def σ1 : Matrix (Fin 2) (Fin 2) ℂ := R
noncomputable def σ2 : Matrix (Fin 2) (Fin 2) ℂ := B

noncomputable def F_sq_eq_I_def := F * F - 1
theorem F_sq_eq_I : F * F = 1 := by
  have h : F_sq_eq_I_def = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    · -- (0,0)
      have h_calc : (1) * (s^2 - (q^2 - q^3)) + (q^2  -  q  -  1) * (q^4 - q^3 + q^2 - q + 1) = 0 := by
        rw [h_s_sq, h_cyclo]
        ring_nf
      dsimp [F_sq_eq_I_def]
      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]
      rw [← h_calc]
      ring_nf
    · -- (0,1)
      dsimp [F_sq_eq_I_def]
      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]
      ring_nf
    · -- (1,0)
      dsimp [F_sq_eq_I_def]
      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]
      ring_nf
    · -- (1,1)
      have h_calc : (1) * (s^2 - (q^2 - q^3)) + (q^2  -  q  -  1) * (q^4 - q^3 + q^2 - q + 1) = 0 := by
        rw [h_s_sq, h_cyclo]
        ring_nf
      dsimp [F_sq_eq_I_def]
      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]
      rw [← h_calc]
      ring_nf
  exact sub_eq_zero.mp h

noncomputable def right_hexagon_def := R * F * R - F * R_prime * F
theorem right_hexagon : R * F * R = F * R_prime * F := by
  have h : right_hexagon_def = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    · -- (0,0)
      have h_calc : (q^2) * (s^2 - (q^2 - q^3)) + (-q^7  +  q^5) * (q^4 - q^3 + q^2 - q + 1) = 0 := by
        rw [h_s_sq, h_cyclo]
        ring_nf
      dsimp [right_hexagon_def]
      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]
      rw [← h_calc]
      ring_nf
    · -- (0,1)
      have h_calc : (0) * (s^2 - (q^2 - q^3)) + (-q^2 * s) * (q^4 - q^3 + q^2 - q + 1) = 0 := by
        rw [h_s_sq, h_cyclo]
        ring_nf
      dsimp [right_hexagon_def]
      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]
      rw [← h_calc]
      ring_nf
    · -- (1,0)
      have h_calc : (0) * (s^2 - (q^2 - q^3)) + (-q^2 * s) * (q^4 - q^3 + q^2 - q + 1) = 0 := by
        rw [h_s_sq, h_cyclo]
        ring_nf
      dsimp [right_hexagon_def]
      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]
      rw [← h_calc]
      ring_nf
    · -- (1,1)
      have h_calc : (-1) * (s^2 - (q^2 - q^3)) + (q^4  -  q^2) * (q^4 - q^3 + q^2 - q + 1) = 0 := by
        rw [h_s_sq, h_cyclo]
        ring_nf
      dsimp [right_hexagon_def]
      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]
      rw [← h_calc]
      ring_nf
  exact sub_eq_zero.mp h

noncomputable def braid_relation_def := σ1 * σ2 * σ1 - σ2 * σ1 * σ2
theorem braid_relation : σ1 * σ2 * σ1 = σ2 * σ1 * σ2 := by
  have h : braid_relation_def = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    · -- (0,0)
      have h_calc : (3 * q^16  -  6 * q^15  +  5 * q^14  -  4 * q^13  +  3 * q^12  -  q^11  -  q^10  -  q^8 * s^2) * (s^2 - (q^2 - q^3)) + (-q^20  +  3 * q^19  -  2 * q^18  -  2 * q^17  +  3 * q^16  -  3 * q^15  +  4 * q^14  -  q^13  -  q^12) * (q^4 - q^3 + q^2 - q + 1) = 0 := by
        rw [h_s_sq, h_cyclo]
        ring_nf
      dsimp [braid_relation_def]
      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]
      rw [← h_calc]
      ring_nf
    · -- (0,1)
      have h_calc : (-2 * q^13 * s  +  2 * q^12 * s  -  2 * q^11 * s  +  2 * q^10 * s) * (s^2 - (q^2 - q^3)) + (q^17 * s  -  2 * q^16 * s  +  q^15 * s  +  q^12 * s  -  q^10 * s) * (q^4 - q^3 + q^2 - q + 1) = 0 := by
        rw [h_s_sq, h_cyclo]
        ring_nf
      dsimp [braid_relation_def]
      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]
      rw [← h_calc]
      ring_nf
    · -- (1,0)
      have h_calc : (-2 * q^13 * s  +  2 * q^12 * s  -  2 * q^11 * s  +  2 * q^10 * s) * (s^2 - (q^2 - q^3)) + (q^17 * s  -  2 * q^16 * s  +  q^15 * s  +  q^12 * s  -  q^10 * s) * (q^4 - q^3 + q^2 - q + 1) = 0 := by
        rw [h_s_sq, h_cyclo]
        ring_nf
      dsimp [braid_relation_def]
      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]
      rw [← h_calc]
      ring_nf
    · -- (1,1)
      have h_calc : (-q^18  +  2 * q^17  -  3 * q^16  +  4 * q^15  -  5 * q^14  +  5 * q^13  -  2 * q^12  +  q^10 * s^2  +  q^8) * (s^2 - (q^2 - q^3)) + (q^17  -  2 * q^16  +  2 * q^15  -  q^14  -  q^13  +  q^11) * (q^4 - q^3 + q^2 - q + 1) = 0 := by
        rw [h_s_sq, h_cyclo]
        ring_nf
      dsimp [braid_relation_def]
      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]
      rw [← h_calc]
      ring_nf
  exact sub_eq_zero.mp h

end FibAnyonThm4

end
