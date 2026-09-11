import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Real

noncomputable section

/-!
# Bregman Analytic Bound — Dikin Ellipsoid bound for the finite 2×2 model

The phase axis `K = [[0,-1],[1,0]]` satisfies `K² = -I`.
The Bregman remainder `R(ε) = Δ(ε) - I - εK` has explicit entries
`[[cos ε - 1, -sin ε + ε], [sin ε - ε, cos ε - 1]]`.

Frobenius norm: ‖R‖_F = √(2(c-1)² + 2(s-ε)²) ≤ 2√2·ε² for |ε| ≤ 1.

Zero global axioms. No matrix typeclass dependencies.
-/

namespace InfoGeometry.Canonical.BregmanAnalyticBound

/-! ### Taylor bounds for sin/cos -/

lemma cos_one_bound (ε : ℝ) : |Real.cos ε - 1| ≤ ε ^ 2 := by
  have h_eq : Real.cos ε - 1 = -2 * ((Real.sin (ε / 2)) ^ 2) := by
    calc
      Real.cos ε - 1 = Real.cos ε - Real.cos 0 := by simp
      _ = -2 * Real.sin ((ε + 0)/2) * Real.sin ((ε - 0)/2) := by rw [Real.cos_sub_cos]
      _ = -2 * ((Real.sin (ε/2)) ^ 2) := by ring_nf
  rw [h_eq]
  calc
    |-2 * ((Real.sin (ε / 2)) ^ 2)| = 2 * ((Real.sin (ε / 2)) ^ 2) := by
      rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; simp
    _ ≤ 2 * ((ε / 2) ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have h := Real.sin_sq_le_sq (x := ε/2); nlinarith
    _ ≤ ε ^ 2 := by nlinarith

lemma sin_arg_bound (ε : ℝ) (hε : |ε| ≤ 1) : |Real.sin ε - ε| ≤ ε ^ 2 := by
  by_cases h_nonneg : 0 ≤ ε
  · rcases h_nonneg.eq_or_lt with (h_zero | h_pos)
    · subst h_zero; simp
    · have hx : ε ≤ 1 := (abs_le.mp hε).2
      have h_nonpos : Real.sin ε - ε ≤ 0 := by
        have h := Real.sin_lt h_pos; linarith
      have h_bound : |Real.sin ε - ε| ≤ ε ^ 3 / 4 := by
        rw [abs_of_nonpos h_nonpos]
        have h := Real.sin_gt_sub_cube h_pos (by linarith); linarith
      have h_final : ε ^ 3 / 4 ≤ ε ^ 2 := by nlinarith
      exact le_trans h_bound h_final
  · push_neg at h_nonneg
    have h_abs_bd : |(-ε)| ≤ 1 := by rwa [abs_neg]
    have h_nonneg' : 0 ≤ -ε := by linarith
    have h_bound' : |Real.sin (-ε) - (-ε)| ≤ (-ε) ^ 2 := by
      rcases h_nonneg'.eq_or_lt with (h_zero' | h_pos')
      · rw [← h_zero']; simp
      · have hx' : -ε ≤ 1 := (abs_le.mp h_abs_bd).2
        have h_nonpos' : Real.sin (-ε) - (-ε) ≤ 0 := by
          have h := Real.sin_lt h_pos'; linarith
        have h_bound'' : |Real.sin (-ε) - (-ε)| ≤ (-ε) ^ 3 / 4 := by
          rw [abs_of_nonpos h_nonpos']
          have h := Real.sin_gt_sub_cube h_pos' (by linarith); linarith
        have h_final' : (-ε) ^ 3 / 4 ≤ (-ε) ^ 2 := by nlinarith
        exact le_trans h_bound'' h_final'
    have h_eq : Real.sin (-ε) - (-ε) = -(Real.sin ε - ε) := by simp [Real.sin_neg]; ring
    have h_sq_eq : (-ε) ^ 2 = ε ^ 2 := by ring
    rw [h_eq, abs_neg, h_sq_eq] at h_bound'
    exact h_bound'

/-! ### Dikin ellipsoid bound — explicit Frobenius norm computation -/

/--
The Bregman remainder `R(ε) = Δ(ε) - I - εK` has Frobenius norm exactly
  ‖R‖_F = √(2·(cos ε - 1)² + 2·(sin ε - ε)²).

Bound: ‖R‖_F ≤ √2·|cos ε-1| + √2·|sin ε-ε| ≤ √2·ε² + √2·ε² = 2√2·ε².
-/
theorem bregman_quadratic_bound (ε : ℝ) (hε : |ε| ≤ 1) :
    Real.sqrt (2 * ((Real.cos ε - 1) ^ 2 + (Real.sin ε - ε) ^ 2)) ≤ (2 * Real.sqrt 2) * ε ^ 2 := by
  have hcos : |Real.cos ε - 1| ≤ ε ^ 2 := cos_one_bound ε
  have hsin : |Real.sin ε - ε| ≤ ε ^ 2 := sin_arg_bound ε hε
  -- Key inequality: √(a² + b²) ≤ |a| + |b|  (triangle inequality for Euclidean norm)
  -- So √(2c² + 2s²) = √2 · √(c² + s²) ≤ √2 · (|c| + |s|)
  calc
    Real.sqrt (2 * ((Real.cos ε - 1) ^ 2 + (Real.sin ε - ε) ^ 2))
        = Real.sqrt 2 * Real.sqrt ((Real.cos ε - 1) ^ 2 + (Real.sin ε - ε) ^ 2) := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
    _ ≤ Real.sqrt 2 * (|Real.cos ε - 1| + |Real.sin ε - ε|) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      -- √(a² + b²) ≤ |a| + |b|
      have h_nonneg_add : 0 ≤ |Real.cos ε - 1| + |Real.sin ε - ε| := by
        positivity
      have h_sq : ((Real.cos ε - 1) ^ 2 + (Real.sin ε - ε) ^ 2) ≤
                 (|Real.cos ε - 1| + |Real.sin ε - ε|) ^ 2 := by
        have hc : (Real.cos ε - 1) ^ 2 = |Real.cos ε - 1| ^ 2 := (sq_abs _).symm
        have hs : (Real.sin ε - ε) ^ 2 = |Real.sin ε - ε| ^ 2 := (sq_abs _).symm
        rw [hc, hs]
        -- (|a| + |b|)² = |a|² + |b|² + 2|a||b| ≥ |a|² + |b|² since 2|a||b| ≥ 0
        calc
          |Real.cos ε - 1| ^ 2 + |Real.sin ε - ε| ^ 2
              ≤ |Real.cos ε - 1| ^ 2 + |Real.sin ε - ε| ^ 2 +
                2 * |Real.cos ε - 1| * |Real.sin ε - ε| := by
            have h_nonneg_prod : 0 ≤ 2 * |Real.cos ε - 1| * |Real.sin ε - ε| := by
              positivity
            nlinarith
          _ = (|Real.cos ε - 1| + |Real.sin ε - ε|) ^ 2 := by ring
      have h_nonneg_sum_sq : 0 ≤ (Real.cos ε - 1) ^ 2 + (Real.sin ε - ε) ^ 2 := by positivity
      have h_sqrt_bound : Real.sqrt ((Real.cos ε - 1) ^ 2 + (Real.sin ε - ε) ^ 2) ≤
                         |Real.cos ε - 1| + |Real.sin ε - ε| := by
        calc
          Real.sqrt ((Real.cos ε - 1) ^ 2 + (Real.sin ε - ε) ^ 2) ≤
              Real.sqrt ((|Real.cos ε - 1| + |Real.sin ε - ε|) ^ 2) :=
            Real.sqrt_le_sqrt h_sq
          _ = |(|Real.cos ε - 1| + |Real.sin ε - ε|)| := Real.sqrt_sq_eq_abs _
          _ = |Real.cos ε - 1| + |Real.sin ε - ε| := abs_of_nonneg (by positivity)
      exact h_sqrt_bound
    _ ≤ Real.sqrt 2 * (ε ^ 2 + ε ^ 2) := by
      refine mul_le_mul_of_nonneg_left (add_le_add hcos hsin) (Real.sqrt_nonneg _)
    _ = Real.sqrt 2 * (2 * ε ^ 2) := by ring
    _ = (2 * Real.sqrt 2) * ε ^ 2 := by ring

end InfoGeometry.Canonical.BregmanAnalyticBound
