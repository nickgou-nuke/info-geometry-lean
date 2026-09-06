import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Quaternion
import InfoGeometry.Canonical.MixedVarianceDeviance

namespace InfoGeometry.Canonical

open Real

noncomputable def delta_mix (D_mix : ℝ) (x μ : ℝ) : ℝ :=
  if x ≥ μ then sqrt D_mix else - sqrt D_mix

noncomputable def delta_plus (δ : ℝ) : ℝ := max δ 0

noncomputable def delta_minus (δ : ℝ) : ℝ := max (-δ) 0

theorem delta_sq_add_sq (D_mix x μ : ℝ) (hD : D_mix ≥ 0) :
    (delta_plus (delta_mix D_mix x μ))^2 +
      (delta_minus (delta_mix D_mix x μ))^2 = D_mix := by
  dsimp [delta_plus, delta_minus, delta_mix]
  split_ifs with h
  · have h_max_1 : max (sqrt D_mix) 0 = sqrt D_mix :=
      max_eq_left (sqrt_nonneg _)
    have h_max_2 : max (- sqrt D_mix) 0 = 0 := by
      apply max_eq_right
      linarith [sqrt_nonneg D_mix]
    rw [h_max_1, h_max_2]
    ring_nf
    exact sq_sqrt hD
  · have h_max_1 : max (- sqrt D_mix) 0 = 0 := by
      apply max_eq_right
      linarith [sqrt_nonneg D_mix]
    have h_max_2 : max (- (- sqrt D_mix)) 0 = sqrt D_mix := by
      rw [neg_neg]
      exact max_eq_left (sqrt_nonneg _)
    rw [h_max_1, h_max_2]
    ring_nf
    exact sq_sqrt hD

noncomputable def q_anom (D_mix x μ L H κ_L κ_H : ℝ) : Quaternion ℝ :=
  ⟨delta_plus (delta_mix D_mix x μ),
   delta_minus (delta_mix D_mix x μ),
   sqrt κ_L * L,
   sqrt κ_H * H⟩

theorem normSq_q_anom (D_mix x μ L H κ_L κ_H : ℝ)
    (hD : D_mix ≥ 0) (hL : κ_L ≥ 0) (hH : κ_H ≥ 0) :
    (q_anom D_mix x μ L H κ_L κ_H).normSq =
      D_mix + κ_L * L^2 + κ_H * H^2 := by
  dsimp [q_anom]
  rw [Quaternion.normSq_def']
  dsimp
  have h1 : (delta_plus (delta_mix D_mix x μ)) ^ 2 +
      (delta_minus (delta_mix D_mix x μ)) ^ 2 = D_mix :=
    delta_sq_add_sq D_mix x μ hD
  have h2 : (sqrt κ_L * L) ^ 2 = κ_L * L ^ 2 := by
    rw [mul_pow, sq_sqrt hL]
  have h3 : (sqrt κ_H * H) ^ 2 = κ_H * H ^ 2 := by
    rw [mul_pow, sq_sqrt hH]
  linarith

end InfoGeometry.Canonical
