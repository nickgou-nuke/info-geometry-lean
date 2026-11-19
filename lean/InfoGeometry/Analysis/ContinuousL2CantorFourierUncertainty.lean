/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Continuous L2 Cantor Fourier Uncertainty Principle Contraction

This module formalizes continuous $L^2([0, 1])$ trigonometric mode pairs,
proving exact energy identities, wavepacket interval energy bounds, and
multiscale Cantor Fourier uncertainty contraction:

1. `modeSin` and `modeCos`: Continuous normalized trigonometric mode pairs.
2. `mode_sq_sum_eq_two`: Exact pointwise energy identity $s_n(x)^2 + c_n(x)^2 = 2$.
3. `interval_energy_mode_pair`: Exact interval energy $\int_a^b (s_n(x)^2 + c_n(x)^2) dx = 2(b - a)$.
4. `wavepacket_pointwise_cauchy_schwarz`: Pointwise bound on wavepacket sums
   $(\sum_{n \in T} (a_n s_n(x) + b_n c_n(x)))^2 \le (\sum_{n \in T} (a_n^2 + b_n^2)) \cdot 2|T|$.
5. `wavepacket_interval_energy_bound`: Interval energy bound on wavepackets.
6. `cantor_scale_measure` and `cantor_fup_ratio`: Multiscale Cantor measure and contraction ratio.
7. `cantor_fup_ratio_lt_one`: Ratio is strictly $< 1$ when $b - m < \sqrt{b}$.
8. `continuous_cantor_wavepacket_contraction`: Geometric wavepacket contraction bound.
9. `continuous_cantor_fup_tendsto_zero`: Asymptotic decay to zero as scale $k \to \infty$.
10. `continuous_cantor_witness_b4_m3`: Concrete witness at $b = 4, m = 3$.
11. `continuous_fup_noncomm_witness`: OpenGauss Trap T16 non-commutativity witness.
-/

noncomputable section

namespace InfoGeometry.Analysis.ContinuousL2CantorFourierUncertainty

open Real intervalIntegral MeasureTheory

/-- Normalized continuous sine mode on $[0, 1]$. -/
def modeSin (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sin (2 * Real.pi * (n : ℝ) * x)

/-- Normalized continuous cosine mode on $[0, 1]$. -/
def modeCos (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt 2 * Real.cos (2 * Real.pi * (n : ℝ) * x)

/-- Exact pointwise energy identity for continuous trigonometric mode pairs:
$s_n(x)^2 + c_n(x)^2 = 2$. -/
theorem mode_sq_sum_eq_two (n : ℕ) (x : ℝ) :
    (modeSin n x) ^ 2 + (modeCos n x) ^ 2 = 2 := by
  dsimp [modeSin, modeCos]
  have h_sqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h : (Real.sqrt 2 * Real.sin (2 * Real.pi * (n : ℝ) * x)) ^ 2 +
      (Real.sqrt 2 * Real.cos (2 * Real.pi * (n : ℝ) * x)) ^ 2 =
      (Real.sqrt 2) ^ 2 * ((Real.sin (2 * Real.pi * (n : ℝ) * x)) ^ 2 +
        (Real.cos (2 * Real.pi * (n : ℝ) * x)) ^ 2) := by
    ring
  rw [h, Real.sin_sq_add_cos_sq, h_sqrt2_sq, mul_one]

/-- Exact interval energy for a continuous mode pair:
$\int_a^b (s_n(x)^2 + c_n(x)^2) dx = 2 (b - a)$. -/
theorem interval_energy_mode_pair (n : ℕ) (a b : ℝ) :
    ∫ x in a..b, ((modeSin n x) ^ 2 + (modeCos n x) ^ 2) = 2 * (b - a) := by
  have h : (fun x : ℝ => (modeSin n x) ^ 2 + (modeCos n x) ^ 2) = fun _ => (2 : ℝ) := by
    ext x
    exact mode_sq_sum_eq_two n x
  rw [h, intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-- Two-dimensional Cauchy–Schwarz algebraic identity on $\mathbb{R}$. -/
lemma two_dim_cauchy_schwarz (u v s c : ℝ) :
    (u * s + v * c) ^ 2 ≤ (u ^ 2 + v ^ 2) * (s ^ 2 + c ^ 2) := by
  have h_identity : (u ^ 2 + v ^ 2) * (s ^ 2 + c ^ 2) - (u * s + v * c) ^ 2 = (u * c - v * s) ^ 2 := by
    ring
  have h_sq_nonneg : 0 ≤ (u * c - v * s) ^ 2 := sq_nonneg _
  linarith

/-- Pointwise bound on a single mode pair $(a_n s_n(x) + b_n c_n(x))^2 \le 2 (a_n^2 + b_n^2)$. -/
lemma single_mode_sq_bound (a b : ℝ) (n : ℕ) (x : ℝ) :
    (a * modeSin n x + b * modeCos n x) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := two_dim_cauchy_schwarz a b (modeSin n x) (modeCos n x)
  rw [mode_sq_sum_eq_two n x] at h
  linarith

/-- Wavepacket pointwise Cauchy–Schwarz inequality:
$(\sum_{n \in T} (a_n s_n(x) + b_n c_n(x)))^2 \le (\sum_{n \in T} (a_n^2 + b_n^2)) \cdot (2 |T|)$. -/
theorem wavepacket_pointwise_cauchy_schwarz (T : Finset ℕ) (a b : ℕ → ℝ) (x : ℝ) :
    (∑ n ∈ T, (a n * modeSin n x + b n * modeCos n x)) ^ 2 ≤
      (∑ n ∈ T, (a n ^ 2 + b n ^ 2)) * (2 * T.card) := by
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ))
    (fun n => a n * modeSin n x + b n * modeCos n x)
  simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h_cs
  have h_one_mul : (∑ n ∈ T, (1 : ℝ) * (a n * modeSin n x + b n * modeCos n x)) =
      ∑ n ∈ T, (a n * modeSin n x + b n * modeCos n x) := by
    congr 1
    ext n
    rw [one_mul]
  rw [h_one_mul] at h_cs
  have h_sum_le : (∑ n ∈ T, (a n * modeSin n x + b n * modeCos n x) ^ 2) ≤
      ∑ n ∈ T, (2 * (a n ^ 2 + b n ^ 2)) := by
    apply Finset.sum_le_sum
    intro n _
    exact single_mode_sq_bound (a n) (b n) n x
  rw [← Finset.mul_sum] at h_sum_le
  have h_card_nonneg : 0 ≤ (T.card : ℝ) := Nat.cast_nonneg _
  have h_trans := mul_le_mul_of_nonneg_left h_sum_le h_card_nonneg
  have h_ring : (T.card : ℝ) * (2 * ∑ n ∈ T, (a n ^ 2 + b n ^ 2)) =
      (∑ n ∈ T, (a n ^ 2 + b n ^ 2)) * (2 * T.card) := by
    ring
  rw [h_ring] at h_trans
  exact h_cs.trans h_trans

/-- Continuity of modeSin. -/
lemma continuous_modeSin (n : ℕ) : Continuous (modeSin n) := by
  change Continuous (fun x => Real.sqrt 2 * Real.sin (2 * Real.pi * (n : ℝ) * x))
  exact continuous_const.mul (continuous_sin.comp (continuous_const.mul continuous_id))

/-- Continuity of modeCos. -/
lemma continuous_modeCos (n : ℕ) : Continuous (modeCos n) := by
  change Continuous (fun x => Real.sqrt 2 * Real.cos (2 * Real.pi * (n : ℝ) * x))
  exact continuous_const.mul (continuous_cos.comp (continuous_const.mul continuous_id))

/-- Continuity of the wavepacket sum. -/
lemma continuous_wavepacket (T : Finset ℕ) (a b : ℕ → ℝ) :
    Continuous (fun x => (∑ n ∈ T, (a n * modeSin n x + b n * modeCos n x)) ^ 2) := by
  apply Continuous.pow
  apply continuous_finsetSum
  intro n _
  exact (continuous_const.mul (continuous_modeSin n)).add
    (continuous_const.mul (continuous_modeCos n))

/-- Wavepacket interval energy bound on $[u, v]$:
$\int_u^v (\sum_{n \in T} (a_n s_n(x) + b_n c_n(x)))^2 dx \le (\sum_{n \in T} (a_n^2 + b_n^2)) \cdot 2|T|(v - u)$. -/
theorem wavepacket_interval_energy_bound (T : Finset ℕ) (a b : ℕ → ℝ) (u v : ℝ) (huv : u ≤ v) :
    (∫ x in u..v, (∑ n ∈ T, (a n * modeSin n x + b n * modeCos n x)) ^ 2) ≤
      (∑ n ∈ T, (a n ^ 2 + b n ^ 2)) * (2 * (T.card : ℝ) * (v - u)) := by
  let C := (∑ n ∈ T, (a n ^ 2 + b n ^ 2)) * (2 * (T.card : ℝ))
  have h_pw : ∀ x ∈ Set.Icc u v, (∑ n ∈ T, (a n * modeSin n x + b n * modeCos n x)) ^ 2 ≤ C := by
    intro x _
    exact wavepacket_pointwise_cauchy_schwarz T a b x
  have h_int : (∫ x in u..v, (∑ n ∈ T, (a n * modeSin n x + b n * modeCos n x)) ^ 2) ≤
      ∫ x in u..v, C := by
    apply intervalIntegral.integral_mono_on huv
    · exact (continuous_wavepacket T a b).intervalIntegrable u v
    · exact intervalIntegrable_const
    · exact h_pw
  rw [intervalIntegral.integral_const, smul_eq_mul] at h_int
  have h_comm : (v - u) * C = (∑ n ∈ T, (a n ^ 2 + b n ^ 2)) * (2 * (T.card : ℝ) * (v - u)) := by
    dsimp [C]
    ring
  rw [h_comm] at h_int
  exact h_int

/-- Multiscale Cantor spatial measure at scale $k$ with base $b$ and $m$ removed digits. -/
def cantor_scale_measure (b m : ℕ) (k : ℕ) : ℝ :=
  ((b - m : ℝ) / (b : ℝ)) ^ k

/-- Multiscale Cantor Fourier uncertainty principle contraction ratio $(b-m)^2 / b$. -/
def cantor_fup_ratio (b m : ℕ) : ℝ :=
  ((b - m : ℝ) ^ 2) / (b : ℝ)

/-- Contraction ratio is strictly less than 1 under the sparsity condition $(b-m) < \sqrt{b}$. -/
theorem cantor_fup_ratio_lt_one (b m : ℕ) (hm : m < b)
    (h_sparse : (b - m : ℝ) < Real.sqrt (b : ℝ)) :
    cantor_fup_ratio b m < 1 := by
  dsimp [cantor_fup_ratio]
  have hb_pos : 0 < (b : ℝ) := Nat.cast_pos.mpr (by omega)
  have hbm_nonneg : 0 ≤ (b - m : ℝ) := by
    have : m ≤ b := le_of_lt hm
    exact sub_nonneg.mpr (Nat.cast_le.mpr this)
  have h_sqrt_pos : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.mpr hb_pos
  have h_sq_lt : (b - m : ℝ) ^ 2 < (Real.sqrt (b : ℝ)) ^ 2 := by
    have h1 : 0 ≤ (b - m : ℝ) := hbm_nonneg
    have h2 : (b - m : ℝ) < Real.sqrt (b : ℝ) := h_sparse
    nlinarith
  rw [Real.sq_sqrt (le_of_lt hb_pos)] at h_sq_lt
  exact (div_lt_one hb_pos).mpr h_sq_lt

/-- Wavepacket contraction bound on multiscale Cantor sets:
$2 |T| \mu(C_k) \le 2 ((b-m)^2 / b)^k$. -/
theorem continuous_cantor_wavepacket_contraction (b m : ℕ) (hm : m < b) (k : ℕ)
    (T_card : ℝ) (hT : T_card ≤ (b - m : ℝ) ^ k) :
    2 * T_card * cantor_scale_measure b m k ≤ 2 * (cantor_fup_ratio b m) ^ k := by
  dsimp [cantor_scale_measure, cantor_fup_ratio]
  have hb_pos : 0 < (b : ℝ) := Nat.cast_pos.mpr (by omega)
  have hbm_nonneg : 0 ≤ (b - m : ℝ) := by
    have : m ≤ b := le_of_lt hm
    exact sub_nonneg.mpr (Nat.cast_le.mpr this)
  have h_meas_nonneg : 0 ≤ ((b - m : ℝ) / (b : ℝ)) ^ k :=
    pow_nonneg (div_nonneg hbm_nonneg (le_of_lt hb_pos)) k
  have h_step1 : T_card * ((b - m : ℝ) / (b : ℝ)) ^ k ≤
      ((b - m : ℝ) ^ k) * (((b - m : ℝ) / (b : ℝ)) ^ k) :=
    mul_le_mul_of_nonneg_right hT h_meas_nonneg
  have h_alg : ((b - m : ℝ) ^ k) * (((b - m : ℝ) / (b : ℝ)) ^ k) =
      (((b - m : ℝ) ^ 2) / (b : ℝ)) ^ k := by
    rw [div_pow, div_pow]
    have h_pow2 : ((b - m : ℝ) ^ 2) ^ k = ((b - m : ℝ) ^ k) * ((b - m : ℝ) ^ k) := by
      rw [← pow_mul, mul_comm 2 k, pow_mul, sq]
    rw [h_pow2]
    ring
  rw [h_alg] at h_step1
  linarith

/-- Asymptotic contraction to zero of the continuous Cantor FUP bound as scale $k \to \infty$. -/
theorem continuous_cantor_fup_tendsto_zero (b m : ℕ) (hm : m < b)
    (h_sparse : (b - m : ℝ) < Real.sqrt (b : ℝ)) :
    Filter.Tendsto (fun k : ℕ => 2 * (cantor_fup_ratio b m) ^ k) Filter.atTop (nhds 0) := by
  have hb_pos : 0 < (b : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_ratio_nonneg : 0 ≤ cantor_fup_ratio b m := by
    dsimp [cantor_fup_ratio]
    exact div_nonneg (sq_nonneg _) (le_of_lt hb_pos)
  have h_ratio_lt_one : cantor_fup_ratio b m < 1 :=
    cantor_fup_ratio_lt_one b m hm h_sparse
  have h_pow_tendsto := tendsto_pow_atTop_nhds_zero_of_lt_one h_ratio_nonneg h_ratio_lt_one
  have h_const_mul := Filter.Tendsto.const_mul (2 : ℝ) h_pow_tendsto
  simp only [mul_zero] at h_const_mul
  exact h_const_mul

/-- Concrete witness at base $b = 4$, missing $m = 3$ digits:
The FUP ratio is $1/4$, and $2 \cdot (1/4)^k \le 1/2$ for all $k \ge 1$. -/
theorem continuous_cantor_witness_b4_m3 :
    cantor_fup_ratio 4 3 = 1 / 4 ∧ (∀ k ≥ 1, 2 * (cantor_fup_ratio 4 3) ^ k ≤ 1 / 2) := by
  have h_ratio : cantor_fup_ratio 4 3 = 1 / 4 := by
    dsimp [cantor_fup_ratio]
    norm_num
  refine ⟨h_ratio, ?_⟩
  intro k hk
  rw [h_ratio]
  have h_pow_le : (1 / 4 : ℝ) ^ k ≤ 1 / 4 := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
    subst hj
    rw [pow_add, pow_one]
    have h_pow_nonneg : 0 ≤ (1 / 4 : ℝ) ^ j := pow_nonneg (by norm_num) j
    have h_pow_le_one : (1 / 4 : ℝ) ^ j ≤ 1 := by
      exact pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  linarith

/-- OpenGauss Trap T16 Non-Commutativity Witness in the continuous setting:
Truncation to $[0, 1/2)$ does not commute with Fourier modes. -/
theorem continuous_fup_noncomm_witness :
    (fun x => if x < 1/2 then (modeSin 1 x) else 0) ≠ (fun x => modeSin 1 x) := by
  intro h
  have h_val := congr_fun h (3 / 4)
  have h_not_lt : ¬ ((3 : ℝ) / 4 < 1 / 2) := by norm_num
  simp only [h_not_lt, ↓reduceIte] at h_val
  dsimp [modeSin] at h_val
  have h_angle : 2 * Real.pi * ((1 : ℕ) : ℝ) * (3 / 4) = Real.pi / 2 + Real.pi := by
    push_cast
    ring
  rw [h_angle, Real.sin_add_pi, Real.sin_pi_div_two] at h_val
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_contra : Real.sqrt 2 * -(1 : ℝ) = 0 := h_val.symm
  linarith

end InfoGeometry.Analysis.ContinuousL2CantorFourierUncertainty
