/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.UnboundedHilbertResolventAndC0GroupWitness
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic

/-!
# An actual bounded transform on the original real ℓ² space

The symmetric odd unbounded block operator is `D = -Γ K_max` on the existing
maximal domain. Its explicit smoothing multiplier has coefficients
`1 / sqrt (1 + (m+1)^2)`, maps every Hilbert vector into that domain, and
`D (C x) = F x`. The resulting bounded operator is self-adjoint, odd,
invertible, Fredholm with native index zero, and has compact square defect.
Compactness is proved by norm convergence of finite-coordinate operators.

No algebra representation or Fredholm-module compact-commutator conclusion
is supplied by this operator construction.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealL2BoundedTransform

open UnboundedHilbertResolventAndC0GroupWitness Filter
open scoped Topology BigOperators

def pairSwap (n : ℕ) : ℕ := if n % 2 = 0 then n + 1 else n - 1

@[simp] theorem pairSwap_even (m : ℕ) : pairSwap (2 * m) = 2 * m + 1 := by
  simp [pairSwap]

@[simp] theorem pairSwap_odd (m : ℕ) : pairSwap (2 * m + 1) = 2 * m := by
  simp [pairSwap]

@[simp] theorem pairSwap_involutive (n : ℕ) : pairSwap (pairSwap n) = n := by
  by_cases h : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by omega
    rw [hn, pairSwap_even, pairSwap_odd]
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, pairSwap_odd, pairSwap_even]

def pairSwapEquiv : ℕ ≃ ℕ where
  toFun := pairSwap
  invFun := pairSwap
  left_inv := pairSwap_involutive
  right_inv := pairSwap_involutive

@[simp] theorem pairSwapEquiv_apply (n : ℕ) : pairSwapEquiv n = pairSwap n := rfl

def frequency (n : ℕ) : ℝ := (n / 2 : ℕ) + 1

theorem frequency_ge_one (n : ℕ) : 1 ≤ frequency n := by
  dsimp [frequency]
  exact le_add_of_nonneg_left (Nat.cast_nonneg (n / 2))

@[simp] theorem frequency_pairSwap (n : ℕ) : frequency (pairSwap n) = frequency n := by
  unfold frequency pairSwap
  split_ifs <;> congr 2 <;> omega

private def swapLinear : H_lp →ₗ[ℝ] H_lp where
  toFun x := ⟨fun n => x (pairSwap n), by
    apply (memℓp_two_iff _).mpr
    simpa only [Function.comp_def, pairSwapEquiv_apply] using
      (pairSwapEquiv.summable_iff (f := fun n : ℕ => (x n) ^ 2)).mpr
        (summable_sq_of_mem x)⟩
  map_add' x y := by ext n; rfl
  map_smul' c x := by ext n; rfl

private theorem swapLinear_norm (x : H_lp) : ‖swapLinear x‖ = ‖x‖ := by
  have hsq : ‖swapLinear x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
    exact pairSwapEquiv.tsum_eq (fun n => (x n) ^ 2)
  nlinarith [norm_nonneg (swapLinear x), norm_nonneg x]

def swap : H_lp →L[ℝ] H_lp :=
  swapLinear.mkContinuous 1 (fun x => by simpa [swapLinear_norm])

@[simp] theorem swap_apply (x : H_lp) (n : ℕ) : swap x n = x (pairSwap n) := rfl

/-- Native pointwise bounded multiplication on the existing `lp` carrier. -/
def diagonal (d : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) (hd : ∀ n, |d n| ≤ C) :
    H_lp →L[ℝ] H_lp :=
  lp.mapCLM 2 (fun n => d n • ContinuousLinearMap.id ℝ ℝ) hC
    (fun n => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs] using hd n)

@[simp] theorem diagonal_apply (d : ℕ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hd : ∀ n, |d n| ≤ C) (x : H_lp) (n : ℕ) :
    diagonal d hC hd x n = d n * x n := rfl

def paritySign (n : ℕ) : ℝ := if n % 2 = 0 then 1 else -1

@[simp] theorem abs_paritySign (n : ℕ) : |paritySign n| = 1 := by
  unfold paritySign
  split_ifs <;> norm_num

@[simp] theorem paritySign_pairSwap (n : ℕ) : paritySign (pairSwap n) = -paritySign n := by
  by_cases h : n % 2 = 0
  · have hnext : (n + 1) % 2 ≠ 0 := by omega
    simp [paritySign, pairSwap, h, hnext]
  · have hprev : (n - 1) % 2 = 0 := by omega
    simp [paritySign, pairSwap, h, hprev]

def grading : H_lp →L[ℝ] H_lp := diagonal paritySign zero_le_one (by simp)

@[simp] theorem grading_apply (x : H_lp) (n : ℕ) : grading x n = paritySign n * x n := rfl

@[simp] theorem grading_grading (x : H_lp) : grading (grading x) = x := by
  ext n
  simp only [grading_apply]
  unfold paritySign
  split_ifs <;> ring

theorem grading_norm (x : H_lp) : ‖grading x‖ = ‖x‖ := by
  have h (y : H_lp) : ‖grading y‖ ≤ ‖y‖ :=
    lp.norm_mono (by norm_num) (fun n => by simp [Real.norm_eq_abs])
  exact le_antisymm (h x) (by simpa using h (grading x))

def alpha (n : ℕ) : ℝ := frequency n / Real.sqrt (1 + frequency n ^ 2)
def beta (n : ℕ) : ℝ := Real.sqrt (1 + frequency n ^ 2) / frequency n
def smoothingCoefficient (n : ℕ) : ℝ := 1 / Real.sqrt (1 + frequency n ^ 2)

private theorem sqrt_den_pos (n : ℕ) : 0 < Real.sqrt (1 + frequency n ^ 2) := by positivity

theorem alpha_pos (n : ℕ) : 0 < alpha n :=
  div_pos (lt_of_lt_of_le zero_lt_one (frequency_ge_one n)) (sqrt_den_pos n)

theorem alpha_le_one (n : ℕ) : alpha n ≤ 1 := by
  rw [alpha, div_le_one (sqrt_den_pos n)]
  nlinarith [Real.sq_sqrt (show 0 ≤ 1 + frequency n ^ 2 by positivity),
    Real.sqrt_nonneg (1 + frequency n ^ 2), sq_nonneg (frequency n)]

theorem alpha_sq (n : ℕ) : alpha n ^ 2 = frequency n ^ 2 / (1 + frequency n ^ 2) := by
  rw [alpha, div_pow, Real.sq_sqrt (show 0 ≤ 1 + frequency n ^ 2 by positivity)]

theorem alpha_sq_ge_half (n : ℕ) : (1 : ℝ) / 2 ≤ alpha n ^ 2 := by
  have ha : 1 ≤ frequency n ^ 2 := by
    nlinarith [frequency_ge_one n, sq_nonneg (frequency n - 1)]
  rw [alpha_sq, le_div_iff₀ (show 0 < 1 + frequency n ^ 2 by positivity)]
  linarith

/-- A uniform spectral gap for the actual bounded-transform coefficients. -/
theorem alpha_ge_one_div_sqrt_two (n : ℕ) : 1 / Real.sqrt 2 ≤ alpha n := by
  rw [div_le_iff₀ (show 0 < Real.sqrt 2 by positivity)]
  have hmul := mul_le_mul_of_nonneg_right (alpha_sq_ge_half n) (by norm_num : (0 : ℝ) ≤ 2)
  have heq : (alpha n * Real.sqrt 2) ^ 2 = alpha n ^ 2 * 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hnonneg : 0 ≤ alpha n * Real.sqrt 2 :=
    mul_nonneg (alpha_pos n).le (Real.sqrt_nonneg _)
  nlinarith

theorem beta_bound (n : ℕ) : |beta n| ≤ 2 := by
  have ha : 0 < frequency n := lt_of_lt_of_le zero_lt_one (frequency_ge_one n)
  rw [beta, abs_of_pos (div_pos (sqrt_den_pos n) ha), div_le_iff₀ ha]
  nlinarith [frequency_ge_one n, Real.sq_sqrt (show 0 ≤ 1 + frequency n ^ 2 by positivity),
    Real.sqrt_nonneg (1 + frequency n ^ 2)]

theorem smoothingCoefficient_bound (n : ℕ) : |smoothingCoefficient n| ≤ 1 := by
  rw [smoothingCoefficient, abs_of_pos (div_pos zero_lt_one (sqrt_den_pos n)),
    div_le_one (sqrt_den_pos n)]
  nlinarith [Real.sq_sqrt (show 0 ≤ 1 + frequency n ^ 2 by positivity),
    Real.sqrt_nonneg (1 + frequency n ^ 2), sq_nonneg (frequency n)]

@[simp] theorem alpha_pairSwap (n : ℕ) : alpha (pairSwap n) = alpha n := by
  simp [alpha]

@[simp] theorem beta_pairSwap (n : ℕ) : beta (pairSwap n) = beta n := by
  simp [beta]

@[simp] theorem alpha_mul_beta (n : ℕ) : alpha n * beta n = 1 := by
  have ha : frequency n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (frequency_ge_one n))
  have hs := ne_of_gt (sqrt_den_pos n)
  dsimp [alpha, beta]
  field_simp

def boundedTransform : H_lp →L[ℝ] H_lp :=
  (diagonal alpha zero_le_one (fun n => by rw [abs_of_pos (alpha_pos n)]; exact alpha_le_one n)).comp swap

def boundedTransformInverse : H_lp →L[ℝ] H_lp :=
  (diagonal beta (by norm_num : (0 : ℝ) ≤ 2) beta_bound).comp swap

def smoothing : H_lp →L[ℝ] H_lp :=
  diagonal smoothingCoefficient zero_le_one smoothingCoefficient_bound

@[simp] theorem boundedTransform_apply (x : H_lp) (n : ℕ) :
    boundedTransform x n = alpha n * x (pairSwap n) := rfl

@[simp] theorem boundedTransformInverse_apply (x : H_lp) (n : ℕ) :
    boundedTransformInverse x n = beta n * x (pairSwap n) := rfl

@[simp] theorem smoothing_apply (x : H_lp) (n : ℕ) :
    smoothing x n = smoothingCoefficient n * x n := rfl

theorem boundedTransform_isSelfAdjoint : IsSelfAdjoint boundedTransform := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  calc
    _ = ∑' n, inner ℝ (boundedTransform x (pairSwap n)) (y (pairSwap n)) :=
      (pairSwapEquiv.tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro n
      change inner ℝ (alpha (pairSwap n) * x (pairSwap (pairSwap n)))
          (y (pairSwap n)) = inner ℝ (x n) (alpha n * y (pairSwap n))
      rw [alpha_pairSwap, pairSwap_involutive]
      simp only [Real.inner_apply]
      ring

theorem boundedTransform_odd :
    grading.comp boundedTransform = -(boundedTransform.comp grading) := by
  ext x n
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    lp.coeFn_neg, Pi.neg_apply, grading_apply, boundedTransform_apply, paritySign_pairSwap]
  ring

theorem boundedTransform_inverse_right :
    boundedTransform.comp boundedTransformInverse = ContinuousLinearMap.id ℝ H_lp := by
  ext x n
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    boundedTransform_apply, boundedTransformInverse_apply, beta_pairSwap,
    pairSwap_involutive, ← mul_assoc, alpha_mul_beta, one_mul]

theorem boundedTransform_inverse_left :
    boundedTransformInverse.comp boundedTransform = ContinuousLinearMap.id ℝ H_lp := by
  ext x n
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    boundedTransform_apply, boundedTransformInverse_apply, alpha_pairSwap, pairSwap_involutive]
  rw [← mul_assoc, mul_comm (beta n), alpha_mul_beta, one_mul]

theorem boundedTransform_isInvertible : boundedTransform.IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse boundedTransform_inverse_right boundedTransform_inverse_left

theorem boundedTransform_isFredholm : boundedTransform.IsFredholm :=
  boundedTransform_isInvertible.isFredholm

theorem boundedTransform_index : boundedTransform.toLinearMap.index = 0 :=
  LinearMap.index_of_bijective boundedTransform_isInvertible.bijective

/-- The actual symmetric unbounded block operator on the existing maximal domain. -/
def dirac : D_max →ₗ[ℝ] H_lp := -(grading.toLinearMap.comp K_max)

@[simp] theorem dirac_apply (x : D_max) (n : ℕ) :
    dirac x n = frequency n * x.1 (pairSwap n) := by
  change (-grading (K_max x)) n = _
  simp only [lp.coeFn_neg, Pi.neg_apply, grading_apply, K_max_apply_coe]
  unfold K_unb_fun frequency pairSwap paritySign
  split_ifs <;> ring

theorem dirac_is_unbounded :
    ¬ ∃ C : ℝ, ∀ x : D_max, ‖dirac x‖ ≤ C * ‖(x : H_lp)‖ := by
  rintro ⟨C, hC⟩
  apply K_max_is_unbounded
  refine ⟨C, fun x => ?_⟩
  have hx := hC x
  change ‖-(grading (K_max x))‖ ≤ C * ‖(x : H_lp)‖ at hx
  rw [norm_neg, grading_norm] at hx
  exact hx

theorem dirac_symmetric (x y : D_max) :
    inner ℝ (dirac x) (y : H_lp) = inner ℝ (x : H_lp) (dirac y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  calc
    _ = ∑' n, inner ℝ (dirac x (pairSwap n)) (y.1 (pairSwap n)) :=
      (pairSwapEquiv.tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro n
      rw [dirac_apply, dirac_apply, frequency_pairSwap, pairSwap_involutive]
      simp only [Real.inner_apply]
      ring

theorem grading_mem_D_max (x : D_max) : grading x.1 ∈ D_max := by
  change Memℓp (K_unb_fun (grading x.1 : ℕ → ℝ)) 2
  have heq : K_unb_fun (grading x.1 : ℕ → ℝ) =
      ((-grading (K_max x) : H_lp) : ℕ → ℝ) := by
    funext n
    simp only [lp.coeFn_neg, Pi.neg_apply, grading_apply, K_max_apply_coe]
    unfold K_unb_fun
    simp only [grading_apply]
    by_cases h : n % 2 = 0
    · have hh : (n + 1) % 2 ≠ 0 := by omega
      simp [h, hh, paritySign]
    · have hh : (n - 1) % 2 = 0 := by omega
      simp [h, hh, paritySign]
  rw [heq]
  exact (-grading (K_max x)).property

/-- Oddness holds on the genuine maximal domain, including domain preservation. -/
theorem dirac_odd (x : D_max) :
    dirac ⟨grading x.1, grading_mem_D_max x⟩ = -grading (dirac x) := by
  ext n
  simp only [dirac_apply, grading_apply, lp.coeFn_neg, Pi.neg_apply, paritySign_pairSwap]
  ring

theorem smoothing_mem_D_max (x : H_lp) : smoothing x ∈ D_max := by
  change Memℓp (K_unb_fun (smoothing x : ℕ → ℝ)) 2
  have heq : K_unb_fun (smoothing x : ℕ → ℝ) =
      ((-grading (boundedTransform x) : H_lp) : ℕ → ℝ) := by
    funext n
    simp only [lp.coeFn_neg, Pi.neg_apply, grading_apply, boundedTransform_apply]
    unfold K_unb_fun
    simp only [smoothing_apply, smoothingCoefficient]
    by_cases h : n % 2 = 0
    · have hs : (n + 1) / 2 = n / 2 := by omega
      simp [h, paritySign, pairSwap, frequency, hs, alpha]
      ring
    · have hs : (n - 1) / 2 = n / 2 := by omega
      simp [h, paritySign, pairSwap, frequency, hs, alpha]
      ring
  rw [heq]
  exact (-grading (boundedTransform x)).property

/-- The bounded transform is obtained by applying the actual unbounded
operator to its explicit inverse-square-root smoothing map. -/
theorem dirac_smoothing (x : H_lp) :
    dirac ⟨smoothing x, smoothing_mem_D_max x⟩ = boundedTransform x := by
  ext n
  simp only [dirac_apply, smoothing_apply, boundedTransform_apply]
  simp [smoothingCoefficient, frequency_pairSwap, alpha]
  ring

/-- Finite-coordinate approximation, as an actual finite sum of rank-one operators. -/
def diagonalTruncation (d : ℕ → ℝ) (N : ℕ) : H_lp →L[ℝ] H_lp :=
  ∑ n ∈ Finset.range N, d n •
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 n).comp
      (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n)

@[simp] theorem diagonalTruncation_apply (d : ℕ → ℝ) (N : ℕ) (x : H_lp) (n : ℕ) :
    diagonalTruncation d N x n = if n < N then d n * x n else 0 := by
  simp only [diagonalTruncation, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]
  change (∑ i ∈ Finset.range N, d i • (lp.single 2 i (x i) : H_lp)) n = _
  rw [lp.coeFn_sum]
  simp [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    lp.single_apply, Pi.single_apply]

theorem diagonalTruncation_compact (d : ℕ → ℝ) (N : ℕ) :
    IsCompactOperator (diagonalTruncation d N) := by
  change diagonalTruncation d N ∈ compactOperator (RingHom.id ℝ) H_lp H_lp
  apply Submodule.sum_mem
  intro n hn
  exact ((isCompactOperator_of_locallyCompactSpace_rng
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 n)).comp_clm
      (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n)).smul (d n)

theorem diagonalTruncation_error (d : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ n, |d n| ≤ C) (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (htail : ∀ n, N ≤ n → |d n| ≤ ε) :
    ‖diagonalTruncation d N - diagonal d hC hd‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro x
  have h : ‖(diagonalTruncation d N - diagonal d hC hd) x‖ ≤ ‖ε • x‖ := by
    apply lp.norm_mono (by norm_num)
    intro n
    simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply,
      diagonalTruncation_apply, diagonal_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hn : n < N
    · simp only [if_pos hn, sub_self, norm_zero]
      exact norm_nonneg _
    · rw [if_neg hn, zero_sub, norm_neg, norm_mul, norm_mul, Real.norm_eq_abs ε,
        abs_of_nonneg hε]
      exact mul_le_mul_of_nonneg_right (htail n (by omega)) (norm_nonneg _)
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε] using h

theorem diagonal_compact_of_tendsto_zero (d : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ n, |d n| ≤ C) (hlim : Tendsto d atTop (𝓝 0)) :
    IsCompactOperator (diagonal d hC hd) := by
  apply isCompactOperator_of_tendsto (l := (atTop : Filter ℕ)) (F := diagonalTruncation d)
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) (ε / 2) (by linarith)
    refine ⟨N, fun k hk => ?_⟩
    rw [dist_eq_norm]
    apply lt_of_le_of_lt
      (diagonalTruncation_error d hC hd k (ε := ε / 2) (by positivity) ?_) (by linarith)
    intro n hn
    have h := hN n (le_trans hk hn)
    simpa only [Real.dist_eq, sub_zero] using h.le
  · exact Eventually.of_forall (diagonalTruncation_compact d)

def defectCoefficient (n : ℕ) : ℝ := -(1 / (1 + frequency n ^ 2))

theorem defectCoefficient_bound (n : ℕ) : |defectCoefficient n| ≤ 1 := by
  rw [defectCoefficient, abs_neg, abs_of_pos (by positivity), div_le_one (by positivity)]
  exact le_add_of_nonneg_right (sq_nonneg (frequency n))

theorem defectCoefficient_tendsto : Tendsto defectCoefficient atTop (𝓝 0) := by
  have hf : Tendsto frequency atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge b
    refine eventually_atTop.mpr ⟨2 * N, fun n hn => ?_⟩
    have hdiv : N ≤ n / 2 := by omega
    have hcast : (N : ℝ) ≤ (n / 2 : ℕ) := by exact_mod_cast hdiv
    dsimp [frequency]
    linarith
  have hd : Tendsto (fun n => 1 + frequency n ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun n => by nlinarith [frequency_ge_one n]) hf
  change Tendsto (fun n => -(1 / (1 + frequency n ^ 2))) atTop (𝓝 0)
  simpa only [one_div, Function.comp_def, neg_zero] using (tendsto_inv_atTop_zero.comp hd).neg

theorem boundedTransform_square_defect :
    boundedTransform.comp boundedTransform - ContinuousLinearMap.id ℝ H_lp =
      diagonal defectCoefficient zero_le_one defectCoefficient_bound := by
  ext x n
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, lp.coeFn_sub, Pi.sub_apply, boundedTransform_apply,
    alpha_pairSwap, pairSwap_involutive, diagonal_apply]
  have hd : 1 + frequency n ^ 2 ≠ 0 := by positivity
  have hcoeff : alpha n ^ 2 - 1 = defectCoefficient n := by
    rw [alpha_sq]
    dsimp [defectCoefficient]
    field_simp
    ring
  calc
    alpha n * (alpha n * x n) - x n = (alpha n ^ 2 - 1) * x n := by ring
    _ = defectCoefficient n * x n := by rw [hcoeff]

theorem boundedTransform_square_defect_compact : IsCompactOperator
    (boundedTransform.comp boundedTransform - ContinuousLinearMap.id ℝ H_lp) := by
  rw [boundedTransform_square_defect]
  exact diagonal_compact_of_tendsto_zero defectCoefficient zero_le_one
    defectCoefficient_bound defectCoefficient_tendsto

end InfoGeometry.OperatorAlgebra.RealL2BoundedTransform
