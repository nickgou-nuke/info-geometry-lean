/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real

noncomputable section

namespace InfoGeometry.Physics.FisherRaoAitchisonKan

/-!
# Binary Probability Metric Formulas

This file proves elementary identities for explicitly defined scalar functions on
real probabilities. In particular, it verifies their values and bounds on the
binary simplex, along with elementary Bhattacharyya and Wootters identities.
The names `timeDelay` and `casimirEigenvalue` are definitions of reciprocal
quadratic functions; their numerical relation to `fisherRaoMetric` does not
establish a scattering model, a Casimir representation, or an Iwasawa/KAN
decomposition. The file contains no such geometric structures.
-/

/-- Fisher-Rao metric on the open binary simplex (0, 1). -/
def fisherRaoMetric (p : ℝ) : ℝ :=
  1 / (p * (1 - p))

/-- Aitchison metric on the open binary simplex (0, 1). -/
def aitchisonMetric (p : ℝ) : ℝ :=
  1 / (2 * p ^ 2 * (1 - p) ^ 2)

/-- Dikin log-barrier Hessian on the open binary simplex (0, 1). -/
def dikinHessian (p : ℝ) : ℝ :=
  1 / p ^ 2 + 1 / (1 - p) ^ 2

/-- Reciprocal quadratic scalar function used in the stated numerical identity. -/
def timeDelay (t : ℝ) : ℝ :=
  1 / (1 / 4 + t ^ 2)

/-- Quadratic scalar function reciprocal to `timeDelay`. -/
def casimirEigenvalue (t : ℝ) : ℝ :=
  1 / 4 + t ^ 2

/-- Bhattacharyya fidelity on the binary simplex. -/
def bhattacharyyaFidelity (p q : ℝ) : ℝ :=
  Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q))

/-- Wootters quantum pure-state angle on the compact sphere. -/
def woottersDistance (p q : ℝ) : ℝ :=
  Real.arccos (bhattacharyyaFidelity p q)

/-! ## 1. Fisher-Rao Metric Properties -/

/-- 🏆 THEOREM 1: Positivity of the Fisher-Rao metric everywhere on the open simplex. -/
theorem fisherRao_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < fisherRaoMetric p := by
  unfold fisherRaoMetric
  have h1 : 0 < 1 - p := by linarith
  have h2 : 0 < p * (1 - p) := mul_pos hp0 h1
  exact one_div_pos.mpr h2

/-- 🏆 THEOREM 2: Value at the Jaynesian maximum entropy prior p = 1/2. -/
theorem fisherRao_half : fisherRaoMetric (1 / 2) = 4 := by
  unfold fisherRaoMetric
  norm_num

/-- 🏆 THEOREM 3: Weyl reflection symmetry p ↦ 1 - p of the Fisher-Rao metric. -/
theorem fisherRao_symm (p : ℝ) :
    fisherRaoMetric (1 - p) = fisherRaoMetric p := by
  unfold fisherRaoMetric
  have h : (1 - p) * (1 - (1 - p)) = p * (1 - p) := by ring
  rw [h]

/-- 🏆 THEOREM 4: Global minimality of the Fisher-Rao metric at the Jaynesian prior:
    For all  \in (0, 1)$, {\mathrm{FR}}(p) \ge 4$. -/
theorem fisherRao_ge_four {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    4 ≤ fisherRaoMetric p := by
  unfold fisherRaoMetric
  have h1 : 0 < 1 - p := by linarith
  have hprod_pos : 0 < p * (1 - p) := mul_pos hp0 h1
  have h_quad : p * (1 - p) ≤ 1 / 4 := by
    have h_sq : 0 ≤ (p - 1 / 2) ^ 2 := sq_nonneg (p - 1 / 2)
    have : (p - 1 / 2) ^ 2 = p ^ 2 - p + 1 / 4 := by ring
    linarith
  have h_four : (4 : ℝ) = 1 / (1 / 4) := by norm_num
  rw [h_four]
  exact one_div_le_one_div_of_le hprod_pos h_quad

/-! ## 2. Aitchison Metric Properties -/

/-- 🏆 THEOREM 5: Positivity of the Aitchison metric everywhere on the open simplex. -/
theorem aitchison_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < aitchisonMetric p := by
  unfold aitchisonMetric
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have h1p_ne : 1 - p ≠ 0 := by linarith
  have hp2_pos : 0 < p ^ 2 := sq_pos_of_ne_zero hp_ne
  have h1p2_pos : 0 < (1 - p) ^ 2 := sq_pos_of_ne_zero h1p_ne
  have h_denom : 0 < 2 * p ^ 2 * (1 - p) ^ 2 := by
    positivity
  exact one_div_pos.mpr h_denom

/-- 🏆 THEOREM 6: Value of the Aitchison metric at the Jaynesian prior p = 1/2. -/
theorem aitchison_half : aitchisonMetric (1 / 2) = 8 := by
  unfold aitchisonMetric
  norm_num

/-- 🏆 THEOREM 7: Weyl reflection symmetry p ↦ 1 - p of the Aitchison metric. -/
theorem aitchison_symm (p : ℝ) :
    aitchisonMetric (1 - p) = aitchisonMetric p := by
  unfold aitchisonMetric
  have h : (1 - p) ^ 2 * (1 - (1 - p)) ^ 2 = p ^ 2 * (1 - p) ^ 2 := by ring
  rw [mul_assoc 2, h, ← mul_assoc]

/-- 🏆 THEOREM 8: Global minimality of the Aitchison metric at the Jaynesian prior:
    For all  \in (0, 1)$, (p) \ge 8$. -/
theorem aitchison_ge_eight {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    8 ≤ aitchisonMetric p := by
  unfold aitchisonMetric
  have h1 : 0 < 1 - p := by linarith
  have hprod_pos : 0 < p * (1 - p) := mul_pos hp0 h1
  have h_quad : p * (1 - p) ≤ 1 / 4 := by
    have h_sq : 0 ≤ (p - 1 / 2) ^ 2 := sq_nonneg (p - 1 / 2)
    have : (p - 1 / 2) ^ 2 = p ^ 2 - p + 1 / 4 := by ring
    linarith
  have h_sq_le : (p * (1 - p)) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    nlinarith [hprod_pos, h_quad]
  have h_denom_le : 2 * p ^ 2 * (1 - p) ^ 2 ≤ 1 / 8 := by
    have : 2 * p ^ 2 * (1 - p) ^ 2 = 2 * (p * (1 - p)) ^ 2 := by ring
    rw [this]
    linarith
  have h_denom_pos : 0 < 2 * p ^ 2 * (1 - p) ^ 2 := by
    have hp_ne : p ≠ 0 := ne_of_gt hp0
    have h1p_ne : 1 - p ≠ 0 := by linarith
    have hp2_pos : 0 < p ^ 2 := sq_pos_of_ne_zero hp_ne
    have h1p2_pos : 0 < (1 - p) ^ 2 := sq_pos_of_ne_zero h1p_ne
    positivity
  have h_eight : (8 : ℝ) = 1 / (1 / 8) := by norm_num
  rw [h_eight]
  exact one_div_le_one_div_of_le h_denom_pos h_denom_le

/-! ## 3. Dikin Barrier Hessian & Triad Decomposition -/

/-- 🏆 THEOREM 9: Weyl reflection symmetry p ↦ 1 - p of the Dikin Hessian. -/
theorem dikin_symm (p : ℝ) :
    dikinHessian (1 - p) = dikinHessian p := by
  unfold dikinHessian
  have h : 1 - (1 - p) = p := by ring
  rw [h, add_comm]

/-- 🏆 THEOREM 10: The Triad Metric Identity:
    1875036b''(p) = 2 g_A(p) - 2 g_{\mathrm{FR}}(p)1875036 -/
theorem triad_metric_decomposition (p : ℝ) (hp0 : p ≠ 0) (hp1 : 1 - p ≠ 0) :
    dikinHessian p = 2 * aitchisonMetric p - 2 * fisherRaoMetric p := by
  unfold dikinHessian aitchisonMetric fisherRaoMetric
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp0
  have h1p2 : (1 - p) ^ 2 ≠ 0 := pow_ne_zero 2 hp1
  field_simp [hp0, hp1, hp2, h1p2]
  ring

/-- 🏆 THEOREM 11: Value of the Dikin barrier Hessian at the Jaynesian prior. -/
theorem dikin_half : dikinHessian (1 / 2) = 8 := by
  unfold dikinHessian
  norm_num

/-! ## 4. Values of the explicitly defined reciprocal quadratic functions -/

/-- At the midpoint, `fisherRaoMetric` equals `timeDelay` at zero. -/
theorem fisherRao_half_eq_timeDelay_zero :
    fisherRaoMetric (1 / 2) = timeDelay 0 := by
  unfold timeDelay
  rw [fisherRao_half]
  norm_num

/-- At the midpoint, `aitchisonMetric` is twice `timeDelay` at zero. -/
theorem aitchison_half_eq_two_timeDelay_zero :
    aitchisonMetric (1 / 2) = 2 * timeDelay 0 := by
  unfold timeDelay
  rw [aitchison_half]
  norm_num

/-- The midpoint Fisher-Rao value times `casimirEigenvalue` at zero is one. -/
theorem fisherRao_half_mul_casimir_zero :
    fisherRaoMetric (1 / 2) * casimirEigenvalue 0 = 1 := by
  rw [fisherRao_half]
  unfold casimirEigenvalue
  norm_num

/-- The midpoint Aitchison value times `casimirEigenvalue` at zero is two. -/
theorem aitchison_half_mul_casimir_zero :
    aitchisonMetric (1 / 2) * casimirEigenvalue 0 = 2 := by
  rw [aitchison_half]
  unfold casimirEigenvalue
  norm_num

/-! ## 5. Quantum Fidelity & Wootters Pure-State Distance -/

/-- 🏆 THEOREM 16: Bhattacharyya self-fidelity is normalized to 1. -/
theorem bhattacharyya_self {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bhattacharyyaFidelity p p = 1 := by
  unfold bhattacharyyaFidelity
  have h1 : 0 ≤ 1 - p := by linarith
  have hpp : p * p = p ^ 2 := by ring
  have h1p1p : (1 - p) * (1 - p) = (1 - p) ^ 2 := by ring
  rw [hpp, h1p1p, Real.sqrt_sq hp0, Real.sqrt_sq h1]
  ring

/-- 🏆 THEOREM 17: Symmetry of Bhattacharyya fidelity. -/
theorem bhattacharyya_symm (p q : ℝ) :
    bhattacharyyaFidelity p q = bhattacharyyaFidelity q p := by
  unfold bhattacharyyaFidelity
  rw [mul_comm p q, mul_comm (1 - p) (1 - q)]

/-- 🏆 THEOREM 18: Fidelity at the Jaynesian prior state. -/
theorem bhattacharyya_half_half :
    bhattacharyyaFidelity (1 / 2) (1 / 2) = 1 := by
  exact bhattacharyya_self (by norm_num) (by norm_num)

/-- 🏆 THEOREM 19: Strict positivity of Bhattacharyya fidelity for interior states. -/
theorem bhattacharyya_pos {p q : ℝ} (hp0 : 0 < p) (hq0 : 0 < q) (hp1 : p < 1) (hq1 : q < 1) :
    0 < bhattacharyyaFidelity p q := by
  unfold bhattacharyyaFidelity
  have h1 : 0 < Real.sqrt (p * q) := Real.sqrt_pos.mpr (mul_pos hp0 hq0)
  have h2 : 0 < Real.sqrt ((1 - p) * (1 - q)) :=
    Real.sqrt_pos.mpr (mul_pos (by linarith) (by linarith))
  exact add_pos h1 h2

/-- 🏆 THEOREM 20: Vanishing of the Wootters pure-state distance between identical states. -/
theorem wootters_self {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    woottersDistance p p = 0 := by
  unfold woottersDistance
  rw [bhattacharyya_self hp0 hp1, Real.arccos_one]

/-- 🏆 THEOREM 21: Vanishing of the Wootters distance at the Jaynesian ground state. -/
theorem wootters_half_half :
    woottersDistance (1 / 2) (1 / 2) = 0 := by
  unfold woottersDistance
  rw [bhattacharyya_half_half, Real.arccos_one]


end InfoGeometry.Physics.FisherRaoAitchisonKan
