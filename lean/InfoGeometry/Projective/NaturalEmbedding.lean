/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

namespace InfoGeometry.Projective.NaturalEmbedding

open Real Complex Filter Topology

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

/-!
# Embedding of Natural Numbers in ℂP¹ and Asymptotic Approach to the Boundary

This module formalizes the embedding of natural numbers $n \ge 1$ into the Apollonian
geometry and proves their asymptotic behavior as $n \to \infty$:

1. **Rational Inhomogeneous Embedding**:
   $$w(n) = \frac{2n - 3}{2n + 1} = 1 - \frac{4}{2n + 1}$$

2. **Homogeneous Projective Point on $\mathbb{CP}^1$**:
   $$[Z_0(n) : Z_1(n)] = [2n - 3 : 2n + 1]$$

3. **Natural Logarithmic Scale Position**:
   $$\xi(n) = \ln(w(n)) = \ln\left(1 - \frac{4}{2n + 1}\right) < 0 \quad (\text{for } n \ge 2)$$

4. **Asymptotic Convergence to the Critical Leaf Boundary**:
   - $\lim_{n \to \infty} w(n) = 1$
   - $\lim_{n \to \infty} \xi(n) = 0$
   - $\lim_{n \to \infty} Q(n) = 0$ (where $Q = \tanh(\xi)$ is the Fubini-Study signature quotient)
-/

/-- Rational Apollonian embedding of a real/natural parameter n:
    w(n) = (2n - 3) / (2n + 1). -/
def apollonianIntEmbedding (n : ℝ) : ℝ :=
  (2 * n - 3) / (2 * n + 1)

/-- The logarithmic scale position coordinate ξ(n) = ln(w(n)) on the cylinder. -/
def intNaturalScale (n : ℝ) : ℝ :=
  Real.log (apollonianIntEmbedding n)

/-- The Fubini-Study / Cayley signature quotient: Q(n) = (w(n)² - 1) / (w(n)² + 1). -/
def intSignatureQuotient (n : ℝ) : ℝ :=
  ((apollonianIntEmbedding n) ^ 2 - 1) / ((apollonianIntEmbedding n) ^ 2 + 1)

/-!
### 1. Algebraic Identities & Bounds for n ≥ 2
-/

/-- 🏆 THEOREM 1 (Fractional Defect Form):
    w(n) = 1 - 4 / (2n + 1). -/
theorem apollonianIntEmbedding_eq_one_sub (n : ℝ) (hn : 2 * n + 1 ≠ 0) :
    apollonianIntEmbedding n = 1 - 4 / (2 * n + 1) := by
  unfold apollonianIntEmbedding
  have : 1 - 4 / (2 * n + 1) = ((2 * n + 1) - 4) / (2 * n + 1) := by
    field_simp
  rw [this]
  ring_nf

/-- 🏆 THEOREM 2 (Strict Positivity and Upper Bound for n ≥ 2):
    For any n ≥ 2, we have 0 < w(n) < 1. -/
theorem apollonianIntEmbedding_bounds (n : ℝ) (hn : 2 ≤ n) :
    0 < apollonianIntEmbedding n ∧ apollonianIntEmbedding n < 1 := by
  have h_den_pos : 0 < 2 * n + 1 := by linarith
  have h_num_pos : 0 < 2 * n - 3 := by linarith
  unfold apollonianIntEmbedding
  constructor
  · exact div_pos h_num_pos h_den_pos
  · rw [div_lt_one h_den_pos]
    linarith

/-- 🏆 THEOREM 3 (Negative Scale Coordinate in the Exterior Basin):
    For any n ≥ 2, the scale coordinate satisfies ξ(n) < 0. -/
theorem intNaturalScale_neg (n : ℝ) (hn : 2 ≤ n) :
    intNaturalScale n < 0 := by
  unfold intNaturalScale
  have ⟨h_pos, h_lt_one⟩ := apollonianIntEmbedding_bounds n hn
  exact Real.log_neg h_pos h_lt_one

lemma div_div_div_cancel_eq {G₀ : Type*} [GroupWithZero G₀] (a b c : G₀) (hc : c ≠ 0) :
    (a / c) / (b / c) = a / b := by
  rw [div_div_eq_mul_div, div_mul_cancel₀ a hc]

/-- 🏆 THEOREM 4 (Signature Quotient as Rational Function):
    Q(n) = (-4n + 2) / (2n² - 2n + 5/2) = (4 - 8n) / (4n² - 4n + 5). -/
theorem intSignatureQuotient_eq (n : ℝ) (hn : 2 * n + 1 ≠ 0) :
    intSignatureQuotient n = (4 - 8 * n) / (4 * n ^ 2 - 4 * n + 5) := by
  unfold intSignatureQuotient apollonianIntEmbedding
  have h_num : ((2 * n - 3) / (2 * n + 1)) ^ 2 - 1 = ((2 * n - 3) ^ 2 - (2 * n + 1) ^ 2) / (2 * n + 1) ^ 2 := by
    field_simp
  have h_den : ((2 * n - 3) / (2 * n + 1)) ^ 2 + 1 = ((2 * n - 3) ^ 2 + (2 * n + 1) ^ 2) / (2 * n + 1) ^ 2 := by
    field_simp
  rw [h_num, h_den]
  have h_sq_ne : (2 * n + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hn
  rw [div_div_div_cancel_eq _ _ _ h_sq_ne]
  have h1 : (2 * n - 3) ^ 2 - (2 * n + 1) ^ 2 = 2 * (4 - 8 * n) := by ring
  have h2 : (2 * n - 3) ^ 2 + (2 * n + 1) ^ 2 = 2 * (4 * n ^ 2 - 4 * n + 5) := by ring
  rw [h1, h2, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-!
### 2. Asymptotic Convergence to the Boundary
-/

/-- 🏆 THEOREM 5 (Asymptotic Boundary Convergence of Embedding w(n) → 1):
    lim_{n → ∞} (1 - 4/(2n + 1)) = 1. -/
theorem tendsto_apollonianIntEmbedding_atTop :
    Tendsto apollonianIntEmbedding atTop (𝓝 1) := by
  have h_eq : (fun n : ℝ => apollonianIntEmbedding n) =ᶠ[atTop] (fun n : ℝ => 1 - 4 / (2 * n + 1)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h_ne : 2 * n + 1 ≠ 0 := by linarith
    exact apollonianIntEmbedding_eq_one_sub n h_ne
  rw [tendsto_congr' h_eq]
  have h_lin : Tendsto (fun n : ℝ => 2 * n + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1 (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have h_inv : Tendsto (fun n : ℝ => (2 * n + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h_lin
  have h_mul : Tendsto (fun n : ℝ => 4 * (2 * n + 1)⁻¹) atTop (𝓝 (4 * 0)) :=
    tendsto_const_nhds.mul h_inv
  rw [mul_zero] at h_mul
  have h_sub : Tendsto (fun n : ℝ => 1 - 4 * (2 * n + 1)⁻¹) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h_mul
  simp only [div_eq_mul_inv]
  simpa only [sub_zero] using h_sub

/-- 🏆 THEOREM 6 (Asymptotic Scale Convergence ξ(n) → 0):
    lim_{n → ∞} ln(w(n)) = 0. -/
theorem tendsto_intNaturalScale_atTop :
    Tendsto intNaturalScale atTop (𝓝 0) := by
  unfold intNaturalScale
  have h_cont : ContinuousAt Real.log 1 := Real.continuousAt_log (by norm_num)
  have h_comp := h_cont.tendsto.comp tendsto_apollonianIntEmbedding_atTop
  simpa only [Real.log_one] using h_comp

/-- 🏆 THEOREM 7 (Asymptotic Signature Equilibrium Q(n) → 0):
    lim_{n → ∞} Q(n) = 0. -/
theorem tendsto_intSignatureQuotient_atTop :
    Tendsto intSignatureQuotient atTop (𝓝 0) := by
  have h_cont : ContinuousAt (fun w : ℝ => (w ^ 2 - 1) / (w ^ 2 + 1)) 1 := by
    apply ContinuousAt.div
    · exact (continuousAt_id.pow 2).sub continuousAt_const
    · exact (continuousAt_id.pow 2).add continuousAt_const
    · norm_num
  have h_comp := h_cont.tendsto.comp tendsto_apollonianIntEmbedding_atTop
  unfold intSignatureQuotient
  have h_val : (1 ^ 2 - 1) / (1 ^ 2 + (1 : ℝ)) = 0 := by norm_num
  rwa [h_val] at h_comp

/-!
### 3. Grand Capstone: Natural Number Embedding Synthesis
-/

/-- 🏆 GRAND CAPSTONE: Complete formal verification of natural number bounds,
    exterior basin scale, rational signature quotient, and asymptotic approach to the boundary -/
theorem grand_natural_embedding_synthesis (n : ℝ) (hn : 2 ≤ n) :
    (apollonianIntEmbedding n = 1 - 4 / (2 * n + 1)) ∧
    (0 < apollonianIntEmbedding n ∧ apollonianIntEmbedding n < 1) ∧
    (intNaturalScale n < 0) ∧
    (intSignatureQuotient n = (4 - 8 * n) / (4 * n ^ 2 - 4 * n + 5)) ∧
    (Tendsto apollonianIntEmbedding atTop (𝓝 1)) ∧
    (Tendsto intNaturalScale atTop (𝓝 0)) ∧
    (Tendsto intSignatureQuotient atTop (𝓝 0)) := by
  have h_ne : 2 * n + 1 ≠ 0 := by linarith
  exact ⟨apollonianIntEmbedding_eq_one_sub n h_ne,
         apollonianIntEmbedding_bounds n hn,
         intNaturalScale_neg n hn,
         intSignatureQuotient_eq n h_ne,
         tendsto_apollonianIntEmbedding_atTop,
         tendsto_intNaturalScale_atTop,
         tendsto_intSignatureQuotient_atTop⟩

end

end InfoGeometry.Projective.NaturalEmbedding
