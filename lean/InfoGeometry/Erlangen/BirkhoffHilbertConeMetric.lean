/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Projective.GeneralHilbertConeMetric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Birkhoff–Hilbert Projective Cone Metric, Cross-Ratio Chord Formula, and Contraction Theorem

This owner module builds the complete Felix Klein projective / Birkhoff–Hilbert cone metric
architecture on top of `InfoGeometry.Projective.GeneralHilbertConeMetric` (`coneLE`, `upperGauge`,
and `hilbertOrderDistance` on an arbitrary Mathlib `ProperCone ℝ E`):

1. **General Birkhoff–Hilbert Metric `d_Ω(x, y) = (1/2) log (M_Ω(x, y) / m_Ω(x, y))`**:
   Defines `lowerGauge C x y := (upperGauge C y x)⁻¹` and
   `birkhoffHilbertMetric C x y := (1 / 2) * Real.log (upperGauge C x y / lowerGauge C x y)`,
   proves metric nonnegativity, symmetry, triangle inequality, projective ray invariance,
   closed-cone infimum attainment (`coneLE_upperGauge_of_mem_interior`), and the sharp ray-zero
   characterization `birkhoffHilbertMetric C x y = 0 ↔ ∃ c > 0, x = c • y`.
2. **Projective Cross-Ratio Chord Formula `d_Ω(x, y) = (1/2) log [a, x; y, b]`**:
   For any chord through a proper cone meeting `∂C` in linearly independent boundary rays `u, v`,
   evaluates `upperGauge` and `lowerGauge` explicitly and proves that `birkhoffHilbertMetric`
   equals `(1 / 2) * Real.log (scalarCrossRatio τ_a τ_x τ_y τ_b)`.
3. **Positive Linear Non-Expansiveness & Birkhoff's Contraction Theorem**:
   Proves Birkhoff's Mean-Value / `tanh(Δ/2)` derivative bound in pure real analysis (`HasDerivAt.log`
   + `image_sub_le_mul_sub_of_deriv_le`), shows positive linear operators are non-expansive, and
   proves the full **Birkhoff Contraction Theorem**: if `T : E₁ →ₗ[ℝ] E₂` maps nonzero elements of
   `C₁` into `interior C₂` with projective diameter `≤ Δ`, then
   `birkhoffHilbertMetric C₂ (T x) (T y) ≤ Real.tanh (Δ / 2) * birkhoffHilbertMetric C₁ x y`.
4. **Positive Orthant `ℝⁿ_{≥0}` & Concrete `2 × 2` Contraction Witness (`tanh((log 2)/2) = 1/3`)**:
   Instantiates `orthantProperCone n := ProperCone.positive ℝ (Fin n → ℝ)`, characterizes its
   interior (`∀ i, 0 < v i`), proves noncommutativity on `Matrix (Fin 2) (Fin 2) ℝ`, and certifies
   that `posMatA = !![2, 1; 1, 2]` contracts the orthant Birkhoff–Hilbert metric by `1 / 3`.

No `sorry`, `admit`, `native_decide`, or custom axioms are used.
-/

noncomputable section

namespace InfoGeometry.Erlangen.BirkhoffHilbertConeMetric

open Filter Set Metric
open InfoGeometry.Projective.GeneralHilbertConeMetric
open InfoGeometry.MetaCompiler

/-! ## Section 1: Pure Scalar Cross-Ratio, Hyperbolic Tangent, & Birkhoff Mean-Value Kernel -/

/-- Projective cross-ratio `[a, x; y, b] := ((y - a) * (b - x)) / ((x - a) * (b - y))`
ordered so `a < x < y < b` gives `1 < [a, x; y, b]`. -/
def scalarCrossRatio (a x y b : ℝ) : ℝ :=
  ((y - a) * (b - x)) / ((x - a) * (b - y))

theorem scalarCrossRatio_pos_of_strict_order {a x y b : ℝ}
    (hax : a < x) (hxy : x < y) (hyb : y < b) :
    0 < scalarCrossRatio a x y b := by
  have h1 : 0 < y - a := sub_pos.mpr (hax.trans hxy)
  have h2 : 0 < b - x := sub_pos.mpr (hxy.trans hyb)
  have h3 : 0 < x - a := sub_pos.mpr hax
  have h4 : 0 < b - y := sub_pos.mpr hyb
  unfold scalarCrossRatio
  exact div_pos (mul_pos h1 h2) (mul_pos h3 h4)

theorem scalarCrossRatio_gt_one_of_strict_order {a x y b : ℝ}
    (hax : a < x) (hxy : x < y) (hyb : y < b) :
    1 < scalarCrossRatio a x y b := by
  have hxa : 0 < x - a := sub_pos.mpr hax
  have hby : 0 < b - y := sub_pos.mpr hyb
  have hden : 0 < (x - a) * (b - y) := mul_pos hxa hby
  have hyx : 0 < y - x := sub_pos.mpr hxy
  have hba : 0 < b - a := sub_pos.mpr (hax.trans (hxy.trans hyb))
  have hdiff : 0 < (y - a) * (b - x) - (x - a) * (b - y) := by
    have hid : (y - a) * (b - x) - (x - a) * (b - y) = (y - x) * (b - a) := by ring
    rw [hid]
    exact mul_pos hyx hba
  unfold scalarCrossRatio
  rw [one_lt_div hden]
  linarith [hdiff]

theorem tanh_half_eq_exp_ratio (Δ : ℝ) :
    Real.tanh (Δ / 2) = (Real.exp Δ - 1) / (Real.exp Δ + 1) := by
  rw [Real.tanh_eq]
  have hpos : 0 < Real.exp (Δ / 2) := Real.exp_pos (Δ / 2)
  have hne : Real.exp (Δ / 2) ≠ 0 := hpos.ne'
  have hmul : Real.exp (Δ / 2) * Real.exp (Δ / 2) = Real.exp Δ := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hneg : Real.exp (-(Δ / 2)) * Real.exp (Δ / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hden1 : Real.exp (Δ / 2) + Real.exp (-(Δ / 2)) ≠ 0 := by positivity
  calc
    (Real.exp (Δ / 2) - Real.exp (-(Δ / 2))) / (Real.exp (Δ / 2) + Real.exp (-(Δ / 2)))
        = ((Real.exp (Δ / 2) - Real.exp (-(Δ / 2))) * Real.exp (Δ / 2)) /
            ((Real.exp (Δ / 2) + Real.exp (-(Δ / 2))) * Real.exp (Δ / 2)) := by
          field_simp [hne, hden1]
    _ = (Real.exp Δ - 1) / (Real.exp Δ + 1) := by
          rw [sub_mul, add_mul, hmul, hneg]

private lemma birkhoff_exp_sq_gap (s p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Real.exp s * (Real.sqrt q + Real.sqrt p) ^ 2 ≤ (Real.exp s * q + 1) * (Real.exp s * p + 1) := by
  have hsqrtq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  have hsqrtp : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
  have hid :
      (Real.exp s * q + 1) * (Real.exp s * p + 1) - Real.exp s * (Real.sqrt q + Real.sqrt p) ^ 2 =
        (Real.exp s * (Real.sqrt q * Real.sqrt p) - 1) ^ 2 := by
    calc
      (Real.exp s * q + 1) * (Real.exp s * p + 1) - Real.exp s * (Real.sqrt q + Real.sqrt p) ^ 2
          = (Real.exp s * Real.sqrt q ^ 2 + 1) * (Real.exp s * Real.sqrt p ^ 2 + 1) -
              Real.exp s * (Real.sqrt q + Real.sqrt p) ^ 2 := by rw [hsqrtq, hsqrtp]
      _ = (Real.exp s * (Real.sqrt q * Real.sqrt p) - 1) ^ 2 := by ring
  have hsq : 0 ≤ (Real.exp s * (Real.sqrt q * Real.sqrt p) - 1) ^ 2 := sq_nonneg _
  linarith

private lemma birkhoff_deriv_algebra_bound {s p q Δ : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) (hΔ : 0 ≤ Δ) (hqΔ : q / p ≤ Real.exp (2 * Δ)) :
    (Real.exp s * (q - p)) / ((Real.exp s * q + 1) * (Real.exp s * p + 1)) ≤
      (Real.exp Δ - 1) / (Real.exp Δ + 1) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsum_pos : 0 < Real.sqrt q + Real.sqrt p := add_pos hsq hsp
  have hEs : 0 < Real.exp s := Real.exp_pos s
  have hq_diff : q - p = (Real.sqrt q - Real.sqrt p) * (Real.sqrt q + Real.sqrt p) := by
    have h1 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
    have h2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
    nlinarith
  have hsqrt_le : Real.sqrt q ≤ Real.sqrt p * Real.exp Δ := by
    have hexp2 : Real.exp (2 * Δ) = (Real.exp Δ) ^ 2 := by
      rw [two_mul, Real.exp_add, sq]
    have hmul : q ≤ p * (Real.exp Δ) ^ 2 := by
      have h1 : Real.exp (2 * Δ) * p ≥ q := (div_le_iff₀ hp).mp hqΔ
      nlinarith [h1, hexp2]
    have hsq_le : Real.sqrt q ^ 2 ≤ (Real.sqrt p * Real.exp Δ) ^ 2 := by
      rw [Real.sq_sqrt hq.le, mul_pow, Real.sq_sqrt hp.le]
      exact hmul
    exact le_of_sq_le_sq hsq_le (mul_nonneg hsp.le (Real.exp_pos Δ).le)
  have hstep1 :
      (Real.exp s * (q - p)) / ((Real.exp s * q + 1) * (Real.exp s * p + 1)) ≤
        (Real.sqrt q - Real.sqrt p) / (Real.sqrt q + Real.sqrt p) := by
    have hdenB : 0 < Real.exp s * (Real.sqrt q + Real.sqrt p) ^ 2 := by positivity
    have hnum : 0 ≤ Real.exp s * (q - p) := by
      apply mul_nonneg hEs.le
      linarith
    have hle_den :
        Real.exp s * (Real.sqrt q + Real.sqrt p) ^ 2 ≤
          (Real.exp s * q + 1) * (Real.exp s * p + 1) :=
      birkhoff_exp_sq_gap s p q hp.le hq.le
    have hdiv1 := div_le_div_of_nonneg_left hnum hdenB hle_den
    have heq :
        (Real.exp s * (q - p)) / (Real.exp s * (Real.sqrt q + Real.sqrt p) ^ 2) =
          (Real.sqrt q - Real.sqrt p) / (Real.sqrt q + Real.sqrt p) := by
      rw [hq_diff]
      field_simp [hEs.ne', hsum_pos.ne']
    exact hdiv1.trans_eq heq
  have hstep2 :
      (Real.sqrt q - Real.sqrt p) / (Real.sqrt q + Real.sqrt p) ≤
        (Real.exp Δ - 1) / (Real.exp Δ + 1) := by
    have hden_exp : 0 < Real.exp Δ + 1 := by positivity
    rw [div_le_div_iff₀ hsum_pos hden_exp]
    have hexp_nonneg : 0 ≤ Real.exp Δ := (Real.exp_pos Δ).le
    have h1exp : 1 ≤ Real.exp Δ := Real.one_le_exp hΔ
    nlinarith [hsqrt_le, hexp_nonneg, h1exp]
  exact hstep1.trans hstep2

private lemma birkhoff_log_homographic_diff_le {p q Δ t : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) (hΔ : 0 ≤ Δ) (hqΔ : q / p ≤ Real.exp (2 * Δ)) (ht : 0 ≤ t) :
    Real.log (((Real.exp t * q + 1) / (q + 1)) * ((p + 1) / (Real.exp t * p + 1))) ≤
      Real.tanh (Δ / 2) * t := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  let f : ℝ → ℝ := fun s => Real.log (Real.exp s * q + 1) - Real.log (Real.exp s * p + 1)
  have hf_hasDeriv :
      ∀ s : ℝ, HasDerivAt f
        ((Real.exp s * (q - p)) / ((Real.exp s * q + 1) * (Real.exp s * p + 1))) s := by
    intro s
    have hEq_pos : Real.exp s * q + 1 ≠ 0 := by positivity
    have hEp_pos : Real.exp s * p + 1 ≠ 0 := by positivity
    have h1 : HasDerivAt (fun x => Real.log (Real.exp x * q + 1))
        ((Real.exp s * q) / (Real.exp s * q + 1)) s := by
      have hlin := ((Real.hasDerivAt_exp s).mul_const q).add_const 1
      simpa using hlin.log hEq_pos
    have h2 : HasDerivAt (fun x => Real.log (Real.exp x * p + 1))
        ((Real.exp s * p) / (Real.exp s * p + 1)) s := by
      have hlin := ((Real.hasDerivAt_exp s).mul_const p).add_const 1
      simpa using hlin.log hEp_pos
    have halg :
        (Real.exp s * q) / (Real.exp s * q + 1) - (Real.exp s * p) / (Real.exp s * p + 1) =
          (Real.exp s * (q - p)) / ((Real.exp s * q + 1) * (Real.exp s * p + 1)) := by
      field_simp [hEq_pos, hEp_pos]
      ring
    convert h1.sub h2
    exact halg.symm
  have hf_diff : Differentiable ℝ f := fun s => (hf_hasDeriv s).differentiableAt
  have hderiv_le : ∀ s : ℝ, deriv f s ≤ Real.tanh (Δ / 2) := by
    intro s
    rw [(hf_hasDeriv s).deriv, tanh_half_eq_exp_ratio]
    exact birkhoff_deriv_algebra_bound hp hpq hΔ hqΔ
  have hmvt := image_sub_le_mul_sub_of_deriv_le hf_diff hderiv_le ht
  have hf0 : f 0 = Real.log (q + 1) - Real.log (p + 1) := by
    simp [f, Real.exp_zero]
  have hEtq : Real.exp t * q + 1 ≠ 0 := by positivity
  have hEtp : Real.exp t * p + 1 ≠ 0 := by positivity
  have hq1 : q + 1 ≠ 0 := by positivity
  have hp1 : p + 1 ≠ 0 := by positivity
  have hlog_eq :
      Real.log (((Real.exp t * q + 1) / (q + 1)) * ((p + 1) / (Real.exp t * p + 1))) =
        f t - f 0 := by
    have hdiv1 : 0 < (Real.exp t * q + 1) / (q + 1) := by positivity
    have hdiv2 : 0 < (p + 1) / (Real.exp t * p + 1) := by positivity
    rw [Real.log_mul hdiv1.ne' hdiv2.ne', Real.log_div hEtq hq1, Real.log_div hp1 hEtp, hf0]
    simp only [f]
    ring
  rw [hlog_eq]
  linarith [hmvt]

private lemma birkhoff_chord_gauge_bounds_arith {τ_a τ_x τ_y τ_b r : ℝ}
    (hax : τ_a < τ_x) (hxy : τ_x < τ_y) (hyb : τ_y < τ_b) :
    0 < (τ_b - τ_x) / (τ_b - τ_y) ∧
    0 ≤ ((τ_b - τ_x) / (τ_b - τ_y)) * ((τ_y - τ_a) / (τ_b - τ_a)) -
          ((τ_x - τ_a) / (τ_b - τ_a)) ∧
    (((τ_b - τ_x) / (τ_b - τ_y)) * ((τ_b - τ_y) / (τ_b - τ_a)) -
          ((τ_b - τ_x) / (τ_b - τ_a)) = 0) ∧
    (0 ≤ r * ((τ_b - τ_y) / (τ_b - τ_a)) - ((τ_b - τ_x) / (τ_b - τ_a)) →
      (τ_b - τ_x) / (τ_b - τ_y) ≤ r) := by
  have hab : 0 < τ_b - τ_a := sub_pos.mpr (hax.trans (hxy.trans hyb))
  have hby : 0 < τ_b - τ_y := sub_pos.mpr hyb
  have hbx : 0 < τ_b - τ_x := sub_pos.mpr (hxy.trans hyb)
  refine ⟨div_pos hbx hby, ?_, ?_, ?_⟩
  · have hid :
        ((τ_b - τ_x) / (τ_b - τ_y)) * ((τ_y - τ_a) / (τ_b - τ_a)) - ((τ_x - τ_a) / (τ_b - τ_a)) =
          ((τ_y - τ_x) * (τ_b - τ_a)) / ((τ_b - τ_y) * (τ_b - τ_a)) := by
      field_simp [hby.ne', hab.ne']
      ring
    rw [hid]
    have h1 : 0 < τ_y - τ_x := sub_pos.mpr hxy
    exact div_nonneg (mul_pos h1 hab).le (mul_pos hby hab).le
  · field_simp [hby.ne', hab.ne']
    ring
  · intro hr
    have hdiv_pos : 0 < (τ_b - τ_y) / (τ_b - τ_a) := div_pos hby hab
    have hmul : (τ_b - τ_x) / (τ_b - τ_a) ≤ r * ((τ_b - τ_y) / (τ_b - τ_a)) := by linarith
    have hdiv := (div_le_iff₀ hdiv_pos).mpr hmul
    have hid : ((τ_b - τ_x) / (τ_b - τ_a)) / ((τ_b - τ_y) / (τ_b - τ_a)) =
        (τ_b - τ_x) / (τ_b - τ_y) := by
      field_simp [hab.ne', hby.ne']
    linarith [hdiv, hid]

private lemma birkhoff_chord_rev_bounds_arith {τ_a τ_x τ_y τ_b r : ℝ}
    (hax : τ_a < τ_x) (hxy : τ_x < τ_y) (hyb : τ_y < τ_b) :
    0 < (τ_y - τ_a) / (τ_x - τ_a) ∧
    0 ≤ ((τ_y - τ_a) / (τ_x - τ_a)) * ((τ_b - τ_x) / (τ_b - τ_a)) -
          ((τ_b - τ_y) / (τ_b - τ_a)) ∧
    (((τ_y - τ_a) / (τ_x - τ_a)) * ((τ_x - τ_a) / (τ_b - τ_a)) -
          ((τ_y - τ_a) / (τ_b - τ_a)) = 0) ∧
    (0 ≤ r * ((τ_x - τ_a) / (τ_b - τ_a)) - ((τ_y - τ_a) / (τ_b - τ_a)) →
      (τ_y - τ_a) / (τ_x - τ_a) ≤ r) := by
  have hab : 0 < τ_b - τ_a := sub_pos.mpr (hax.trans (hxy.trans hyb))
  have hxa : 0 < τ_x - τ_a := sub_pos.mpr hax
  have hya : 0 < τ_y - τ_a := sub_pos.mpr (hax.trans hxy)
  refine ⟨div_pos hya hxa, ?_, ?_, ?_⟩
  · have hid :
        ((τ_y - τ_a) / (τ_x - τ_a)) * ((τ_b - τ_x) / (τ_b - τ_a)) - ((τ_b - τ_y) / (τ_b - τ_a)) =
          ((τ_y - τ_x) * (τ_b - τ_a)) / ((τ_x - τ_a) * (τ_b - τ_a)) := by
      field_simp [hxa.ne', hab.ne']
      ring
    rw [hid]
    have h1 : 0 < τ_y - τ_x := sub_pos.mpr hxy
    exact div_nonneg (mul_pos h1 hab).le (mul_pos hxa hab).le
  · field_simp [hxa.ne', hab.ne']
    ring
  · intro hr
    have hdiv_pos : 0 < (τ_x - τ_a) / (τ_b - τ_a) := div_pos hxa hab
    have hmul : (τ_y - τ_a) / (τ_b - τ_a) ≤ r * ((τ_x - τ_a) / (τ_b - τ_a)) := by linarith
    have hdiv := (div_le_iff₀ hdiv_pos).mpr hmul
    have hid : ((τ_y - τ_a) / (τ_b - τ_a)) / ((τ_x - τ_a) / (τ_b - τ_a)) =
        (τ_y - τ_a) / (τ_x - τ_a) := by
      field_simp [hab.ne', hxa.ne']
    linarith [hdiv, hid]

private lemma birkhoff_chord_ratio_eq_crossRatio {τ_a τ_x τ_y τ_b : ℝ}
    (hax : τ_a < τ_x) (hxy : τ_x < τ_y) (hyb : τ_y < τ_b) :
    ((τ_b - τ_x) / (τ_b - τ_y)) / ((τ_x - τ_a) / (τ_y - τ_a)) =
      scalarCrossRatio τ_a τ_x τ_y τ_b := by
  have h1 : (τ_b - τ_y) ≠ 0 := (sub_pos.mpr hyb).ne'
  have h2 : (τ_x - τ_a) ≠ 0 := (sub_pos.mpr hax).ne'
  have h3 : (τ_y - τ_a) ≠ 0 := (sub_pos.mpr (hax.trans hxy)).ne'
  unfold scalarCrossRatio
  field_simp [h1, h2, h3]

private lemma birkhoff_fwd_coeff_u {α β q : ℝ} (hq : 0 < q) :
    (β * q + α) / (q + 1) - β = -((β - α) / (q + 1)) := by
  have hq1 : q + 1 ≠ 0 := by linarith [hq]
  field_simp [hq1]
  ring

private lemma birkhoff_fwd_coeff_v {α β q : ℝ} (hq : 0 < q) :
    (β * q + α) / (q + 1) - α = q * ((β - α) / (q + 1)) := by
  have hq1 : q + 1 ≠ 0 := by linarith [hq]
  field_simp [hq1]
  ring

private lemma birkhoff_rev_coeff_u {α β p : ℝ} (hα : 0 < α) (hβα : α < β) (hp : 0 < p) :
    ((p + 1) / (β * p + α)) * β - 1 = (β - α) / (β * p + α) := by
  have hbp : β * p + α ≠ 0 := by
    have : 0 < β * p + α := by nlinarith [hα, hβα, hp]
    exact this.ne'
  calc
    ((p + 1) / (β * p + α)) * β - 1
        = ((p + 1) * β) / (β * p + α) - (β * p + α) / (β * p + α) := by
          rw [div_mul_eq_mul_div, div_self hbp]
    _ = ((p + 1) * β - (β * p + α)) / (β * p + α) := div_sub_div_same _ _ _
    _ = (β - α) / (β * p + α) := by congr 1; ring

private lemma birkhoff_rev_coeff_v {α β p : ℝ} (hα : 0 < α) (hβα : α < β) (hp : 0 < p) :
    ((p + 1) / (β * p + α)) * α - 1 = -(p * ((β - α) / (β * p + α))) := by
  have hbp : β * p + α ≠ 0 := by
    have : 0 < β * p + α := by nlinarith [hα, hβα, hp]
    exact this.ne'
  calc
    ((p + 1) / (β * p + α)) * α - 1
        = ((p + 1) * α) / (β * p + α) - (β * p + α) / (β * p + α) := by
          rw [div_mul_eq_mul_div, div_self hbp]
    _ = ((p + 1) * α - (β * p + α)) / (β * p + α) := div_sub_div_same _ _ _
    _ = -(p * ((β - α) / (β * p + α))) := by rw [mul_div_assoc', ← neg_div]; congr 1; ring

private lemma birkhoff_contraction_prod_bound {M1 M2 β α q p : ℝ}
    (hM1 : 0 < M1) (hM2 : 0 < M2) (hα : 0 < α) (hq : 0 < q) (hp : 0 < p)
    (hb1 : M1 ≤ (β * q + α) / (q + 1)) (hb2 : M2 ≤ (p + 1) / (β * p + α)) (hβ : α < β) :
    M1 * M2 ≤ (((β / α) * q + 1) / (q + 1)) * ((p + 1) / ((β / α) * p + 1)) := by
  have hq1 : 0 < q + 1 := add_pos hq zero_lt_one
  have hβp : 0 < β * p + α := by nlinarith [hα, hβ, hp]
  have hR1 : 0 ≤ (β * q + α) / (q + 1) := hM1.le.trans hb1
  have hmul : M1 * M2 ≤ ((β * q + α) / (q + 1)) * ((p + 1) / (β * p + α)) :=
    mul_le_mul hb1 hb2 hM2.le hR1
  have halg :
      ((β * q + α) / (q + 1)) * ((p + 1) / (β * p + α)) =
        (((β / α) * q + 1) / (q + 1)) * ((p + 1) / ((β / α) * p + 1)) := by
    have hαne : α ≠ 0 := hα.ne'
    have hq1ne : q + 1 ≠ 0 := hq1.ne'
    have hbpne : β * p + α ≠ 0 := hβp.ne'
    have hbp2 : (β / α) * p + 1 ≠ 0 := by
      have : 0 < (β / α) * p + 1 := by
        have hba : 0 < β / α := div_pos (hα.trans hβ) hα
        nlinarith [hba, hp]
      exact this.ne'
    field_simp [hαne, hq1ne, hbpne, hbp2]
  exact hmul.trans_eq halg

/-! ## Section 2: General Birkhoff–Hilbert Cone Metric, Closed Attainment, & Ray-Zero Theorem -/

section GeneralCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lower order gauge `m_Ω(x, y) := sup { r ≥ 0 | r • y ≤_Ω x } = (M_Ω(y, x))⁻¹`. -/
def lowerGauge (C : ProperCone ℝ E) (x y : E) : ℝ :=
  (upperGauge C y x)⁻¹

/-- Felix Klein / Birkhoff–Hilbert projective cone metric
`d_Ω(x, y) = (1 / 2) * log (M_Ω(x, y) / m_Ω(x, y))`. -/
def birkhoffHilbertMetric (C : ProperCone ℝ E) (x y : E) : ℝ :=
  (1 / 2 : ℝ) * Real.log (upperGauge C x y / lowerGauge C x y)

theorem birkhoffHilbertMetric_eq_half_hilbertOrderDistance (C : ProperCone ℝ E) (x y : E) :
    birkhoffHilbertMetric C x y = (1 / 2 : ℝ) * hilbertOrderDistance C x y := by
  simp only [birkhoffHilbertMetric, lowerGauge, hilbertOrderDistance, div_inv_eq_mul]

theorem birkhoffHilbertMetric_nonneg (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient) [Nontrivial E]
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E)) :
    0 ≤ birkhoffHilbertMetric C x y := by
  rw [birkhoffHilbertMetric_eq_half_hilbertOrderDistance]
  exact mul_nonneg (by norm_num) (hilbertOrderDistance_nonneg C hC hx hy)

theorem birkhoffHilbertMetric_symm (C : ProperCone ℝ E) (x y : E) :
    birkhoffHilbertMetric C x y = birkhoffHilbertMetric C y x := by
  rw [birkhoffHilbertMetric_eq_half_hilbertOrderDistance,
    birkhoffHilbertMetric_eq_half_hilbertOrderDistance,
    hilbertOrderDistance_symm]

theorem birkhoffHilbertMetric_projective (C : ProperCone ℝ E)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x y : E) :
    birkhoffHilbertMetric C (a • x) (b • y) = birkhoffHilbertMetric C x y := by
  rw [birkhoffHilbertMetric_eq_half_hilbertOrderDistance,
    birkhoffHilbertMetric_eq_half_hilbertOrderDistance,
    hilbertOrderDistance_projective C a b ha hb x y]

theorem birkhoffHilbertMetric_triangle (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient) [Nontrivial E]
    {x y z : E} (hx : x ∈ interior (C : Set E))
    (hy : y ∈ interior (C : Set E)) (hz : z ∈ interior (C : Set E)) :
    birkhoffHilbertMetric C x z ≤
      birkhoffHilbertMetric C x y + birkhoffHilbertMetric C y z := by
  rw [birkhoffHilbertMetric_eq_half_hilbertOrderDistance,
    birkhoffHilbertMetric_eq_half_hilbertOrderDistance,
    birkhoffHilbertMetric_eq_half_hilbertOrderDistance]
  have htri := hilbertOrderDistance_triangle C hC hx hy hz
  linarith

/-- Closedness of a proper cone implies the infimum order gauge `M_Ω(x, y)` is attained
whenever `y ∈ interior C`. -/
theorem coneLE_upperGauge_of_mem_interior (C : ProperCone ℝ E)
    {x y : E} (hy : y ∈ interior (C : Set E)) :
    coneLE C x (upperGauge C x y • y) := by
  change upperGauge C x y • y - x ∈ C
  by_contra hnot
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((C.isClosed.isOpen_compl).mem_nhds hnot)
  let δ : ℝ := ε / (‖y‖ + 1)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let f : Set ℝ := { r : ℝ | 0 ≤ r ∧ coneLE C x (r • y) }
  have hne : f.Nonempty := exists_cone_upper_bound_of_mem_interior C hy
  obtain ⟨r, hrf, hr_lt⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right (upperGauge C x y) hδ_pos)
  have hr_ge : upperGauge C x y ≤ r := csInf_le ⟨0, fun s hs => hs.1⟩ hrf
  have hdist : dist (r • y - x) (upperGauge C x y • y - x) < ε := by
    rw [dist_eq_norm]
    have hdiff : (r • y - x) - (upperGauge C x y • y - x) = (r - upperGauge C x y) • y := by
      module
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr_ge)]
    have hy_nn : 0 ≤ ‖y‖ := norm_nonneg y
    have hr_sub : r - upperGauge C x y < δ := sub_lt_iff_lt_add'.mpr hr_lt
    have hy1_pos : 0 < ‖y‖ + 1 := by positivity
    calc
      (r - upperGauge C x y) * ‖y‖ ≤ δ * ‖y‖ :=
        mul_le_mul_of_nonneg_right hr_sub.le hy_nn
      _ < δ * (‖y‖ + 1) := mul_lt_mul_of_pos_left (lt_add_one ‖y‖) hδ_pos
      _ = ε := by
        dsimp [δ]
        field_simp [hy1_pos.ne']
  have hcompl : r • y - x ∈ (C : Set E)ᶜ := hball hdist
  exact hcompl hrf.2

theorem birkhoffHilbertMetric_eq_zero_iff_same_ray (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient) [Nontrivial E]
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E)) :
    birkhoffHilbertMetric C x y = 0 ↔ ∃ c : ℝ, 0 < c ∧ x = c • y := by
  constructor
  · intro hzero
    have hMxy : 0 < upperGauge C x y := upperGauge_pos_of_mem_interior C hC hx hy
    have hMyx : 0 < upperGauge C y x := upperGauge_pos_of_mem_interior C hC hy hx
    have hprod_pos : 0 < upperGauge C x y * upperGauge C y x := mul_pos hMxy hMyx
    have hlog0 : Real.log (upperGauge C x y * upperGauge C y x) = 0 := by
      rw [birkhoffHilbertMetric_eq_half_hilbertOrderDistance, hilbertOrderDistance] at hzero
      linarith
    have hprod1 : upperGauge C x y * upperGauge C y x = 1 :=
      (Real.log_eq_zero.mp hlog0).resolve_left hprod_pos.ne' |>
        fun h => h.resolve_right (by linarith [hprod_pos])
    have hMyx_eq : upperGauge C y x = (upperGauge C x y)⁻¹ := by
      field_simp [hMxy.ne']
      linarith [hprod1]
    have hle1 : coneLE C x (upperGauge C x y • y) := coneLE_upperGauge_of_mem_interior C hy
    have hle2_raw : coneLE C y (upperGauge C y x • x) := coneLE_upperGauge_of_mem_interior C hx
    have hle2 : coneLE C (upperGauge C x y • y) x := by
      change upperGauge C y x • x - y ∈ C at hle2_raw
      change x - upperGauge C x y • y ∈ C
      have hsc := C.smul_mem hle2_raw hMxy.le
      have hrew : upperGauge C x y • (upperGauge C y x • x - y) = x - upperGauge C x y • y := by
        rw [smul_sub, smul_smul, hMyx_eq, mul_inv_cancel₀ hMxy.ne', one_smul]
      rwa [hrew] at hsc
    exact ⟨upperGauge C x y, hMxy, coneLE_antisymm C hC hle1 hle2⟩
  · rintro ⟨c, hc, rfl⟩
    have hproj := birkhoffHilbertMetric_projective C c 1 hc zero_lt_one y y
    rw [one_smul] at hproj
    rw [hproj, birkhoffHilbertMetric_eq_half_hilbertOrderDistance, hilbertOrderDistance,
      upperGauge_self_eq_one_of_mem_interior C hC hy, mul_one, Real.log_one, mul_zero]

/-! ## Projectivization: the metric on positive rays, not just representatives -/

/-- Interior points of a proper cone, used as representatives of its projective
interior rays. -/
abbrev ConeInteriorPoint (C : ProperCone ℝ E) :=
  {x : E // x ∈ interior (C : Set E)}

/-- Two interior points determine the same positive projective ray exactly
when one is a strictly positive scalar multiple of the other. -/
def coneInteriorRaySetoid (C : ProperCone ℝ E) : Setoid (ConeInteriorPoint C) where
  r x y := ∃ c : ℝ, 0 < c ∧ x.1 = c • y.1
  iseqv := {
    refl := fun x => ⟨1, one_pos, by simp⟩
    symm := by
      intro x y h
      rcases h with ⟨c, hc, hxy⟩
      refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
      rw [hxy, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    trans := by
      intro x y z hxy hyz
      rcases hxy with ⟨a, ha, hxy⟩
      rcases hyz with ⟨b, hb, hyz⟩
      refine ⟨a * b, mul_pos ha hb, ?_⟩
      rw [hxy, hyz, smul_smul]
  }

/-- The projective interior of `C`: equivalence classes of its interior
points under positive rescaling. -/
abbrev ConeInteriorRay (C : ProperCone ℝ E) :=
  Quotient (coneInteriorRaySetoid C)

/-- The Birkhoff–Hilbert distance descends from interior representatives to
the quotient by positive rescaling. -/
noncomputable def birkhoffRayDist (C : ProperCone ℝ E) :
    ConeInteriorRay C → ConeInteriorRay C → ℝ :=
  fun q r => Quotient.liftOn₂ q r
    (fun x y => birkhoffHilbertMetric C x.1 y.1) (by
      intro x y x' y' hxx hyy
      rcases hxx with ⟨a, ha, hx⟩
      rcases hyy with ⟨b, hb, hy⟩
      rw [hx, hy]
      exact birkhoffHilbertMetric_projective C a b ha hb x'.1 y'.1)

@[simp]
theorem birkhoffRayDist_mk (C : ProperCone ℝ E) (x y : ConeInteriorPoint C) :
    birkhoffRayDist C (Quotient.mk _ x) (Quotient.mk _ y) =
      birkhoffHilbertMetric C x.1 y.1 := rfl

/-- The descended distance is nonnegative on the projective interior. -/
theorem birkhoffRayDist_nonneg (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient) [Nontrivial E]
    (x y : ConeInteriorRay C) : 0 ≤ birkhoffRayDist C x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro x y
  exact birkhoffHilbertMetric_nonneg C hC x.2 y.2

/-- The descended distance is symmetric. -/
theorem birkhoffRayDist_symm (C : ProperCone ℝ E)
    (x y : ConeInteriorRay C) : birkhoffRayDist C x y = birkhoffRayDist C y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro x y
  exact birkhoffHilbertMetric_symm C x.1 y.1

/-- The descended distance satisfies the triangle inequality. -/
theorem birkhoffRayDist_triangle (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient) [Nontrivial E]
    (x y z : ConeInteriorRay C) :
    birkhoffRayDist C x z ≤ birkhoffRayDist C x y + birkhoffRayDist C y z := by
  refine Quotient.inductionOn₃ x y z ?_
  intro x y z
  exact birkhoffHilbertMetric_triangle C hC x.2 y.2 z.2

/-- On the positive-ray quotient, zero distance is equality of rays. -/
theorem birkhoffRayDist_eq_zero_iff (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient) [Nontrivial E]
    (x y : ConeInteriorRay C) : birkhoffRayDist C x y = 0 ↔ x = y := by
  refine Quotient.inductionOn₂ x y ?_
  intro x y
  change birkhoffHilbertMetric C x.1 y.1 = 0 ↔ Quotient.mk _ x = Quotient.mk _ y
  rw [birkhoffHilbertMetric_eq_zero_iff_same_ray C hC x.2 y.2]
  constructor
  · rintro ⟨c, hc, hxy⟩
    exact Quotient.sound ⟨c, hc, hxy⟩
  · intro hq
    rcases Quotient.exact hq with ⟨c, hc, hxy⟩
    exact ⟨c, hc, hxy⟩

/-- The projective interior of a salient proper cone carries the genuine
Birkhoff–Hilbert metric. The only hypotheses needed to separate rays are
salience of the cone order and nontriviality of the ambient normed space. -/
@[instance_reducible]
noncomputable def coneInteriorRayMetricSpace (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient) [Nontrivial E] :
    MetricSpace (ConeInteriorRay C) where
  dist := birkhoffRayDist C
  dist_self x := by
    rw [birkhoffRayDist_eq_zero_iff C hC x x]
  dist_comm := birkhoffRayDist_symm C
  dist_triangle := birkhoffRayDist_triangle C hC
  eq_of_dist_eq_zero := by
    intro x y h
    exact (birkhoffRayDist_eq_zero_iff C hC x y).mp h

/-! ## Section 3: Projective Cross-Ratio Chord Formula `d_Ω(x, y) = (1/2) log [a, x; y, b]` -/

private lemma chord_affine_vec_diff (u v : E) (r α₁ α₂ β₁ β₂ : ℝ) :
    r • (α₂ • u + β₂ • v) - (α₁ • u + β₁ • v) =
      (r * α₂ - α₁) • u + (r * β₂ - β₁) • v := by
  module

theorem birkhoff_crossRatio_chord_identity (C : ProperCone ℝ E)
    {u v : E} (hu : u ∈ C) (hv : v ∈ C)
    (hsector : ∀ α β : ℝ, α • u + β • v ∈ C → 0 ≤ α ∧ 0 ≤ β)
    {τ_a τ_x τ_y τ_b : ℝ}
    (hax : τ_a < τ_x) (hxy : τ_x < τ_y) (hyb : τ_y < τ_b) :
    let p : ℝ → E := fun τ =>
      ((τ_b - τ) / (τ_b - τ_a)) • u + ((τ - τ_a) / (τ_b - τ_a)) • v
    birkhoffHilbertMetric C (p τ_x) (p τ_y) =
      (1 / 2 : ℝ) * Real.log (scalarCrossRatio τ_a τ_x τ_y τ_b) := by
  dsimp only
  let p : ℝ → E := fun τ =>
    ((τ_b - τ) / (τ_b - τ_a)) • u + ((τ - τ_a) / (τ_b - τ_a)) • v
  let rFwd : ℝ := (τ_b - τ_x) / (τ_b - τ_y)
  let rRev : ℝ := (τ_y - τ_a) / (τ_x - τ_a)
  have hMxy : upperGauge C (p τ_x) (p τ_y) = rFwd := by
    let f : Set ℝ := { r : ℝ | 0 ≤ r ∧ coneLE C (p τ_x) (r • p τ_y) }
    have hfeas : ∀ r : ℝ, (0 ≤ r ∧ coneLE C (p τ_x) (r • p τ_y)) → rFwd ≤ r := by
      rintro r ⟨_, hle⟩
      change r • p τ_y - p τ_x ∈ C at hle
      dsimp [p] at hle
      rw [chord_affine_vec_diff] at hle
      exact (birkhoff_chord_gauge_bounds_arith (r := r) hax hxy hyb).2.2.2 (hsector _ _ hle).1
    have hmem : rFwd ∈ f := by
      have har := birkhoff_chord_gauge_bounds_arith (r := rFwd) hax hxy hyb
      refine ⟨har.1.le, ?_⟩
      change rFwd • p τ_y - p τ_x ∈ C
      dsimp [p]
      rw [chord_affine_vec_diff, har.2.2.1, zero_smul, zero_add]
      exact C.smul_mem hv har.2.1
    exact le_antisymm (csInf_le ⟨rFwd, hfeas⟩ hmem) (le_csInf ⟨rFwd, hmem⟩ hfeas)
  have hMyx : upperGauge C (p τ_y) (p τ_x) = rRev := by
    let f : Set ℝ := { r : ℝ | 0 ≤ r ∧ coneLE C (p τ_y) (r • p τ_x) }
    have hfeas : ∀ r : ℝ, (0 ≤ r ∧ coneLE C (p τ_y) (r • p τ_x)) → rRev ≤ r := by
      rintro r ⟨_, hle⟩
      change r • p τ_x - p τ_y ∈ C at hle
      dsimp [p] at hle
      rw [chord_affine_vec_diff] at hle
      exact (birkhoff_chord_rev_bounds_arith (r := r) hax hxy hyb).2.2.2 (hsector _ _ hle).2
    have hmem : rRev ∈ f := by
      have har := birkhoff_chord_rev_bounds_arith (r := rRev) hax hxy hyb
      refine ⟨har.1.le, ?_⟩
      change rRev • p τ_x - p τ_y ∈ C
      dsimp [p]
      rw [chord_affine_vec_diff, har.2.2.1, zero_smul, add_zero]
      exact C.smul_mem hu har.2.1
    exact le_antisymm (csInf_le ⟨rRev, hfeas⟩ hmem) (le_csInf ⟨rRev, hmem⟩ hfeas)
  rw [birkhoffHilbertMetric, lowerGauge, hMxy, hMyx, div_inv_eq_mul]
  congr 2
  have hmul : rFwd * rRev = rFwd / ((τ_x - τ_a) / (τ_y - τ_a)) := by
    dsimp [rFwd, rRev]
    rw [div_eq_mul_inv (τ_b - τ_x) (τ_b - τ_y), div_div_eq_mul_div]
    ring
  rw [hmul, birkhoff_chord_ratio_eq_crossRatio hax hxy hyb]

/-! ## Section 4: Positive Linear Non-Expansiveness & Birkhoff's Contraction Theorem -/

section PositiveLinearMaps

variable {E₁ E₂ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

theorem upperGauge_map_le (C₁ : ProperCone ℝ E₁) (C₂ : ProperCone ℝ E₂)
    (T : E₁ →ₗ[ℝ] E₂) (hpos : ∀ v ∈ C₁, T v ∈ C₂)
    {x y : E₁} (hy : y ∈ interior (C₁ : Set E₁)) :
    upperGauge C₂ (T x) (T y) ≤ upperGauge C₁ x y := by
  let f₁ : Set ℝ := { r : ℝ | 0 ≤ r ∧ coneLE C₁ x (r • y) }
  have hne : f₁.Nonempty := exists_cone_upper_bound_of_mem_interior C₁ hy
  apply le_csInf hne
  rintro r ⟨hr, hle⟩
  apply upperGauge_le_of_feasible C₂ (T x) (T y)
  refine ⟨hr, ?_⟩
  change r • T y - T x ∈ C₂
  have hmap : r • T y - T x = T (r • y - x) := by
    rw [map_sub, map_smul]
  rw [hmap]
  exact hpos (r • y - x) hle

theorem birkhoffHilbertMetric_map_le (C₁ : ProperCone ℝ E₁) (C₂ : ProperCone ℝ E₂)
    (hC₂ : C₂.toPointedCone.toConvexCone.Salient) [Nontrivial E₂]
    (T : E₁ →ₗ[ℝ] E₂) (hpos : ∀ v ∈ C₁, T v ∈ C₂)
    {x y : E₁} (hx : x ∈ interior (C₁ : Set E₁)) (hy : y ∈ interior (C₁ : Set E₁))
    (hTx : T x ∈ interior (C₂ : Set E₂)) (hTy : T y ∈ interior (C₂ : Set E₂)) :
    birkhoffHilbertMetric C₂ (T x) (T y) ≤ birkhoffHilbertMetric C₁ x y := by
  have hMTxy : 0 < upperGauge C₂ (T x) (T y) := upperGauge_pos_of_mem_interior C₂ hC₂ hTx hTy
  have hMTyx : 0 < upperGauge C₂ (T y) (T x) := upperGauge_pos_of_mem_interior C₂ hC₂ hTy hTx
  have hle1 := upperGauge_map_le C₁ C₂ T hpos hy (x := x)
  have hle2 := upperGauge_map_le C₁ C₂ T hpos hx (x := y)
  have hmul :
      upperGauge C₂ (T x) (T y) * upperGauge C₂ (T y) (T x) ≤
        upperGauge C₁ x y * upperGauge C₁ y x :=
    mul_le_mul hle1 hle2 hMTyx.le (hMTxy.le.trans hle1)
  rw [birkhoffHilbertMetric_eq_half_hilbertOrderDistance,
    birkhoffHilbertMetric_eq_half_hilbertOrderDistance,
    hilbertOrderDistance, hilbertOrderDistance]
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (mul_pos hMTxy hMTyx) hmul) (by norm_num)

/-- A linear equivalence carrying each proper cone onto the other preserves the
Birkhoff--Hilbert metric.  The cone and interior mapping conditions are stated
explicitly so this result applies to arbitrary normed real spaces and proper
cones without assuming finite dimension or choosing coordinates. -/
theorem birkhoffHilbertMetric_linearEquiv_isometry
    (C₁ : ProperCone ℝ E₁) (C₂ : ProperCone ℝ E₂)
    (hC₁ : C₁.toPointedCone.toConvexCone.Salient)
    (hC₂ : C₂.toPointedCone.toConvexCone.Salient)
    [Nontrivial E₁] [Nontrivial E₂]
    (e : E₁ ≃L[ℝ] E₂)
    (hpos : ∀ v ∈ C₁, e v ∈ C₂)
    (hpos_inv : ∀ w ∈ C₂, e.symm w ∈ C₁)
    {x y : E₁} (hx : x ∈ interior (C₁ : Set E₁))
    (hy : y ∈ interior (C₁ : Set E₁)) :
    birkhoffHilbertMetric C₂ (e x) (e y) = birkhoffHilbertMetric C₁ x y := by
  have hcones : e.toHomeomorph '' (C₁ : Set E₁) = C₂ := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hpos v hv
    · intro hw
      exact ⟨e.symm w, hpos_inv w hw, e.apply_symm_apply w⟩
  have hinterior : e.toHomeomorph '' interior (C₁ : Set E₁) =
      interior (C₂ : Set E₂) := by
    rw [e.toHomeomorph.image_interior, hcones]
  have hInteriorMap (v : E₁) (hv : v ∈ interior (C₁ : Set E₁)) :
      e v ∈ interior (C₂ : Set E₂) := by
    have hv' : e v ∈ e.toHomeomorph '' interior (C₁ : Set E₁) :=
      Set.mem_image_of_mem _ hv
    rw [hinterior] at hv'
    exact hv'
  have hInteriorMapInv (w : E₂) (hw : w ∈ interior (C₂ : Set E₂)) :
      e.symm w ∈ interior (C₁ : Set E₁) := by
    have hw' : w ∈ e.toHomeomorph '' interior (C₁ : Set E₁) := by
      rw [hinterior]
      exact hw
    rcases hw' with ⟨v, hv, hvw⟩
    have : e v = w := hvw
    simpa [← this] using hv
  apply le_antisymm
  · exact birkhoffHilbertMetric_map_le C₁ C₂ hC₂ e.toLinearMap hpos hx hy
      (hInteriorMap x hx) (hInteriorMap y hy)
  · have hback := birkhoffHilbertMetric_map_le C₂ C₁ hC₁ e.symm.toLinearMap
      hpos_inv (hInteriorMap x hx) (hInteriorMap y hy)
      (hInteriorMapInv (e x) (hInteriorMap x hx))
      (hInteriorMapInv (e y) (hInteriorMap y hy))
    simpa using hback

private lemma birkhoff_contraction_vec_x_id {α β : ℝ} (x y : E₁) :
    (β - α) • x = β • (x - α • y) + α • (β • y - x) := by
  module

private lemma birkhoff_contraction_vec_y_id {α β : ℝ} (x y : E₁) :
    (β - α) • y = (x - α • y) + (β • y - x) := by
  module

private lemma birkhoff_contraction_fwd_id {α β q : ℝ} (hq : 0 < q) (u v : E₂) :
    ((β * q + α) / (q + 1)) • (u + v) - (β • u + α • v) =
      ((β - α) / (q + 1)) • (q • v - u) := by
  calc
    ((β * q + α) / (q + 1)) • (u + v) - (β • u + α • v)
        = ((β * q + α) / (q + 1) - β) • u + ((β * q + α) / (q + 1) - α) • v := by module
    _ = (-((β - α) / (q + 1))) • u + (q * ((β - α) / (q + 1))) • v := by
        rw [birkhoff_fwd_coeff_u hq, birkhoff_fwd_coeff_v hq]
    _ = ((β - α) / (q + 1)) • (q • v - u) := by module

private lemma birkhoff_contraction_rev_id {α β p : ℝ} (hα : 0 < α) (hβα : α < β) (hp : 0 < p)
    (u v : E₂) :
    ((p + 1) / (β * p + α)) • (β • u + α • v) - (u + v) =
      ((β - α) / (β * p + α)) • (u - p • v) := by
  calc
    ((p + 1) / (β * p + α)) • (β • u + α • v) - (u + v)
        = (((p + 1) / (β * p + α)) * β - 1) • u +
            (((p + 1) / (β * p + α)) * α - 1) • v := by module
    _ = ((β - α) / (β * p + α)) • u + (-(p * ((β - α) / (β * p + α)))) • v := by
        rw [birkhoff_rev_coeff_u hα hβα hp, birkhoff_rev_coeff_v hα hβα hp]
    _ = ((β - α) / (β * p + α)) • (u - p • v) := by module

/-- **Birkhoff Contraction Theorem**: Any linear operator `T : E₁ →ₗ[ℝ] E₂` mapping nonzero
vectors of a salient proper cone `C₁` into `interior C₂` with projective diameter bounded by `Δ`
strictly contracts the Birkhoff–Hilbert metric by at most `Real.tanh (Δ / 2)`. -/
theorem birkhoff_contraction_theorem
    (C₁ : ProperCone ℝ E₁) (C₂ : ProperCone ℝ E₂)
    (hC₁ : C₁.toPointedCone.toConvexCone.Salient)
    (hC₂ : C₂.toPointedCone.toConvexCone.Salient)
    [Nontrivial E₁] [Nontrivial E₂]
    (T : E₁ →ₗ[ℝ] E₂)
    (hT_int : ∀ w : E₁, w ∈ C₁ → w ≠ 0 → T w ∈ interior (C₂ : Set E₂))
    {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hdiam : ∀ u v : E₁, u ∈ C₁ → u ≠ 0 → v ∈ C₁ → v ≠ 0 →
      birkhoffHilbertMetric C₂ (T u) (T v) ≤ Δ)
    {x y : E₁} (hx : x ∈ interior (C₁ : Set E₁)) (hy : y ∈ interior (C₁ : Set E₁)) :
    birkhoffHilbertMetric C₂ (T x) (T y) ≤ Real.tanh (Δ / 2) * birkhoffHilbertMetric C₁ x y := by
  let β : ℝ := upperGauge C₁ x y
  let α : ℝ := lowerGauge C₁ x y
  have hβ_pos : 0 < β := upperGauge_pos_of_mem_interior C₁ hC₁ hx hy
  have hMyx_pos : 0 < upperGauge C₁ y x := upperGauge_pos_of_mem_interior C₁ hC₁ hy hx
  have hα_pos : 0 < α := inv_pos.mpr hMyx_pos
  have hprod_ge : 1 ≤ β * upperGauge C₁ y x := by
    have hself := upperGauge_self_eq_one_of_mem_interior C₁ hC₁ hx
    have hsub := upperGauge_submultiplicative C₁ x y x hy hx
    rw [hself] at hsub
    exact hsub
  have hαβ : α ≤ β := by
    have hinv : (upperGauge C₁ y x)⁻¹ ≤ β :=
      (inv_le_iff_one_le_mul₀' hMyx_pos).mpr (by rw [mul_comm]; exact hprod_ge)
    exact hinv
  rcases eq_or_lt_of_le hαβ with hEq | hLt
  · have hMxy_yx : upperGauge C₁ x y * upperGauge C₁ y x = 1 := by
      have : α * upperGauge C₁ y x = 1 := inv_mul_cancel₀ hMyx_pos.ne'
      dsimp [β] at hEq ⊢
      rw [← hEq]
      exact this
    have hd0 : birkhoffHilbertMetric C₁ x y = 0 := by
      rw [birkhoffHilbertMetric_eq_half_hilbertOrderDistance, hilbertOrderDistance, hMxy_yx,
        Real.log_one, mul_zero]
    obtain ⟨c, hc, hxc⟩ := (birkhoffHilbertMetric_eq_zero_iff_same_ray C₁ hC₁ hx hy).mp hd0
    have hTx : T x ∈ interior (C₂ : Set E₂) :=
      hT_int x (interior_subset hx) (interior_mem_ne_zero_of_salient C₁ hC₁ hx)
    have hTy : T y ∈ interior (C₂ : Set E₂) :=
      hT_int y (interior_subset hy) (interior_mem_ne_zero_of_salient C₁ hC₁ hy)
    have hT0 : birkhoffHilbertMetric C₂ (T x) (T y) = 0 :=
      (birkhoffHilbertMetric_eq_zero_iff_same_ray C₂ hC₂ hTx hTy).mpr
        ⟨c, hc, by rw [hxc, map_smul]⟩
    rw [hT0, hd0, mul_zero]
  · let u : E₁ := x - α • y
    let v : E₁ := β • y - x
    have hv_mem : v ∈ C₁ := coneLE_upperGauge_of_mem_interior C₁ hy
    have hu_mem : u ∈ C₁ := by
      have hraw := coneLE_upperGauge_of_mem_interior C₁ hx (x := y)
      change upperGauge C₁ y x • x - y ∈ C₁ at hraw
      have hsc := C₁.smul_mem hraw hα_pos.le
      have hrew : α • (upperGauge C₁ y x • x - y) = u := by
        dsimp [u, α, lowerGauge]
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hMyx_pos.ne', one_smul]
      rwa [hrew] at hsc
    have hu_ne : u ≠ 0 := by
      intro hu0
      have hx_eq : x = α • y := sub_eq_zero.mp hu0
      have hβ_eq : β = α := by
        dsimp [β]
        rw [hx_eq, upperGauge_scale_left C₁ α hα_pos y y,
          upperGauge_self_eq_one_of_mem_interior C₁ hC₁ hy, mul_one]
      exact hLt.ne' hβ_eq
    have hv_ne : v ≠ 0 := by
      intro hv0
      have hx_eq : x = β • y := (sub_eq_zero.mp hv0).symm
      have hMyx_eq : upperGauge C₁ y x = β⁻¹ := by
        rw [hx_eq, upperGauge_scale_right C₁ β hβ_pos y y,
          upperGauge_self_eq_one_of_mem_interior C₁ hC₁ hy, mul_one]
      have hα_eq : α = β := by
        dsimp [α, lowerGauge]
        rw [hMyx_eq, inv_inv]
      exact hLt.ne hα_eq
    have hTu_int : T u ∈ interior (C₂ : Set E₂) := hT_int u hu_mem hu_ne
    have hTv_int : T v ∈ interior (C₂ : Set E₂) := hT_int v hv_mem hv_ne
    let q : ℝ := upperGauge C₂ (T u) (T v)
    let p : ℝ := lowerGauge C₂ (T u) (T v)
    have hq_pos : 0 < q := upperGauge_pos_of_mem_interior C₂ hC₂ hTu_int hTv_int
    have hMvu_pos : 0 < upperGauge C₂ (T v) (T u) :=
      upperGauge_pos_of_mem_interior C₂ hC₂ hTv_int hTu_int
    have hp_pos : 0 < p := inv_pos.mpr hMvu_pos
    have hpq : p ≤ q := by
      have hself := upperGauge_self_eq_one_of_mem_interior C₂ hC₂ hTu_int
      have hsub := upperGauge_submultiplicative C₂ (T u) (T v) (T u) hTv_int hTu_int
      rw [hself] at hsub
      exact (inv_le_iff_one_le_mul₀' hMvu_pos).mpr (by rw [mul_comm]; exact hsub)
    have hqp_exp : q / p ≤ Real.exp (2 * Δ) := by
      have hdiam_uv := hdiam u v hu_mem hu_ne hv_mem hv_ne
      rw [birkhoffHilbertMetric] at hdiam_uv
      have hlog_le : Real.log (q / p) ≤ 2 * Δ := by linarith [hdiam_uv]
      exact (Real.log_le_iff_le_exp (div_pos hq_pos hp_pos)).mp hlog_le
    have hTu_plus_Tv : (β - α) • T y = T u + T v := by
      rw [← map_smul, ← map_add, birkhoff_contraction_vec_y_id (x := x) (y := y)]
    have hTx_combo : (β - α) • T x = β • T u + α • T v := by
      rw [← map_smul, ← map_smul, ← map_smul, ← map_add,
        birkhoff_contraction_vec_x_id (x := x) (y := y)]
    have hβα_pos : 0 < β - α := sub_pos.mpr hLt
    have hbound1 : upperGauge C₂ (T x) (T y) ≤ (β * q + α) / (q + 1) := by
      rw [← upperGauge_common_scale C₂ (β - α) hβα_pos (T x) (T y)]
      apply upperGauge_le_of_feasible C₂ ((β - α) • T x) ((β - α) • T y)
      refine ⟨by positivity, ?_⟩
      change ((β * q + α) / (q + 1)) • ((β - α) • T y) - (β - α) • T x ∈ C₂
      rw [hTu_plus_Tv, hTx_combo, birkhoff_contraction_fwd_id hq_pos]
      have hcone_uv : q • T v - T u ∈ C₂ := coneLE_upperGauge_of_mem_interior C₂ hTv_int
      exact C₂.smul_mem hcone_uv (div_pos hβα_pos (by linarith [hq_pos])).le
    have hbound2 : upperGauge C₂ (T y) (T x) ≤ (p + 1) / (β * p + α) := by
      rw [← upperGauge_common_scale C₂ (β - α) hβα_pos (T y) (T x)]
      apply upperGauge_le_of_feasible C₂ ((β - α) • T y) ((β - α) • T x)
      refine ⟨by positivity, ?_⟩
      change ((p + 1) / (β * p + α)) • ((β - α) • T x) - (β - α) • T y ∈ C₂
      rw [hTx_combo, hTu_plus_Tv, birkhoff_contraction_rev_id hα_pos hLt hp_pos]
      have hraw : upperGauge C₂ (T v) (T u) • T u - T v ∈ C₂ :=
        coneLE_upperGauge_of_mem_interior C₂ hTu_int
      have hcone_uv : T u - p • T v ∈ C₂ := by
        have hsc := C₂.smul_mem hraw hp_pos.le
        have hrew : p • (upperGauge C₂ (T v) (T u) • T u - T v) = T u - p • T v := by
          dsimp [p, lowerGauge]
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hMvu_pos.ne', one_smul]
        rwa [hrew] at hsc
      have hbp_pos : 0 < β * p + α := by nlinarith [hα_pos, hLt, hp_pos]
      exact C₂.smul_mem hcone_uv (div_pos hβα_pos hbp_pos).le
    have hTx_int : T x ∈ interior (C₂ : Set E₂) :=
      hT_int x (interior_subset hx) (interior_mem_ne_zero_of_salient C₁ hC₁ hx)
    have hTy_int : T y ∈ interior (C₂ : Set E₂) :=
      hT_int y (interior_subset hy) (interior_mem_ne_zero_of_salient C₁ hC₁ hy)
    have hMTxy : 0 < upperGauge C₂ (T x) (T y) := upperGauge_pos_of_mem_interior C₂ hC₂ hTx_int hTy_int
    have hMTyx : 0 < upperGauge C₂ (T y) (T x) := upperGauge_pos_of_mem_interior C₂ hC₂ hTy_int hTx_int
    have hprod_le := birkhoff_contraction_prod_bound hMTxy hMTyx hα_pos hq_pos hp_pos hbound1 hbound2 hLt
    let t : ℝ := Real.log (β / α)
    have hβα_ge1 : 1 ≤ β / α := (one_le_div hα_pos).mpr hLt.le
    have ht_nonneg : 0 ≤ t := Real.log_nonneg hβα_ge1
    have hexp_t : Real.exp t = β / α := Real.exp_log (div_pos hβ_pos hα_pos)
    have hlog_lhs :
        Real.log (upperGauge C₂ (T x) (T y) * upperGauge C₂ (T y) (T x)) ≤
          Real.log (((Real.exp t * q + 1) / (q + 1)) * ((p + 1) / (Real.exp t * p + 1))) := by
      rw [hexp_t]
      exact Real.log_le_log (mul_pos hMTxy hMTyx) hprod_le
    have hmvt := birkhoff_log_homographic_diff_le hp_pos hpq hΔ hqp_exp ht_nonneg
    have hd1 : birkhoffHilbertMetric C₁ x y = (1 / 2 : ℝ) * t := rfl
    rw [birkhoffHilbertMetric_eq_half_hilbertOrderDistance, hilbertOrderDistance, hd1]
    have hchain : Real.log (upperGauge C₂ (T x) (T y) * upperGauge C₂ (T y) (T x)) ≤
        Real.tanh (Δ / 2) * t := hlog_lhs.trans hmvt
    linarith [hchain]

end PositiveLinearMaps

end GeneralCone

/-! ## Section 5: Positive Orthant `ℝⁿ_{≥0}`, Concrete `2 × 2` Contraction (`1 / 3`), & T17 Witness -/

/-- Salience is not a consequence of Mathlib's `ProperCone` type: the whole real line is
a closed `Nonneg ℝ` submodule, but contains both `1` and `-1`. Thus the explicit salience
premise in generic ray-separation and contraction statements cannot be removed for arbitrary
`ProperCone`s. -/
theorem topProperCone_not_salient :
    ¬ (⊤ : ProperCone ℝ ℝ).toPointedCone.toConvexCone.Salient := by
  intro hsalient
  have hone : (1 : ℝ) ∈ (⊤ : ProperCone ℝ ℝ).toPointedCone.toConvexCone := by simp
  have hnegone : -(1 : ℝ) ∈ (⊤ : ProperCone ℝ ℝ).toPointedCone.toConvexCone := by simp
  exact (hsalient 1 hone (by norm_num)) hnegone

/-- The positive orthant proper cone `ℝⁿ_{≥0} := { v : Fin n → ℝ | ∀ i, 0 ≤ v i }`. -/
abbrev orthantProperCone (n : ℕ) : ProperCone ℝ (Fin n → ℝ) :=
  ProperCone.positive ℝ (Fin n → ℝ)

theorem orthantProperCone_salient (n : ℕ) :
    (orthantProperCone n).toPointedCone.toConvexCone.Salient := by
  intro x hx hne hxneg
  apply hne
  funext i
  have h1 : 0 ≤ x i := hx i
  have h2 : 0 ≤ -x i := hxneg i
  exact le_antisymm (neg_nonneg.mp h2) h1

theorem mem_interior_orthantProperCone_of_pos {n : ℕ} {v : Fin n → ℝ}
    (hv : ∀ i : Fin n, 0 < v i) :
    v ∈ interior (orthantProperCone n : Set (Fin n → ℝ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have huniv : (orthantProperCone 0 : Set (Fin 0 → ℝ)) = Set.univ := by
      ext w
      simp [orthantProperCone]
    rw [huniv, interior_univ]
    trivial
  · have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨⟨0, Nat.pos_of_ne_zero hn⟩, Finset.mem_univ _⟩
    let ε : ℝ := (Finset.univ : Finset (Fin n)).inf' hne v
    have hε_pos : 0 < ε := (Finset.lt_inf'_iff hne).mpr fun i _ => hv i
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    refine ⟨ε, hε_pos, fun w hw i => ?_⟩
    have hdist : ‖w - v‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hcoord : |w i - v i| < ε := lt_of_le_of_lt (norm_le_pi_norm (w - v) i) hdist
    have hvi : ε ≤ v i := Finset.inf'_le v (Finset.mem_univ i)
    change 0 ≤ w i
    linarith [(abs_lt.mp hcoord).1, hvi]

/-- A point is interior to the finite-dimensional positive orthant exactly when every
coordinate is strictly positive. The forward direction is proved by perturbing one coordinate
inside an open ball; the reverse direction is `mem_interior_orthantProperCone_of_pos`. -/
theorem mem_interior_orthantProperCone_iff_pos {n : ℕ} {v : Fin n → ℝ} :
    v ∈ interior (orthantProperCone n : Set (Fin n → ℝ)) ↔ ∀ i : Fin n, 0 < v i := by
  constructor
  · intro hv i
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      (mem_interior_iff_mem_nhds.mp hv)
    let w : Fin n → ℝ := fun j => if j = i then v j - ε / 2 else v j
    have hdiff : w - v = Pi.single i (-ε / 2) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [w]
        ring
      · simp [w, hji]
    have hwball : ‖w - v‖ < ε := by
      rw [hdiff, Pi.norm_single, Real.norm_eq_abs, abs_of_neg (by linarith : -ε / 2 < 0)]
      linarith
    have hwC := hball hwball
    have hwi : 0 ≤ w i := hwC i
    have hvalue : w i = v i - ε / 2 := by simp [w]
    rw [hvalue] at hwi
    linarith
  · exact mem_interior_orthantProperCone_of_pos

/-- Coordinate formula for the upper order gauge on a strictly positive
finite-dimensional orthant. The finite supremum is the exact least scalar
`r` for which every coordinate of `x` is bounded by `r * y`. -/
def orthantUpperRatio {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sup' (by
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩) (fun i => x i / y i)

theorem upperGauge_orthant_eq_sup_ratio {n : ℕ} (hn : 0 < n)
    {x y : Fin n → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    upperGauge (orthantProperCone n) x y = orthantUpperRatio hn x y := by
  let R := orthantUpperRatio hn x y
  have hidx : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hRpos : 0 < R := by
    have hratio : 0 < x ⟨0, hn⟩ / y ⟨0, hn⟩ := div_pos (hx _) (hy _)
    exact lt_of_lt_of_le hratio (Finset.le_sup' (fun i => x i / y i) hidx)
  have hR_ge : ∀ i, x i / y i ≤ R := by
    intro i
    exact Finset.le_sup' (fun j => x j / y j) (Finset.mem_univ i)
  have hR_feasible : coneLE (orthantProperCone n) x (R • y) := by
    intro i
    change 0 ≤ R * y i - x i
    have hmul := (div_le_iff₀ (hy i)).mp (hR_ge i)
    nlinarith
  have hfeasible_nonempty :
      {r : ℝ | 0 ≤ r ∧ coneLE (orthantProperCone n) x (r • y)}.Nonempty :=
    ⟨R, hRpos.le, hR_feasible⟩
  have hR_le_feasible : ∀ r ∈
      {q : ℝ | 0 ≤ q ∧ coneLE (orthantProperCone n) x (q • y)}, R ≤ r := by
    intro r hr
    have hcoords := hr.2
    apply Finset.sup'_le
    intro i hi
    have hcoord : 0 ≤ r * y i - x i := by simpa [coneLE] using hcoords i
    have hratio : x i / y i ≤ r := (div_le_iff₀ (hy i)).mpr (by linarith)
    exact hratio
  have h_lower : R ≤ sInf
      {r : ℝ | 0 ≤ r ∧ coneLE (orthantProperCone n) x (r • y)} :=
    le_csInf hfeasible_nonempty hR_le_feasible
  have h_upper : sInf
      {r : ℝ | 0 ≤ r ∧ coneLE (orthantProperCone n) x (r • y)} ≤ R :=
    csInf_le ⟨0, fun r hr => hr.1⟩ ⟨hRpos.le, hR_feasible⟩
  change sInf {r : ℝ | 0 ≤ r ∧ coneLE (orthantProperCone n) x (r • y)} = R
  exact le_antisymm h_upper h_lower

/-- Exact finite-dimensional formula for Hilbert's projective metric on the
positive orthant: it is half the logarithm of the product of the two directed
coordinate-ratio suprema. -/
theorem birkhoffHilbertMetric_orthant_eq_log_sup_ratio {n : ℕ} (hn : 0 < n)
    {x y : Fin n → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    birkhoffHilbertMetric (orthantProperCone n) x y =
      (1 / 2 : ℝ) * Real.log (orthantUpperRatio hn x y * orthantUpperRatio hn y x) := by
  rw [birkhoffHilbertMetric, lowerGauge,
    upperGauge_orthant_eq_sup_ratio hn hx hy,
    upperGauge_orthant_eq_sup_ratio hn hy hx, div_inv_eq_mul]

/-- The orthant metric formula stated using the cone's intrinsic interior condition. Coordinate
positivity is derived from the proved characterization of the orthant interior. -/
theorem birkhoffHilbertMetric_orthant_eq_log_sup_ratio_of_interior {n : ℕ} (hn : 0 < n)
    {x y : Fin n → ℝ}
    (hx : x ∈ interior (orthantProperCone n : Set (Fin n → ℝ)))
    (hy : y ∈ interior (orthantProperCone n : Set (Fin n → ℝ))) :
    birkhoffHilbertMetric (orthantProperCone n) x y =
      (1 / 2 : ℝ) * Real.log (orthantUpperRatio hn x y * orthantUpperRatio hn y x) := by
  apply birkhoffHilbertMetric_orthant_eq_log_sup_ratio hn
    (mem_interior_orthantProperCone_iff_pos.mp hx)
    (mem_interior_orthantProperCone_iff_pos.mp hy)

theorem orthant2_chord_identity {τ_a τ_x τ_y τ_b : ℝ}
    (hax : τ_a < τ_x) (hxy : τ_x < τ_y) (hyb : τ_y < τ_b) :
    let u : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
    let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
    let p : ℝ → Fin 2 → ℝ := fun τ =>
      ((τ_b - τ) / (τ_b - τ_a)) • u + ((τ - τ_a) / (τ_b - τ_a)) • v
    birkhoffHilbertMetric (orthantProperCone 2) (p τ_x) (p τ_y) =
      (1 / 2 : ℝ) * Real.log (scalarCrossRatio τ_a τ_x τ_y τ_b) := by
  dsimp only
  let u : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
  let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
  have hu : u ∈ orthantProperCone 2 := fun i => by fin_cases i <;> simp [u]
  have hv : v ∈ orthantProperCone 2 := fun i => by fin_cases i <;> simp [v]
  have hsector : ∀ α β : ℝ, α • u + β • v ∈ orthantProperCone 2 → 0 ≤ α ∧ 0 ≤ β := by
    intro α β hmem
    have h0 := hmem 0
    have h1 := hmem 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, u, v, ↓reduceIte,
      Fin.reduceEq, mul_one, mul_zero, add_zero, zero_add] at h0 h1
    exact ⟨h0, h1⟩
  exact birkhoff_crossRatio_chord_identity (orthantProperCone 2) hu hv hsector hax hxy hyb

/-- Concrete positive strictly-contracting `2 × 2` matrix `posMatA = !![2, 1; 1, 2]`. -/
def posMatA : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]

/-- Companion noncommuting `2 × 2` shear matrix `posMatB = !![1, 2; 0, 1]`. -/
def posMatB : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 0, 1]

/-- Mandatory T17 noncommutativity ground witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem posMatA_mul_posMatB_ne : posMatA * posMatB ≠ posMatB * posMatA := by
  intro hEq
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hEq
  simp only [posMatA, posMatB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h00
  norm_num at h00

private lemma posMatA_pair_pos {w0 w1 : ℝ} (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hsum : 0 < w0 + w1) :
    0 < 2 * w0 + w1 ∧ 0 < w0 + 2 * w1 :=
  ⟨by linarith [hw0, hsum], by linarith [hw1, hsum]⟩

private lemma posMatA_ratio_pair_le (a0 a1 b0 b1 : ℝ)
    (ha0 : 0 < a0) (hb0 : 0 < b0) (hb1 : 0 < b1) :
    0 < max (a0 / b0) (a1 / b1) ∧
    a0 ≤ max (a0 / b0) (a1 / b1) * b0 ∧
    a1 ≤ max (a0 / b0) (a1 / b1) * b1 := by
  refine ⟨lt_max_of_lt_left (div_pos ha0 hb0), ?_, ?_⟩
  · have h : a0 / b0 ≤ max (a0 / b0) (a1 / b1) := le_max_left _ _
    exact (div_le_iff₀ hb0).mp h
  · have h : a1 / b1 ≤ max (a0 / b0) (a1 / b1) := le_max_right _ _
    exact (div_le_iff₀ hb1).mp h

private lemma posMatA_cross_ratio_le_four {a0 a1 b0 b1 : ℝ}
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (ha01 : a0 ≤ 2 * a1) (ha10 : a1 ≤ 2 * a0)
    (hb01 : b0 ≤ 2 * b1) (hb10 : b1 ≤ 2 * b0) :
    max (a0 / b0) (a1 / b1) * max (b0 / a0) (b1 / a1) ≤ 4 := by
  have h1 : (a0 / b0) * (b0 / a0) ≤ 4 := by
    have : (a0 / b0) * (b0 / a0) = 1 := by field_simp [ha0.ne', hb0.ne']
    linarith
  have h2 : (a0 / b0) * (b1 / a1) ≤ 4 := by
    have hr1 : a0 / a1 ≤ 2 := (div_le_iff₀ ha1).mpr ha01
    have hr2 : b1 / b0 ≤ 2 := (div_le_iff₀ hb0).mpr hb10
    have hid : (a0 / b0) * (b1 / a1) = (a0 / a1) * (b1 / b0) := by ring
    rw [hid]
    nlinarith [div_pos ha0 ha1, div_pos hb1 hb0]
  have h3 : (a1 / b1) * (b0 / a0) ≤ 4 := by
    have hr1 : a1 / a0 ≤ 2 := (div_le_iff₀ ha0).mpr ha10
    have hr2 : b0 / b1 ≤ 2 := (div_le_iff₀ hb1).mpr hb01
    have hid : (a1 / b1) * (b0 / a0) = (a1 / a0) * (b0 / b1) := by ring
    rw [hid]
    nlinarith [div_pos ha1 ha0, div_pos hb0 hb1]
  have h4 : (a1 / b1) * (b1 / a1) ≤ 4 := by
    have : (a1 / b1) * (b1 / a1) = 1 := by field_simp [ha1.ne', hb1.ne']
    linarith
  rcases le_total (a0 / b0) (a1 / b1) with hL | hL <;>
    rcases le_total (b0 / a0) (b1 / a1) with hR | hR <;>
    simp only [max_eq_right, max_eq_left, hL, hR]
  · exact h4
  · exact h3
  · exact h2
  · exact h1

private lemma posMatA_entry_bounds_scalar {u0 u1 : ℝ} (hu0 : 0 ≤ u0) (hu1 : 0 ≤ u1) :
    2 * u0 + u1 ≤ 2 * (u0 + 2 * u1) ∧ u0 + 2 * u1 ≤ 2 * (2 * u0 + u1) :=
  ⟨by linarith [hu1], by linarith [hu0]⟩

private lemma half_log_four_eq_log_two {M : ℝ} (hM : 0 < M) (hle : M ≤ 4) :
    (1 / 2 : ℝ) * Real.log M ≤ Real.log 2 := by
  have hlog : Real.log M ≤ Real.log (2 ^ 2) := by
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
    exact Real.log_le_log hM hle
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

private lemma tanh_half_log_two : Real.tanh (Real.log 2 / 2) = 1 / 3 := by
  rw [tanh_half_eq_exp_ratio, Real.exp_log (by norm_num)]
  norm_num

private lemma nonzero_orthant2_sum_pos {w0 w1 : ℝ} (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1)
    (hne : ¬ (w0 = 0 ∧ w1 = 0)) : 0 < w0 + w1 := by
  rcases eq_or_lt_of_le hw0 with h0 | h0
  · rcases eq_or_lt_of_le hw1 with h1 | h1
    · exfalso; exact hne ⟨h0.symm, h1.symm⟩
    · linarith
  · linarith

private lemma posMatA_mulVec_coords (w : Fin 2 → ℝ) :
    (posMatA.mulVecLin w) 0 = 2 * w 0 + w 1 ∧ (posMatA.mulVecLin w) 1 = w 0 + 2 * w 1 := by
  constructor <;>
    simp [posMatA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma posMatA_maps_nonzero_to_interior :
    ∀ w : Fin 2 → ℝ, w ∈ orthantProperCone 2 → w ≠ 0 →
      posMatA.mulVecLin w ∈ interior (orthantProperCone 2 : Set (Fin 2 → ℝ)) := by
  intro w hw hne
  apply mem_interior_orthantProperCone_of_pos
  have hnot : ¬ (w 0 = 0 ∧ w 1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hne
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have hpair := posMatA_pair_pos (hw 0) (hw 1) (nonzero_orthant2_sum_pos (hw 0) (hw 1) hnot)
  have hco := posMatA_mulVec_coords w
  intro i
  fin_cases i
  · change 0 < (posMatA.mulVecLin w) 0; rw [hco.1]; exact hpair.1
  · change 0 < (posMatA.mulVecLin w) 1; rw [hco.2]; exact hpair.2

private lemma posMatA_projective_diam_le_log_two :
    ∀ u v : Fin 2 → ℝ, u ∈ orthantProperCone 2 → u ≠ 0 →
      v ∈ orthantProperCone 2 → v ≠ 0 →
      birkhoffHilbertMetric (orthantProperCone 2) (posMatA.mulVecLin u) (posMatA.mulVecLin v) ≤
        Real.log 2 := by
  intro u v hu hu_ne hv hv_ne
  have ha_int := posMatA_maps_nonzero_to_interior u hu hu_ne
  have hb_int := posMatA_maps_nonzero_to_interior v hv hv_ne
  have hco_u := posMatA_mulVec_coords u
  have hco_v := posMatA_mulVec_coords v
  have ha0 : 0 < (posMatA.mulVecLin u) 0 := by
    have hnot : ¬ (u 0 = 0 ∧ u 1 = 0) := fun ⟨h0, h1⟩ => hu_ne (by funext i; fin_cases i <;> assumption)
    rw [hco_u.1]
    exact (posMatA_pair_pos (hu 0) (hu 1) (nonzero_orthant2_sum_pos (hu 0) (hu 1) hnot)).1
  have ha1 : 0 < (posMatA.mulVecLin u) 1 := by
    have hnot : ¬ (u 0 = 0 ∧ u 1 = 0) := fun ⟨h0, h1⟩ => hu_ne (by funext i; fin_cases i <;> assumption)
    rw [hco_u.2]
    exact (posMatA_pair_pos (hu 0) (hu 1) (nonzero_orthant2_sum_pos (hu 0) (hu 1) hnot)).2
  have hb0 : 0 < (posMatA.mulVecLin v) 0 := by
    have hnot : ¬ (v 0 = 0 ∧ v 1 = 0) := fun ⟨h0, h1⟩ => hv_ne (by funext i; fin_cases i <;> assumption)
    rw [hco_v.1]
    exact (posMatA_pair_pos (hv 0) (hv 1) (nonzero_orthant2_sum_pos (hv 0) (hv 1) hnot)).1
  have hb1 : 0 < (posMatA.mulVecLin v) 1 := by
    have hnot : ¬ (v 0 = 0 ∧ v 1 = 0) := fun ⟨h0, h1⟩ => hv_ne (by funext i; fin_cases i <;> assumption)
    rw [hco_v.2]
    exact (posMatA_pair_pos (hv 0) (hv 1) (nonzero_orthant2_sum_pos (hv 0) (hv 1) hnot)).2
  have hMab_pos : 0 < upperGauge (orthantProperCone 2) (posMatA.mulVecLin u) (posMatA.mulVecLin v) :=
    upperGauge_pos_of_mem_interior (orthantProperCone 2) (orthantProperCone_salient 2) ha_int hb_int
  have hMba_pos : 0 < upperGauge (orthantProperCone 2) (posMatA.mulVecLin v) (posMatA.mulVecLin u) :=
    upperGauge_pos_of_mem_interior (orthantProperCone 2) (orthantProperCone_salient 2) hb_int ha_int
  have hpr1 := posMatA_ratio_pair_le
    ((posMatA.mulVecLin u) 0) ((posMatA.mulVecLin u) 1)
    ((posMatA.mulVecLin v) 0) ((posMatA.mulVecLin v) 1) ha0 hb0 hb1
  have hpr2 := posMatA_ratio_pair_le
    ((posMatA.mulVecLin v) 0) ((posMatA.mulVecLin v) 1)
    ((posMatA.mulVecLin u) 0) ((posMatA.mulVecLin u) 1) hb0 ha0 ha1
  have hub1 : upperGauge (orthantProperCone 2) (posMatA.mulVecLin u) (posMatA.mulVecLin v) ≤
      max ((posMatA.mulVecLin u) 0 / (posMatA.mulVecLin v) 0)
        ((posMatA.mulVecLin u) 1 / (posMatA.mulVecLin v) 1) := by
    apply upperGauge_le_of_feasible (orthantProperCone 2) (posMatA.mulVecLin u) (posMatA.mulVecLin v)
    refine ⟨hpr1.1.le, fun i => ?_⟩
    fin_cases i <;> dsimp
    · exact sub_nonneg.mpr hpr1.2.1
    · exact sub_nonneg.mpr hpr1.2.2
  have hub2 : upperGauge (orthantProperCone 2) (posMatA.mulVecLin v) (posMatA.mulVecLin u) ≤
      max ((posMatA.mulVecLin v) 0 / (posMatA.mulVecLin u) 0)
        ((posMatA.mulVecLin v) 1 / (posMatA.mulVecLin u) 1) := by
    apply upperGauge_le_of_feasible (orthantProperCone 2) (posMatA.mulVecLin v) (posMatA.mulVecLin u)
    refine ⟨hpr2.1.le, fun i => ?_⟩
    fin_cases i <;> dsimp
    · exact sub_nonneg.mpr hpr2.2.1
    · exact sub_nonneg.mpr hpr2.2.2
  have ha_eb := posMatA_entry_bounds_scalar (hu 0) (hu 1)
  have hb_eb := posMatA_entry_bounds_scalar (hv 0) (hv 1)
  have ha01 : (posMatA.mulVecLin u) 0 ≤ 2 * (posMatA.mulVecLin u) 1 := by
    rw [hco_u.1, hco_u.2]; exact ha_eb.1
  have ha10 : (posMatA.mulVecLin u) 1 ≤ 2 * (posMatA.mulVecLin u) 0 := by
    rw [hco_u.1, hco_u.2]; exact ha_eb.2
  have hb01 : (posMatA.mulVecLin v) 0 ≤ 2 * (posMatA.mulVecLin v) 1 := by
    rw [hco_v.1, hco_v.2]; exact hb_eb.1
  have hb10 : (posMatA.mulVecLin v) 1 ≤ 2 * (posMatA.mulVecLin v) 0 := by
    rw [hco_v.1, hco_v.2]; exact hb_eb.2
  have hcross4 := posMatA_cross_ratio_le_four ha0 ha1 hb0 hb1 ha01 ha10 hb01 hb10
  have hprod_le :
      upperGauge (orthantProperCone 2) (posMatA.mulVecLin u) (posMatA.mulVecLin v) *
        upperGauge (orthantProperCone 2) (posMatA.mulVecLin v) (posMatA.mulVecLin u) ≤ 4 :=
    (mul_le_mul hub1 hub2 hMba_pos.le hpr1.1.le).trans hcross4
  rw [birkhoffHilbertMetric_eq_half_hilbertOrderDistance, hilbertOrderDistance]
  exact half_log_four_eq_log_two (mul_pos hMab_pos hMba_pos) hprod_le

theorem posMatA_contraction_one_third {x y : Fin 2 → ℝ}
    (hx : ∀ i : Fin 2, 0 < x i) (hy : ∀ i : Fin 2, 0 < y i) :
    birkhoffHilbertMetric (orthantProperCone 2) (posMatA.mulVec x) (posMatA.mulVec y) ≤
      (1 / 3 : ℝ) * birkhoffHilbertMetric (orthantProperCone 2) x y := by
  have hΔ : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hthm := birkhoff_contraction_theorem
    (orthantProperCone 2) (orthantProperCone 2)
    (orthantProperCone_salient 2) (orthantProperCone_salient 2)
    posMatA.mulVecLin posMatA_maps_nonzero_to_interior hΔ posMatA_projective_diam_le_log_two
    (mem_interior_orthantProperCone_of_pos hx) (mem_interior_orthantProperCone_of_pos hy)
  rw [tanh_half_log_two] at hthm
  exact hthm

/-! ## Section 6: Master Synthesis & QMS Archetype Registration -/

def BirkhoffHilbertConeMetricSynthesis : Prop :=
  (posMatA * posMatB ≠ posMatB * posMatA) ∧
  (¬ (⊤ : ProperCone ℝ ℝ).toPointedCone.toConvexCone.Salient) ∧
  (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (C : ProperCone ℝ E) (_hC : C.toPointedCone.toConvexCone.Salient)
    (x y : E) (_hx : x ∈ interior (C : Set E)) (_hy : y ∈ interior (C : Set E)),
    birkhoffHilbertMetric C x y = 0 ↔ ∃ c : ℝ, 0 < c ∧ x = c • y) ∧
  (∀ (τ_a τ_x τ_y τ_b : ℝ), τ_a < τ_x → τ_x < τ_y → τ_y < τ_b →
    let u : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
    let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
    let p : ℝ → Fin 2 → ℝ := fun τ =>
      ((τ_b - τ) / (τ_b - τ_a)) • u + ((τ - τ_a) / (τ_b - τ_a)) • v
    birkhoffHilbertMetric (orthantProperCone 2) (p τ_x) (p τ_y) =
      (1 / 2 : ℝ) * Real.log (scalarCrossRatio τ_a τ_x τ_y τ_b)) ∧
  (∀ (x y : Fin 2 → ℝ), (∀ i : Fin 2, 0 < x i) → (∀ i : Fin 2, 0 < y i) →
    birkhoffHilbertMetric (orthantProperCone 2) (posMatA.mulVec x) (posMatA.mulVec y) ≤
      (1 / 3 : ℝ) * birkhoffHilbertMetric (orthantProperCone 2) x y)

theorem birkhoff_hilbert_cone_metric_synthesis :
    BirkhoffHilbertConeMetricSynthesis := by
  refine ⟨posMatA_mul_posMatB_ne, topProperCone_not_salient, ?_, ?_, ?_⟩
  · intro E _ _ _ C hC x y hx hy
    exact birkhoffHilbertMetric_eq_zero_iff_same_ray C hC hx hy
  · intro τ_a τ_x τ_y τ_b hax hxy hyb
    exact orthant2_chord_identity hax hxy hyb
  · intro x y hx hy
    exact posMatA_contraction_one_third hx hy

def birkhoffHilbertConeMetricArchetype : TypedArchetype Unit .proved where
  name := `InfoGeometry.Erlangen.BirkhoffHilbertConeMetric.birkhoff_hilbert_cone_metric_synthesis
  phase := 5
  claim := fun _ => BirkhoffHilbertConeMetricSynthesis
  evidence := fun _ => birkhoff_hilbert_cone_metric_synthesis

#register_archetype birkhoffHilbertConeMetricArchetype
#audit_archetype birkhoffHilbertConeMetricArchetype

end InfoGeometry.Erlangen.BirkhoffHilbertConeMetric
