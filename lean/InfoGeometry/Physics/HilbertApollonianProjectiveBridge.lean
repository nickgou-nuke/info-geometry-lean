import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Hilbert-Apollonian Projective Metric & Cross-Ratio Bridge

Formalizing the deep synthesis between:
1. **Hilbert Projective Metric on Positive Cones**:
   On the positive cone $\mathbb{R}_{>0}^2$, the projective distance is:
   $$d_H(\mathbf{x}, \mathbf{y}) = \ln \left( \frac{\max(x_1/y_1, x_2/y_2)}{\min(x_1/y_1, x_2/y_2)} \right)$$
   satisfying projective ray scale invariance: $d_H(c_1 \mathbf{x}, c_2 \mathbf{y}) = d_H(\mathbf{x}, \mathbf{y})$
   for all $c_1, c_2 > 0$.

2. **Apollonian Cross-Ratio Metric on the Simplex $\Delta^1$**:
   Restricting to the normalized simplex $\mathbf{p} = (p, 1-p)$ and $\mathbf{q} = (q, 1-q)$:
   The cross-ratio with respect to the boundary points $\{0, 1\}$ is:
   $$\mathrm{cr}(p, q) = \frac{p(1-q)}{q(1-p)} = \frac{p/(1-p)}{q/(1-q)}$$
   Taking the logarithm recovers the log-odds difference:
   $$\ln \mathrm{cr}(p, q) = \operatorname{logit}(p) - \operatorname{logit}(q)$$
   whose absolute value equals the Hilbert projective distance:
   $$d_H(\mathbf{p}, \mathbf{q}) = |\operatorname{logit}(p) - \operatorname{logit}(q)| = d_{\mathrm{Apol}}(p, q)$$

3. **Relativistic Rapidity Duality**:
   With rapidity $\theta(p) = \frac{1}{2}\operatorname{logit}(p)$:
   $$d_{\mathrm{Apol}}(p, q) = 2 |\theta(p) - \theta(q)|$$
   invariant under Lorentz rapidity boosts $\theta \mapsto \theta + \Delta$.

4. **The Jaynesian Neutral Throat & Reflection Symmetry**:
   At the uniform maximum entropy prior $p_{\mathrm{Jaynes}} = 1/2$ (the Klein bottle throat):
   $$\operatorname{logit}(1/2) = 0, \quad \theta(1/2) = 0$$
   $$d_{\mathrm{Apol}}(p, 1/2) = |\operatorname{logit}(p)| = 2|\theta(p)|$$
   Under the glide reflection / time-reversal involution $p \mapsto 1 - p$:
   $$d_{\mathrm{Apol}}(1 - p, 1/2) = d_{\mathrm{Apol}}(p, 1/2)$$

5. **Asymptotic Lightcone Horizon**:
   For any distance bound $M > 0$, deterministic certainty is unreachable at finite distance:
   there exists $p \in (0, 1)$ such that $d_{\mathrm{Apol}}(p, 1/2) > M$,
   establishing that the boundary $\partial \Delta^1 = \{0, 1\}$ is an infinite horizon,
   identical to the speed of light $c$ at $\theta \to \infty$.

All proofs verified constructively in Lean 4 with Mathlib (0 `sorry`, 0 `admit`).
-/

open Set

noncomputable section

namespace InfoGeometry.Physics.HilbertApollonianProjectiveBridge

/-! ### 1. The Positive Ray Cone and Hilbert Projective Distance in 2D -/

/-- Maximum coordinate ratio between two positive pairs. -/
def maxRatio (x y : ℝ × ℝ) : ℝ :=
  max (x.1 / y.1) (x.2 / y.2)

/-- Minimum coordinate ratio between two positive pairs. -/
def minRatio (x y : ℝ × ℝ) : ℝ :=
  min (x.1 / y.1) (x.2 / y.2)

/-- The Hilbert projective distance on the positive quadrant $\mathbb{R}_{>0}^2$:
    $$d_H(\mathbf{x}, \mathbf{y}) = \ln \left( \frac{\max(x_1/y_1, x_2/y_2)}{\min(x_1/y_1, x_2/y_2)} \right)$$ -/
def hilbertDist (x y : ℝ × ℝ) : ℝ :=
  Real.log (maxRatio x y / minRatio x y)

/-- Coordinate-wise scaling preserves ratio quotients:
    $\frac{c_1 x_i}{c_2 y_i} = \frac{c_1}{c_2} \frac{x_i}{y_i}$. -/
theorem scaled_ratio (x y : ℝ × ℝ) (c1 c2 : ℝ) :
    (c1 * x.1) / (c2 * y.1) = (c1 / c2) * (x.1 / y.1) ∧
    (c1 * x.2) / (c2 * y.2) = (c1 / c2) * (x.2 / y.2) := by
  constructor <;> ring

/-- Positive scalar multiplication scales the maximum ratio. -/
theorem maxRatio_scale (x y : ℝ × ℝ) (c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2) :
    maxRatio (c1 * x.1, c1 * x.2) (c2 * y.1, c2 * y.2) = (c1 / c2) * maxRatio x y := by
  dsimp [maxRatio]
  obtain ⟨h1, h2⟩ := scaled_ratio x y c1 c2
  rw [h1, h2]
  have h_c_pos : 0 ≤ c1 / c2 := div_nonneg (le_of_lt hc1) (le_of_lt hc2)
  exact (mul_max_of_nonneg (x.1 / y.1) (x.2 / y.2) h_c_pos).symm

/-- Positive scalar multiplication scales the minimum ratio. -/
theorem minRatio_scale (x y : ℝ × ℝ) (c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2) :
    minRatio (c1 * x.1, c1 * x.2) (c2 * y.1, c2 * y.2) = (c1 / c2) * minRatio x y := by
  dsimp [minRatio]
  obtain ⟨h1, h2⟩ := scaled_ratio x y c1 c2
  rw [h1, h2]
  have h_c_pos : 0 ≤ c1 / c2 := div_nonneg (le_of_lt hc1) (le_of_lt hc2)
  exact (mul_min_of_nonneg (x.1 / y.1) (x.2 / y.2) h_c_pos).symm

/-- 🏆 THEOREM 1: Projective Ray Scale Invariance of the Hilbert Metric.
    Scaling the vectors by arbitrary positive scalars leaves the Hilbert distance unchanged:
    $$d_H(c_1 \mathbf{x}, c_2 \mathbf{y}) = d_H(\mathbf{x}, \mathbf{y})$$ -/
theorem hilbert_scale_invariant (x y : ℝ × ℝ) (c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    hilbertDist (c1 * x.1, c1 * x.2) (c2 * y.1, c2 * y.2) = hilbertDist x y := by
  dsimp [hilbertDist]
  rw [maxRatio_scale x y c1 c2 hc1 hc2]
  rw [minRatio_scale x y c1 c2 hc1 hc2]
  have hc_pos : 0 < c1 / c2 := div_pos hc1 hc2
  have hc_ne : c1 / c2 ≠ 0 := ne_of_gt hc_pos
  have h_cancel : ((c1 / c2) * maxRatio x y) / ((c1 / c2) * minRatio x y) =
      maxRatio x y / minRatio x y := by
    rw [mul_div_mul_left _ _ hc_ne]
  rw [h_cancel]

/-! ### 2. Reduction to Binary Simplex & Apollonian Cross-Ratio -/

/-- Log-odds function on the unit interval $(0, 1)$. -/
def logit (p : ℝ) : ℝ := Real.log (p / (1 - p))

/-- Apollonian cross-ratio metric between two probabilities:
    $$d_{\mathrm{Apol}}(p, q) = |\operatorname{logit}(p) - \operatorname{logit}(q)|$$ -/
def apollonianMetric (p q : ℝ) : ℝ := |logit p - logit q|

/-- Relativistic rapidity coordinate: $\theta(p) = \frac{1}{2} \operatorname{logit}(p)$. -/
def rapidity (p : ℝ) : ℝ := (1 / 2) * logit p

/-- Odds ratio is strictly positive on $(0, 1)$. -/
theorem odds_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < p / (1 - p) := by
  have h1 : 0 < 1 - p := by linarith
  exact div_pos hp0 h1

/-- 🏆 THEOREM 2: Cross-Ratio Algebraic Factorization.
    $$\frac{p(1 - q)}{q(1 - p)} = \frac{p / (1 - p)}{q / (1 - q)}$$ -/
theorem cross_ratio_factorization {p q : ℝ}
    (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    (p * (1 - q)) / (q * (1 - p)) = (p / (1 - p)) / (q / (1 - q)) := by
  have hp_den : 1 - p ≠ 0 := by linarith
  have hq_den : 1 - q ≠ 0 := by linarith
  have hq_nz : q ≠ 0 := by linarith
  field_simp

/-- 🏆 THEOREM 3: Logarithm of the Cross-Ratio is the Log-Odds Difference.
    $$\ln \left( \frac{p(1-q)}{q(1-p)} \right) = \operatorname{logit}(p) - \operatorname{logit}(q)$$ -/
theorem log_cross_ratio {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    Real.log ((p * (1 - q)) / (q * (1 - p))) = logit p - logit q := by
  have hp_odds : 0 < p / (1 - p) := odds_pos hp0 hp1
  have hq_odds : 0 < q / (1 - q) := odds_pos hq0 hq1
  rw [cross_ratio_factorization hp1 hq0 hq1]
  rw [Real.log_div (ne_of_gt hp_odds) (ne_of_gt hq_odds)]
  rfl

/-- 🏆 THEOREM 4: 2D Hilbert Projective Distance equals Apollonian Metric on $\Delta^1$.
    When $p \ge q$, the maximum ratio is $p/q$ and minimum is $(1-p)/(1-q)$,
    recovering the exact cross-ratio logarithm. -/
theorem hilbert_dist_eq_apollonian_of_ge {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) (hpq : q ≤ p) :
    hilbertDist (p, 1 - p) (q, 1 - q) = apollonianMetric p q := by
  have hp_odds : 0 < p / (1 - p) := odds_pos hp0 hp1
  have hq_odds : 0 < q / (1 - q) := odds_pos hq0 hq1
  have h1mp : 0 < 1 - p := by linarith
  have h1mq : 0 < 1 - q := by linarith
  have h_pq_ratio : (1 - p) / (1 - q) ≤ p / q := by
    rw [div_le_div_iff₀ h1mq hq0]
    have h_sub : (1 - p) * q ≤ p * (1 - q) := by
      calc (1 - p) * q = q - p * q := by ring
      _ ≤ p - p * q := by linarith
      _ = p * (1 - q) := by ring
    exact h_sub
  dsimp [hilbertDist, maxRatio, minRatio]
  rw [max_eq_left h_pq_ratio]
  rw [min_eq_right h_pq_ratio]
  have h_quot : (p / q) / ((1 - p) / (1 - q)) = (p * (1 - q)) / (q * (1 - p)) := by
    have hq_nz : q ≠ 0 := ne_of_gt hq0
    have h1mp_nz : 1 - p ≠ 0 := ne_of_gt h1mp
    have h1mq_nz : 1 - q ≠ 0 := ne_of_gt h1mq
    field_simp
  rw [h_quot]
  rw [log_cross_ratio hp0 hp1 hq0 hq1]
  dsimp [apollonianMetric]
  have h_odds_le : q / (1 - q) ≤ p / (1 - p) := by
    rw [div_le_div_iff₀ h1mq h1mp]
    calc q * (1 - p) = q - q * p := by ring
    _ ≤ p - q * p := by linarith
    _ = p * (1 - q) := by ring
  have h_log_le : logit q ≤ logit p := by
    dsimp [logit]
    exact (Real.log_le_log_iff hq_odds hp_odds).mpr h_odds_le
  rw [abs_of_nonneg (by linarith)]

/-! ### 3. Metric Axioms on the Simplex -/

/-- 🏆 THEOREM 5: Non-negativity of the Apollonian metric. -/
theorem apollonian_nonneg (p q : ℝ) : 0 ≤ apollonianMetric p q :=
  abs_nonneg _

/-- 🏆 THEOREM 6: Reflexivity / Self-distance is zero. -/
theorem apollonian_self (p : ℝ) : apollonianMetric p p = 0 := by
  dsimp [apollonianMetric]
  simp

/-- 🏆 THEOREM 7: Symmetry of the Apollonian metric. -/
theorem apollonian_symm (p q : ℝ) : apollonianMetric p q = apollonianMetric q p := by
  dsimp [apollonianMetric]
  exact abs_sub_comm _ _

/-- 🏆 THEOREM 8: Triangle Inequality for the Apollonian metric. -/
theorem apollonian_triangle (p q r : ℝ) :
    apollonianMetric p r ≤ apollonianMetric p q + apollonianMetric q r := by
  dsimp [apollonianMetric]
  exact abs_sub_le (logit p) (logit q) (logit r)

/-- Injectivity of the logit map on $(0, 1)$. -/
theorem logit_injective {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) (h : logit p = logit q) : p = q := by
  dsimp [logit] at h
  have hp_odds : 0 < p / (1 - p) := odds_pos hp0 hp1
  have hq_odds : 0 < q / (1 - q) := odds_pos hq0 hq1
  have h_exp := congrArg Real.exp h
  rw [Real.exp_log hp_odds, Real.exp_log hq_odds] at h_exp
  have hp_den : 1 - p ≠ 0 := by linarith
  have hq_den : 1 - q ≠ 0 := by linarith
  have h_cross : p * (1 - q) = q * (1 - p) := by
    exact (div_eq_div_iff hp_den hq_den).mp h_exp
  linarith

/-- 🏆 THEOREM 9: Definiteness / Identity of Indiscernibles:
    $d_{\mathrm{Apol}}(p, q) = 0 \iff p = q$. -/
theorem apollonian_eq_zero_iff {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    apollonianMetric p q = 0 ↔ p = q := by
  constructor
  · intro h
    dsimp [apollonianMetric] at h
    rw [abs_eq_zero, sub_eq_zero] at h
    exact logit_injective hp0 hp1 hq0 hq1 h
  · intro h
    rw [h, apollonian_self]

/-! ### 4. Relativistic Rapidity Duality & Lorentz Invariance -/

/-- 🏆 THEOREM 10: Apollonian distance is exactly twice the rapidity distance:
    $$d_{\mathrm{Apol}}(p, q) = 2 |\theta(p) - \theta(q)|$$ -/
theorem apollonian_eq_two_mul_rapidity_diff (p q : ℝ) :
    apollonianMetric p q = 2 * |rapidity p - rapidity q| := by
  dsimp [apollonianMetric, rapidity]
  have h : (1/2 : ℝ) * logit p - (1/2) * logit q = (1/2) * (logit p - logit q) := by ring
  rw [h, abs_mul]
  have h2 : |(1/2 : ℝ)| = 1/2 := by norm_num
  rw [h2]
  ring

/-- 🏆 THEOREM 11: Lorentz Rapidity Boost Invariance.
    Hyperbolic translation $\theta \mapsto \theta + \Delta$ preserves the Apollonian distance:
    $$2 |(\theta_p + \Delta) - (\theta_q + \Delta)| = d_{\mathrm{Apol}}(p, q)$$ -/
theorem apollonian_boost_invariance (p q : ℝ) (Δ : ℝ) :
    2 * |(rapidity p + Δ) - (rapidity q + Δ)| = apollonianMetric p q := by
  have h : (rapidity p + Δ) - (rapidity q + Δ) = rapidity p - rapidity q := by ring
  rw [h, ← apollonian_eq_two_mul_rapidity_diff]

/-! ### 5. The Jaynesian Neutral Throat & Reflection Symmetry -/

/-- Logit of the Jaynesian prior $p_{\mathrm{Jaynes}} = 1/2$ vanishes. -/
theorem logit_half : logit (1/2) = 0 := by
  dsimp [logit]
  have h : (1/2 : ℝ) / (1 - 1/2) = 1 := by norm_num
  rw [h, Real.log_one]

/-- Relativistic rapidity vanishes at the Jaynesian prior: $\theta(1/2) = 0$. -/
theorem rapidity_half : rapidity (1/2) = 0 := by
  dsimp [rapidity]
  rw [logit_half, mul_zero]

/-- 🏆 THEOREM 12: Distance to the Jaynesian throat recovers the log-odds magnitude:
    $$d_{\mathrm{Apol}}(p, 1/2) = |\operatorname{logit}(p)| = 2 |\theta(p)|$$ -/
theorem apollonian_dist_to_jaynesian (p : ℝ) :
    apollonianMetric p (1/2) = |logit p| := by
  dsimp [apollonianMetric]
  rw [logit_half, sub_zero]

/-- Logit reflection under glide flip $p \mapsto 1 - p$:
    $$\operatorname{logit}(1 - p) = -\operatorname{logit}(p)$$ -/
theorem logit_reflection {p : ℝ} :
    logit (1 - p) = - logit p := by
  dsimp [logit]
  have h_id : (1 - p) / (1 - (1 - p)) = (p / (1 - p))⁻¹ := by
    have h_sub : 1 - (1 - p) = p := by ring
    rw [h_sub, inv_div]
  rw [h_id, Real.log_inv]

/-- 🏆 THEOREM 13: Parity / Reflection Symmetry across the Throat:
    $$d_{\mathrm{Apol}}(1 - p, 1/2) = d_{\mathrm{Apol}}(p, 1/2)$$ -/
theorem apollonian_throat_reflection (p : ℝ) :
    apollonianMetric (1 - p) (1/2) = apollonianMetric p (1/2) := by
  rw [apollonian_dist_to_jaynesian, apollonian_dist_to_jaynesian]
  rw [logit_reflection]
  exact abs_neg (logit p)

/-! ### 6. Asymptotic Lightcone Horizon Divergence -/

/-- The logistic sigmoid squashing map. -/
def sigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

theorem sigmoid_pos (x : ℝ) : 0 < sigmoid x := by
  dsimp [sigmoid]
  have h : 0 < 1 + Real.exp (-x) := by linarith [Real.exp_pos (-x)]
  exact div_pos zero_lt_one h

theorem sigmoid_lt_one (x : ℝ) : sigmoid x < 1 := by
  dsimp [sigmoid]
  have h : 1 < 1 + Real.exp (-x) := by linarith [Real.exp_pos (-x)]
  exact (div_lt_one (by linarith [Real.exp_pos (-x)])).mpr h

theorem logit_sigmoid (x : ℝ) : logit (sigmoid x) = x := by
  dsimp [logit, sigmoid]
  have hexp_pos : 0 < Real.exp (-x) := Real.exp_pos (-x)
  have hden_pos : 0 < 1 + Real.exp (-x) := by linarith
  have hden_ne : 1 + Real.exp (-x) ≠ 0 := ne_of_gt hden_pos
  have hexp_ne : Real.exp (-x) ≠ 0 := ne_of_gt hexp_pos
  have h_one_sub : 1 - 1 / (1 + Real.exp (-x)) = Real.exp (-x) / (1 + Real.exp (-x)) := by
    field_simp [hden_ne]
    ring
  rw [h_one_sub]
  have h_quot : (1 / (1 + Real.exp (-x))) / (Real.exp (-x) / (1 + Real.exp (-x))) =
      1 / Real.exp (-x) := by
    field_simp
  rw [h_quot, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]

/-- 🏆 THEOREM 14: Asymptotic Lightcone Horizon Divergence.
    For any positive target bound $M > 0$, the sigmoid state $p = \sigma(M + 1)$
    lies in $(0, 1)$ and has distance from the Jaynesian throat exceeding $M$. -/
theorem apollonian_boundary_divergence (M : ℝ) (hM : 0 < M) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ M < apollonianMetric p (1/2) := by
  let p := sigmoid (M + 1)
  have hp0 : 0 < p := sigmoid_pos (M + 1)
  have hp1 : p < 1 := sigmoid_lt_one (M + 1)
  use p
  refine ⟨hp0, hp1, ?_⟩
  rw [apollonian_dist_to_jaynesian]
  have h_log : logit p = M + 1 := logit_sigmoid (M + 1)
  rw [h_log]
  have h_pos : 0 ≤ M + 1 := by linarith
  rw [abs_of_nonneg h_pos]
  linarith

/-! ### 7. Master Certified Synthesis -/

/-- Certified conjunction of the Hilbert-Apollonian Projective Metric Bridge. -/
def certified_hilbert_apollonian_projective_synthesis : Prop :=
  -- 1. Projective Ray Scale Invariance
  (∀ (x y : ℝ × ℝ) (c1 c2 : ℝ),
    0 < c1 → 0 < c2 →
    hilbertDist (c1 * x.1, c1 * x.2) (c2 * y.1, c2 * y.2) = hilbertDist x y) ∧
  -- 2. Log-Cross-Ratio Identification
  (∀ (p q : ℝ), 0 < p → p < 1 → 0 < q → q < 1 →
    Real.log ((p * (1 - q)) / (q * (1 - p))) = logit p - logit q) ∧
  -- 3. Metric Axioms: nonneg, self, symm, triangle, separation
  (∀ (p q : ℝ), 0 ≤ apollonianMetric p q) ∧
  (∀ (p : ℝ), apollonianMetric p p = 0) ∧
  (∀ (p q : ℝ), apollonianMetric p q = apollonianMetric q p) ∧
  (∀ (p q r : ℝ), apollonianMetric p r ≤ apollonianMetric p q + apollonianMetric q r) ∧
  (∀ (p q : ℝ), 0 < p → p < 1 → 0 < q → q < 1 → (apollonianMetric p q = 0 ↔ p = q)) ∧
  -- 4. Rapidity Duality & Boost Invariance
  (∀ (p q : ℝ), apollonianMetric p q = 2 * |rapidity p - rapidity q|) ∧
  (∀ (p q : ℝ) (Δ : ℝ), 2 * |(rapidity p + Δ) - (rapidity q + Δ)| = apollonianMetric p q) ∧
  -- 5. Jaynesian Throat Origin & Parity Invariance
  (logit (1/2) = 0 ∧ rapidity (1/2) = 0) ∧
  (∀ (p : ℝ), apollonianMetric (1 - p) (1/2) = apollonianMetric p (1/2)) ∧
  -- 6. Boundary Horizon Divergence
  (∀ (M : ℝ), 0 < M → ∃ p : ℝ, 0 < p ∧ p < 1 ∧ M < apollonianMetric p (1/2))

/-- 🏆 MASTER THEOREM: Formal certification of the Hilbert-Apollonian synthesis. -/
theorem hilbert_apollonian_projective_synthesis :
    certified_hilbert_apollonian_projective_synthesis := by
  refine ⟨hilbert_scale_invariant,
          fun p q hp0 hp1 hq0 hq1 => log_cross_ratio hp0 hp1 hq0 hq1,
          apollonian_nonneg,
          apollonian_self,
          apollonian_symm,
          apollonian_triangle,
          fun p q hp0 hp1 hq0 hq1 => apollonian_eq_zero_iff hp0 hp1 hq0 hq1,
          apollonian_eq_two_mul_rapidity_diff,
          apollonian_boost_invariance,
          ⟨logit_half, rapidity_half⟩,
          fun p => apollonian_throat_reflection p,
          apollonian_boundary_divergence⟩

end InfoGeometry.Physics.HilbertApollonianProjectiveBridge
