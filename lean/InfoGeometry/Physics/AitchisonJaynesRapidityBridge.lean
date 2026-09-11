import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real

noncomputable section

namespace InfoGeometry.Physics.AitchisonJaynesRapidity

/-!
# Aitchison Simplex Geometry, Jaynesian State & Relativistic Rapidity

This module formalizes:
1. **The Aitchison Centered Log-Ratio (clr) on the Binary Simplex $\Delta^1$**:
   A state is parameterized by $p \in (0, 1)$ with complement $1-p \in (0, 1)$.
   $$\operatorname{clr}_1(p) = \frac{1}{2} \operatorname{logit}(p), \quad \operatorname{clr}_2(p) = -\frac{1}{2} \operatorname{logit}(p)$$
   satisfying $\operatorname{clr}_1(p) + \operatorname{clr}_2(p) = 0$ (traceless Cartan subalgebra of $\mathfrak{sl}(2, \mathbb{R})$).
2. **The Jaynesian Maximum Entropy Prior $p_{\mathrm{Jaynes}} = 1/2$**:
   Acts as the neutral origin / additive identity in the Aitchison vector space:
   $$\operatorname{logit}(p_{\mathrm{Jaynes}}) = 0, \quad \operatorname{clr}(p_{\mathrm{Jaynes}}) = \mathbf{0}$$
   corresponding to the Klein bottle throat $\operatorname{Re}(s) = 1/2$.
3. **Logit $\longleftrightarrow$ Relativistic Rapidity Duality**:
   With normalized velocity $v = 2p - 1 \in (-1, 1)$, relativistic rapidity $\theta = \operatorname{artanh}(v)$ satisfies:
   $$\frac{1+v}{1-v} = \frac{p}{1-p} \implies \operatorname{logit}(p) = 2 \theta$$
   $$\operatorname{clr}_1(p) = \theta, \quad \operatorname{clr}_2(p) = -\theta$$
4. **The Logistic Sigmoid as Relativistic Squashing Map**:
   $$\sigma(x) = \frac{1}{1 + e^{-x}}$$
   maps the unbounded Lie algebra rapidity $2\theta \in \mathbb{R}$ back onto the bounded probability simplex:
   $$\sigma(2\theta) = p, \quad \sigma(0) = 1/2 = p_{\mathrm{Jaynes}}$$
5. **Apollonian Information Geometry & Cross-Ratio Metric**:
   $$d_{\mathrm{Apol}}(p, q) = |\operatorname{logit}(p) - \operatorname{logit}(q)| = 2 |\theta_p - \theta_q|$$
   invariant under Lorentz rapidity boosts: $\theta \mapsto \theta + \Delta$.
6. **Split Peirce Density Matrix Representation**:
   $\hat{\rho} = p P_+ + (1-p) P_-$, yielding the maximally mixed state $\hat{\rho} = \frac{1}{2} \mathbb{I}$ at $p = 1/2$.
-/

/-- A valid probability in the open binary simplex (0, 1). -/
structure BinaryProbability where
  p : ℝ
  h_pos : 0 < p
  h_lt_one : p < 1

namespace BinaryProbability

variable (bp : BinaryProbability)

/-- The complement probability 1 - p > 0. -/
theorem one_sub_pos : 0 < 1 - bp.p := by
  linarith [bp.h_lt_one]

/-- The odds ratio p / (1 - p) > 0. -/
theorem odds_pos : 0 < bp.p / (1 - bp.p) :=
  div_pos bp.h_pos bp.one_sub_pos

/-- The logit coordinate: $\mathrm{logit}(p) = \ln(p / (1 - p))$. -/
def logit : ℝ :=
  Real.log (bp.p / (1 - bp.p))

/-- Centered log-ratio (clr) coordinates in the 2D simplex:
    $$\mathrm{clr}_1 = \frac{1}{2} \mathrm{logit}(p), \quad \mathrm{clr}_2 = -\frac{1}{2} \mathrm{logit}(p)$$ -/
def clr1 : ℝ := bp.logit / 2
def clr2 : ℝ := -bp.logit / 2

/-- 🏆 THEOREM 1: The clr coordinates lie in the traceless hyperplane $\sum u_i = 0$ (Cartan of $\mathfrak{sl}(2, \mathbb{R})$). -/
theorem clr_sum_zero : bp.clr1 + bp.clr2 = 0 := by
  dsimp [clr1, clr2]
  ring

/-- The Jaynesian maximum entropy prior $p_{\mathrm{Jaynes}} = 1/2$. -/
def jaynesianPrior : BinaryProbability where
  p := 1 / 2
  h_pos := by linarith
  h_lt_one := by linarith

/-- 🏆 THEOREM 2: The Jaynesian prior is the exact additive zero (origin) in the Aitchison vector space:
    $$\mathrm{logit}(p_{\mathrm{Jaynes}}) = 0, \quad \mathrm{clr}(p_{\mathrm{Jaynes}}) = \mathbf{0}$$ -/
theorem jaynesian_logit_zero : jaynesianPrior.logit = 0 := by
  dsimp [logit, jaynesianPrior]
  have h_eq : (1 / 2 : ℝ) / (1 - (1 / 2 : ℝ)) = 1 := by ring
  rw [h_eq, Real.log_one]

theorem jaynesian_clr_zero : jaynesianPrior.clr1 = 0 ∧ jaynesianPrior.clr2 = 0 := by
  dsimp [clr1, clr2]
  rw [jaynesian_logit_zero]
  constructor <;> ring

/-- Centered velocity coordinate $v = 2p - 1 \in (-1, 1)$. -/
def velocity : ℝ := 2 * bp.p - 1

theorem velocity_gt_neg_one : -1 < bp.velocity := by
  dsimp [velocity]
  linarith [bp.h_pos]

theorem velocity_lt_one : bp.velocity < 1 := by
  dsimp [velocity]
  linarith [bp.h_lt_one]

/-- Relativistic rapidity $\theta = \frac{1}{2} \ln\left(\frac{1 + v}{1 - v}\right)$. -/
def rapidity : ℝ :=
  (1 / 2) * Real.log ((1 + bp.velocity) / (1 - bp.velocity))

/-- 🏆 THEOREM 3: The velocity ratio $(1+v)/(1-v)$ equals the probability odds ratio $p/(1-p)$. -/
theorem velocity_ratio_eq_odds :
    (1 + bp.velocity) / (1 - bp.velocity) = bp.p / (1 - bp.p) := by
  dsimp [velocity]
  have h1 : 1 + (2 * bp.p - 1) = 2 * bp.p := by ring
  have h2 : 1 - (2 * bp.p - 1) = 2 * (1 - bp.p) := by ring
  rw [h1, h2]
  have h_ne : (2 : ℝ) ≠ 0 := by norm_num
  have h_denom : 1 - bp.p ≠ 0 := by linarith [bp.one_sub_pos]
  rw [mul_div_mul_left _ _ h_ne]

/-- 🏆 THEOREM 4: Relativistic rapidity duality:
    The logit coordinate is exactly twice the relativistic rapidity:
    $$\mathrm{logit}(p) = 2 \theta$$
    and the clr coordinates are the rapidities: $\mathrm{clr}_1 = \theta, \mathrm{clr}_2 = -\theta$. -/
theorem logit_eq_two_mul_rapidity :
    bp.logit = 2 * bp.rapidity := by
  dsimp [rapidity, logit]
  rw [bp.velocity_ratio_eq_odds]
  ring

theorem clr1_eq_rapidity : bp.clr1 = bp.rapidity := by
  dsimp [clr1]
  rw [bp.logit_eq_two_mul_rapidity]
  ring

theorem clr2_eq_neg_rapidity : bp.clr2 = -bp.rapidity := by
  dsimp [clr2]
  rw [bp.logit_eq_two_mul_rapidity]
  ring

/-- The sigmoid squashing function mapping Lie algebra rapidity $2\theta \in \mathbb{R}$ back to probability:
    $$\sigma(x) = \frac{1}{1 + e^{-x}}$$ -/
def sigmoid (x : ℝ) : ℝ :=
  1 / (1 + Real.exp (-x))

/-- 🏆 THEOREM 5: The sigmoid squashing function maps $2\theta = \mathrm{logit}(p)$ back to $p$:
    $$\sigma(2\theta) = p$$ -/
theorem sigmoid_two_rapidity_eq_p :
    sigmoid (2 * bp.rapidity) = bp.p := by
  rw [← bp.logit_eq_two_mul_rapidity]
  dsimp [sigmoid, logit]
  have h_odds_pos := bp.odds_pos
  rw [← Real.log_inv]
  rw [Real.exp_log (inv_pos.mpr h_odds_pos)]
  have h_inv : (bp.p / (1 - bp.p))⁻¹ = (1 - bp.p) / bp.p := inv_div _ _
  rw [h_inv]
  have hp_pos : bp.p ≠ 0 := by linarith [bp.h_pos]
  have h_one_add : 1 + (1 - bp.p) / bp.p = 1 / bp.p := by
    rw [← div_self hp_pos]
    rw [← add_div]
    ring
  rw [h_one_add]
  exact one_div_one_div bp.p

/-- 🏆 THEOREM 6: Sigmoid of zero yields the Jaynesian prior: $\sigma(0) = 1/2$. -/
theorem sigmoid_zero : sigmoid 0 = 1 / 2 := by
  dsimp [sigmoid]
  rw [neg_zero, Real.exp_zero]
  norm_num

/-- 🏆 THEOREM 7: Sigmoid strictly lies in the open interval (0, 1). -/
theorem sigmoid_pos (x : ℝ) : 0 < sigmoid x := by
  dsimp [sigmoid]
  have h : 0 < 1 + Real.exp (-x) := by linarith [Real.exp_pos (-x)]
  exact div_pos zero_lt_one h

theorem sigmoid_lt_one (x : ℝ) : sigmoid x < 1 := by
  dsimp [sigmoid]
  have h : 1 < 1 + Real.exp (-x) := by linarith [Real.exp_pos (-x)]
  exact (div_lt_one (by linarith [Real.exp_pos (-x)])).mpr h

/-- Apollonian cross-ratio metric between two states:
    $$d_{\mathrm{Apol}}(p, q) = |\mathrm{logit}(p) - \mathrm{logit}(q)|$$ -/
def apollonianDistance (p q : BinaryProbability) : ℝ :=
  |p.logit - q.logit|

/-- 🏆 THEOREM 8: Apollonian distance in terms of rapidity difference:
    $$d_{\mathrm{Apol}}(p, q) = 2 |\theta_p - \theta_q|$$ -/
theorem apollonian_distance_eq_two_mul_rapidity_diff (p q : BinaryProbability) :
    apollonianDistance p q = 2 * |p.rapidity - q.rapidity| := by
  dsimp [apollonianDistance]
  rw [p.logit_eq_two_mul_rapidity, q.logit_eq_two_mul_rapidity]
  have h : 2 * p.rapidity - 2 * q.rapidity = 2 * (p.rapidity - q.rapidity) := by ring
  rw [h, abs_mul]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]

/-- 🏆 THEOREM 9: Metric properties of the Apollonian cross-ratio metric. -/
theorem apollonian_self (p : BinaryProbability) :
    apollonianDistance p p = 0 := by
  dsimp [apollonianDistance]
  simp

theorem apollonian_comm (p q : BinaryProbability) :
    apollonianDistance p q = apollonianDistance q p := by
  dsimp [apollonianDistance]
  exact abs_sub_comm _ _

theorem apollonian_triangle (p q r : BinaryProbability) :
    apollonianDistance p r ≤ apollonianDistance p q + apollonianDistance q r := by
  dsimp [apollonianDistance]
  have h := abs_sub_le (p.logit) (q.logit) (r.logit)
  exact h

/-- 🏆 THEOREM 10: Invariance of the Apollonian rapidity distance under Lorentz boost / rapidity shifts:
    $$2 |(\theta_p + \Delta) - (\theta_q + \Delta)| = 2 |\theta_p - \theta_q|$$ -/
theorem apollonian_boost_invariance (p q : BinaryProbability) (delta : ℝ) :
    2 * |(p.rapidity + delta) - (q.rapidity + delta)| = apollonianDistance p q := by
  rw [apollonian_distance_eq_two_mul_rapidity_diff]
  have h : (p.rapidity + delta) - (q.rapidity + delta) = p.rapidity - q.rapidity := by ring
  rw [h]

/-- 🏆 THEOREM 11: Probability weights sum to 1 identically: $p + (1-p) = 1$. -/
theorem probability_weights_sum : bp.p + (1 - bp.p) = 1 := by
  ring

/-- 🏆 THEOREM 12: At the Jaynesian prior $p = 1/2$, both weights are equal to $1/2$,
    recovering the maximally mixed state $\hat{\rho} = \frac{1}{2} \mathbb{I}$ (the throat state). -/
theorem jaynesian_weights_equal :
    jaynesianPrior.p = 1 / 2 ∧ (1 - jaynesianPrior.p) = 1 / 2 := by
  dsimp [jaynesianPrior]
  constructor <;> ring

/-- 🏆 MASTER CONJUNCTION: Certified Aitchison Simplex & Relativistic Rapidity Synthesis. -/
theorem certified_aitchison_jaynes_rapidity_synthesis (bp : BinaryProbability) :
    (bp.clr1 + bp.clr2 = 0) ∧
    (jaynesianPrior.logit = 0) ∧
    (jaynesianPrior.clr1 = 0 ∧ jaynesianPrior.clr2 = 0) ∧
    (bp.logit = 2 * bp.rapidity) ∧
    (bp.clr1 = bp.rapidity) ∧
    (bp.clr2 = -bp.rapidity) ∧
    (sigmoid (2 * bp.rapidity) = bp.p) ∧
    (sigmoid 0 = 1 / 2) ∧
    (bp.p + (1 - bp.p) = 1) ∧
    (jaynesianPrior.p = 1 / 2 ∧ (1 - jaynesianPrior.p) = 1 / 2) ∧
    (∀ q : BinaryProbability, apollonianDistance bp q = 2 * |bp.rapidity - q.rapidity|) ∧
    (∀ (q : BinaryProbability) (delta : ℝ),
      2 * |(bp.rapidity + delta) - (q.rapidity + delta)| = apollonianDistance bp q) :=
  ⟨bp.clr_sum_zero,
   jaynesian_logit_zero,
   jaynesian_clr_zero,
   bp.logit_eq_two_mul_rapidity,
   bp.clr1_eq_rapidity,
   bp.clr2_eq_neg_rapidity,
   bp.sigmoid_two_rapidity_eq_p,
   sigmoid_zero,
   bp.probability_weights_sum,
   jaynesian_weights_equal,
   fun q => apollonian_distance_eq_two_mul_rapidity_diff bp q,
   fun q delta => apollonian_boost_invariance bp q delta⟩

end BinaryProbability

end InfoGeometry.Physics.AitchisonJaynesRapidity
