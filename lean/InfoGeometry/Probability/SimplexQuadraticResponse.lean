import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import InfoGeometry.Analysis.BipolarCayleyOccupation

/-!
# Quadratic observations of a binary probability coordinate

An algebraic and differential model, not an assertion of detector dynamics.
The two real metric coefficients below are different. Their identities do
not assert curvature, a physical mass, a soliton equation, or independence
of complementary events. Square roots here are nonnegative real amplitudes;
no complex phase is recovered from a probability.
-/

namespace InfoGeometry.Probability.SimplexQuadraticResponse

noncomputable section

def response (C B x : ℝ) : ℝ := C * x - B * x ^ 2

theorem response_hasDerivAt (C B x : ℝ) :
    HasDerivAt (response C B) (C - 2 * B * x) x := by
  convert ((hasDerivAt_id x).const_mul C).sub
    (((hasDerivAt_id x).pow 2).const_mul B) using 1
  simp
  ring

theorem dilation_defect (C B x : ℝ) :
    x * deriv (response C B) x - response C B x = -B * x ^ 2 := by
  rw [(response_hasDerivAt C B x).deriv]
  unfold response
  ring

theorem probability_coordinate (C B p : ℝ) (hB : B ≠ 0) :
    response C B (C / B * p) = C ^ 2 / B * (p * (1 - p)) := by
  unfold response
  field_simp

theorem vertex_gap (C B x : ℝ) (hB : B ≠ 0) :
    C ^ 2 / (4 * B) - response C B x = B * (x - C / (2 * B)) ^ 2 := by
  unfold response
  field_simp
  ring

theorem response_le_vertex (C B x : ℝ) (hB : 0 < B) :
    response C B x ≤ C ^ 2 / (4 * B) := by
  have h := vertex_gap C B x (ne_of_gt hB)
  have hpos := mul_nonneg (le_of_lt hB) (sq_nonneg (x - C / (2 * B)))
  linarith

theorem response_reflection (C B x : ℝ) (hB : B ≠ 0) :
    response C B (C / B - x) = response C B x := by
  unfold response
  field_simp
  ring

/-- Weighted variance of the binary values zero and one. -/
theorem binary_variance (p : ℝ) :
    p * (1 - p) ^ 2 + (1 - p) * (0 - p) ^ 2 = p * (1 - p) := by
  ring

theorem binary_variance_peak (p : ℝ) :
    p * (1 - p) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (p - 1 / 2)]

theorem amplitude_circle (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.sqrt p ^ 2 + Real.sqrt (1 - p) ^ 2 = 1 := by
  rw [Real.sq_sqrt hp, Real.sq_sqrt (sub_nonneg.mpr hp1)]
  ring

/-- Four amplitudes of a product of two binary distributions are normalized.
The product distribution is specified explicitly, not inferred from marginals. -/
theorem product_amplitude_normalization (p q : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (Real.sqrt p * Real.sqrt q) ^ 2 +
    (Real.sqrt p * Real.sqrt (1 - q)) ^ 2 +
    (Real.sqrt (1 - p) * Real.sqrt q) ^ 2 +
    (Real.sqrt (1 - p) * Real.sqrt (1 - q)) ^ 2 = 1 := by
  simp only [mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hq,
    Real.sq_sqrt (sub_nonneg.mpr hp1), Real.sq_sqrt (sub_nonneg.mpr hq1)]
  ring

theorem complementary_product_positive (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < p * (1 - p) := mul_pos hp (sub_pos.mpr hp1)

/-- Fisher coefficient in probability coordinates. -/
def fisher (p : ℝ) : ℝ := 1 / (p * (1 - p))

/-- Pullback of the Euclidean metric by the log-odds coordinate. -/
def logOddsMetric (p : ℝ) : ℝ := 1 / (p * (1 - p)) ^ 2

theorem metrics_distinct (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    fisher p < logOddsMetric p := by
  have hv := complementary_product_positive p hp hp1
  have hu : p * (1 - p) < 1 := lt_of_le_of_lt (binary_variance_peak p) (by norm_num)
  have hs : (p * (1 - p)) ^ 2 < p * (1 - p) := by nlinarith
  exact one_div_lt_one_div_of_lt (sq_pos_of_pos hv) hs

/-- Exact residual of the rational dead-time model. -/
theorem rational_residual (n τ : ℝ) (h : 1 + n * τ ≠ 0) :
    n / (1 + n * τ) - (n - τ * n ^ 2) = τ ^ 2 * n ^ 3 / (1 + n * τ) := by
  field_simp
  ring

theorem exponential_lower_bound (n τ : ℝ) (hn : 0 ≤ n) :
    n - τ * n ^ 2 ≤ n * Real.exp (-n * τ) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-n * τ)) hn
  nlinarith

/-- The actual derivative of the log-odds coordinate on the open simplex. -/
theorem log_odds_hasDerivAt (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun q : ℝ => Real.log q - Real.log (1 - q))
      (1 / (p * (1 - p))) p := by
  have h0 : p ≠ 0 := ne_of_gt hp
  have h1 : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  convert ((hasDerivAt_id p).log h0).sub
    (((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).log h1) using 1
  dsimp
  field_simp
  ring

/-- Pullback of the Euclidean metric by log odds, as a squared derivative. -/
theorem log_odds_pullback (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (deriv (fun q : ℝ => Real.log q - Real.log (1 - q)) p) ^ 2 =
      logOddsMetric p := by
  rw [(log_odds_hasDerivAt p hp hp1).deriv]
  unfold logOddsMetric
  rw [div_pow, one_pow]

/-- Velocity-field form of the one-dimensional affine geodesic equation.
This proves compatibility of the specified field, not a physical evolution law. -/
theorem logistic_field_geodesic (v p : ℝ) :
    deriv (fun q : ℝ => 2 * v * q * (1 - q)) p * (2 * v * p * (1 - p)) +
      ((2 * p - 1) / (p * (1 - p))) * (2 * v * p * (1 - p)) ^ 2 = 0 := by
  have hd : HasDerivAt (fun q : ℝ => 2 * v * q * (1 - q))
      (2 * v * (1 - 2 * p)) p := by
    convert (((hasDerivAt_id p).const_mul (2 * v)).mul
      ((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p))) using 1
    dsimp
    ring
  rw [hd.deriv]
  field_simp
  ring

theorem kinetic_energy_along_field (v p : ℝ) (hp : p ≠ 0) (hp1 : 1 - p ≠ 0) :
    (1 / 2 : ℝ) * logOddsMetric p * (2 * v * p * (1 - p)) ^ 2 = 2 * v ^ 2 := by
  unfold logOddsMetric
  field_simp

/-- Inversion of a positive radial coordinate is involutive. -/
theorem radial_inversion_involutive (r a : ℝ) (hr : r ≠ 0) (ha : a ≠ 0) :
    a ^ 2 / (a ^ 2 / r) = r := by
  field_simp

/-- The exterior radial interval maps into the half-open probability interval. -/
theorem inverted_radius_probability (r a : ℝ) (ha : 0 < a) (har : a ≤ r) :
    0 < (a / r) ^ 2 ∧ (a / r) ^ 2 ≤ 1 := by
  have hr : 0 < r := lt_of_lt_of_le ha har
  have hpos : 0 < a / r := div_pos ha hr
  have hle : a / r ≤ 1 := (div_le_one hr).mpr har
  constructor
  · positivity
  · nlinarith

/-- A spatial reparameterization is not needed for the exact response symmetry. -/
theorem response_noninjective (C B : ℝ) (hC : C ≠ 0) (hB : B ≠ 0) :
    ¬ Function.Injective (response C B) := by
  intro h
  have he : response C B (C / B) = response C B 0 := by
    simpa using response_reflection C B 0 hB
  have hz := h he
  exact (div_ne_zero hC hB) hz

/-- Reuse the repository's established logistic chart. This profile identity
supplies no differential equation defining a soliton. -/
theorem response_in_rapidity (C B ξ : ℝ) (hB : B ≠ 0) :
    response C B (C / B * InfoGeometry.Analysis.BipolarCrossRatioLog.logistic (2 * ξ)) =
      C ^ 2 / (4 * B) * (1 - Real.tanh ξ ^ 2) := by
  rw [probability_coordinate C B _ hB]
  have h := InfoGeometry.Analysis.BipolarCayleyOccupation.real_polarization_eq_tanh (2 * ξ)
  have hh : 2 * ξ / 2 = ξ := by ring
  rw [hh] at h
  rw [← h]
  ring

end
end InfoGeometry.Probability.SimplexQuadraticResponse
