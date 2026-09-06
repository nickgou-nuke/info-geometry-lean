import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Analysis.BipolarLogDifferential
import Mathlib.Tactic

/-!
# Apollonius reflection and metric-density correction

This file recovers the exact mathematics behind the informal method-of-images
and pullback-metric discussion.

The reflection used here is

`mirror(s) = 1 - conj(s)`.

Its fixed set is exactly `Re(s)=1/2`, and the logarithmic radial coordinate
`eta = log |s/(1-s)|` is odd under this reflection. This is the rigorous
reflection principle behind the image-charge language; no conductor boundary
condition or physical surface charge is asserted.

The pullback metric is represented only by its conformal density

`|dW|^2 = |dlog01(s)|^2`.

The density has poles at `0` and `1`, but the inversion chart `u=1/s` shows that
the end `s=∞` is removable for the metric coefficient. Therefore one must not
claim that the metric on `ℂ \ {0,1}` is globally complete merely because the two
finite punctures are infinitely far away.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarApolloniusReflectionMetric

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential

/-- Reflection across the vertical bisector `Re(s)=1/2`. -/
def mirror (s : ℂ) : ℂ := 1 - Complex.conj s

@[simp] theorem mirror_involutive (s : ℂ) : mirror (mirror s) = s := by
  apply Complex.ext <;> simp [mirror] <;> ring

/-- The fixed locus of `mirror` is exactly the vertical bisector. -/
theorem mirror_fixed_iff (s : ℂ) :
    mirror s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp [mirror] at hre
    linarith
  · intro hs
    apply Complex.ext
    · simp [mirror, hs]
      linarith
    · simp [mirror]

/-- Every standard critical-line point is fixed by the reflection. -/
@[simp] theorem mirror_criticalLine (y : ℝ) :
    mirror (criticalLine y) = criticalLine y := by
  exact (mirror_fixed_iff _).2 (criticalLine_re y)

/-- Under reflection, the canonical Cayley coordinate is inverse-conjugated. -/
theorem crossRatio01_mirror (s : ℂ) :
    crossRatio01 (mirror s) = (Complex.conj (crossRatio01 s))⁻¹ := by
  calc
    crossRatio01 (mirror s)
        = crossRatio01 (1 - Complex.conj s) := rfl
    _ = (crossRatio01 (Complex.conj s))⁻¹ := by
      simpa using
        InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.cayleyToFugacity_one_sub_eq_inv
          (Complex.conj s)
    _ = (Complex.conj (crossRatio01 s))⁻¹ := by
      rw [crossRatio01_conj]

/-- The logarithmic radial coordinate is odd under the reflection. -/
theorem eta_mirror (s : ℂ) : eta (mirror s) = -eta s := by
  rw [eta, bipolarLog, Complex.log_re, crossRatio01_mirror]
  rw [norm_inv, Complex.norm_conj, Real.log_inv]

/-- Apollonius form of the radial coordinate. -/
theorem eta_eq_log_norm_ratio (s : ℂ) :
    eta s = Real.log (‖s‖ / ‖1 - s‖) := by
  rw [eta, bipolarLog, Complex.log_re]
  simp [crossRatio01, InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.cayleyToFugacity,
    norm_div]

/-- Every radial level is exactly an Apollonius ratio locus. -/
theorem eta_eq_iff_apollonius {s : ℂ} (hs : s ∈ punctured01) (c : ℝ) :
    eta s = c ↔ ‖s‖ = Real.exp c * ‖1 - s‖ := by
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs.1
  have hdenpos : 0 < ‖1 - s‖ := norm_pos_iff.mpr (one_sub_ne_zero_of_mem hs)
  have hratio : 0 < ‖s‖ / ‖1 - s‖ := div_pos hspos hdenpos
  constructor
  · intro h
    have hexp := congrArg Real.exp h
    rw [eta_eq_log_norm_ratio, Real.exp_log hratio] at hexp
    exact (div_eq_iff (ne_of_gt hdenpos)).mp hexp
  · intro h
    rw [eta_eq_log_norm_ratio]
    have hratioeq : ‖s‖ / ‖1 - s‖ = Real.exp c :=
      (div_eq_iff (ne_of_gt hdenpos)).2 h
    rw [hratioeq, Real.log_exp]

/-- Zero radial level is exactly equal distance from the two punctures. -/
theorem eta_eq_zero_iff_equidistant {s : ℂ} (hs : s ∈ punctured01) :
    eta s = 0 ↔ ‖s‖ = ‖1 - s‖ := by
  simpa using (eta_eq_iff_apollonius hs 0)

/-- The conformal density of the pullback metric `|dW|²`. -/
def metricDensity (s : ℂ) : ℝ := Complex.normSq (dlog01 s)

/-- Exact density formula on the twice-punctured domain. -/
theorem metricDensity_eq {s : ℂ} (hs : s ∈ punctured01) :
    metricDensity s =
      (Complex.normSq s * Complex.normSq (1 - s))⁻¹ := by
  rw [metricDensity, dlog01_eq_one_div_mul hs, one_div,
    Complex.normSq_inv, Complex.normSq_mul]

/-- Differential coefficient after the inversion chart `s = u⁻¹`.
The factor `-(u⁻²)` is the derivative of inversion. -/
def inversionPullbackDlog (u : ℂ) : ℂ :=
  dlog01 (u⁻¹) * (-(u⁻²))

/-- In the inversion chart, the logarithmic differential becomes `du/(1-u)`.
Thus the apparent metric singularity at `s=∞` is removable. -/
theorem inversionPullbackDlog_eq {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    inversionPullbackDlog u = 1 / (1 - u) := by
  unfold inversionPullbackDlog dlog01
  have huinv : u⁻¹ ≠ 0 := inv_ne_zero hu0
  have hden : 1 - u⁻¹ ≠ 0 := by
    intro h
    apply hu1
    have : u⁻¹ = 1 := sub_eq_zero.mp h
    exact inv_eq_one.mp this
  field_simp [hu0, huinv, hden]
  ring

/-- The metric density in the completed inversion chart. -/
def infinityChartDensity (u : ℂ) : ℝ :=
  Complex.normSq (1 / (1 - u))

/-- The metric coefficient extends to the omitted infinity point with value `1`. -/
@[simp] theorem infinityChartDensity_zero : infinityChartDensity 0 = 1 := by
  simp [infinityChartDensity]

/-- Reflection/metric packet: the bisector is the fixed locus, `eta` changes
sign, and the infinity chart has a finite nonzero metric coefficient. -/
theorem reflection_metric_packet (s : ℂ) :
    (mirror s = s ↔ s.re = 1 / 2) ∧
      eta (mirror s) = -eta s ∧
      infinityChartDensity 0 = 1 := by
  exact ⟨mirror_fixed_iff s, eta_mirror s, infinityChartDensity_zero⟩

end InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
