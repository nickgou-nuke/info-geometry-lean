import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Analysis.BipolarLogDifferential
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Analysis.BipolarApolloniusReflectionMetric

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

def mirror (s : ℂ) : ℂ := 1 - (starRingEnd ℂ) s

@[simp] theorem mirror_involutive (s : ℂ) : mirror (mirror s) = s := by
  apply Complex.ext <;> simp [mirror] <;> ring

theorem mirror_fixed_iff (s : ℂ) :
    mirror s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have h' := congrArg Complex.re h
    simp [mirror] at h'
    linarith
  · intro h
    apply Complex.ext <;> simp [mirror, h] <;> linarith

theorem crossRatio01_mirror (s : ℂ) :
    crossRatio01 (mirror s) = ((starRingEnd ℂ) (crossRatio01 s))⁻¹ := by
  change cayleyToFugacity (1 - (starRingEnd ℂ) s) =
    ((starRingEnd ℂ) (cayleyToFugacity s))⁻¹
  rw [cayleyToFugacity_one_sub_eq_inv]
  congr 1
  simp [cayleyToFugacity]

theorem eta_mirror (s : ℂ) : eta (mirror s) = -eta s := by
  simp [eta, bipolarLog, Complex.log_re, crossRatio01_mirror,
    norm_inv, Real.log_inv]

@[simp] theorem mirror_criticalLine (y : ℝ) :
    mirror (criticalLine y) = criticalLine y := by
  exact (mirror_fixed_iff _).2 (criticalLine_re y)

theorem eta_eq_log_norm_ratio (s : ℂ) :
    eta s = Real.log (‖s‖ / ‖1 - s‖) := by
  calc
    eta s = Real.log ‖crossRatio01 s‖ := (bipolarLog_real_imag s).1
    _ = Real.log (‖s‖ / ‖1 - s‖) := by
      simp [crossRatio01, cayleyToFugacity, norm_div]

theorem eta_eq_iff_apollonius {s : ℂ} (hs : s ∈ punctured01) (c : ℝ) :
    eta s = c ↔ ‖s‖ = Real.exp c * ‖1 - s‖ := by
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs.1
  have hdpos : 0 < ‖1 - s‖ := norm_pos_iff.mpr (one_sub_ne_zero_of_mem hs)
  have hratio : 0 < ‖s‖ / ‖1 - s‖ := div_pos hspos hdpos
  rw [eta_eq_log_norm_ratio]
  constructor
  · intro h
    have := congrArg Real.exp h
    rw [Real.exp_log hratio] at this
    exact (div_eq_iff (ne_of_gt hdpos)).mp this
  · intro h
    have hratioeq : ‖s‖ / ‖1 - s‖ = Real.exp c :=
      (div_eq_iff (ne_of_gt hdpos)).2 h
    rw [hratioeq, Real.log_exp]

theorem eta_eq_zero_iff_equidistant {s : ℂ} (hs : s ∈ punctured01) :
    eta s = 0 ↔ ‖s‖ = ‖1 - s‖ := by
  simpa using (eta_eq_iff_apollonius hs 0)

def metricDensity (s : ℂ) : ℝ := Complex.normSq (dlog01 s)

theorem metricDensity_eq {s : ℂ} (hs : s ∈ punctured01) :
    metricDensity s = (Complex.normSq s * Complex.normSq (1 - s))⁻¹ := by
  rw [metricDensity, dlog01_eq_one_div_mul hs, one_div,
    Complex.normSq_inv, Complex.normSq_mul]

def inversionPullbackDlog (u : ℂ) : ℂ :=
  dlog01 (u⁻¹) * (-((u⁻¹) ^ 2))

theorem inversionPullbackDlog_eq {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    inversionPullbackDlog u = 1 / (1 - u) := by
  unfold inversionPullbackDlog dlog01
  have huinv : u⁻¹ ≠ 0 := inv_ne_zero hu0
  have hden : 1 - u⁻¹ ≠ 0 := by
    intro h
    apply hu1
    have h1 : (1 : ℂ) = u⁻¹ := sub_eq_zero.mp h
    have : u⁻¹ = 1 := h1.symm
    exact inv_eq_one.mp this
  have hmu : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
  have h1mu : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  field_simp [hu0, huinv, hden, hmu, h1mu] <;> ring

def infinityChartDensity (u : ℂ) : ℝ := Complex.normSq (1 / (1 - u))

@[simp] theorem infinityChartDensity_zero : infinityChartDensity 0 = 1 := by
  simp [infinityChartDensity]

theorem reflection_metric_packet (s : ℂ) :
    (mirror s = s ↔ s.re = 1 / 2) ∧
      eta (mirror s) = -eta s ∧
      infinityChartDensity 0 = 1 := by
  exact ⟨mirror_fixed_iff s, eta_mirror s, infinityChartDensity_zero⟩

end InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
