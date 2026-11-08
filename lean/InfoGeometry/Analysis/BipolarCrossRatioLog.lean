import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Coordinate.ApolloniusLogCoordinates
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

/-!
# Bipolar cross-ratio logarithmic coordinate

This file adds only the logarithmic layer over the repository's existing
`CayleyCriticalLineCircleBridge`. The underlying Möbius map is not duplicated:
`crossRatio01` is an abbreviation for the canonical `cayleyToFugacity` owner.

No electrostatic, thermodynamic, or relativistic interpretation is used here.
Because `Complex.log` is the principal branch, source/sink exchange is recorded
at the exact multiplicative level and through exponentiation; we do not assert
the globally false principal-branch equality `W(1-s) = -W(s)`.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarCrossRatioLog

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-- The twice-punctured complex plane. -/
def punctured01 : Set ℂ := {s | s ≠ 0 ∧ s ≠ 1}

/-- Canonical repository Möbius coordinate `s / (1-s)`. -/
abbrev crossRatio01 : ℂ → ℂ := cayleyToFugacity

/-- Principal logarithmic coordinate associated with `crossRatio01`. -/
def bipolarLog (s : ℂ) : ℂ := Complex.log (crossRatio01 s)

/-- Real logarithmic coordinate. -/
def eta (s : ℂ) : ℝ := (bipolarLog s).re

/-- Angular principal-branch coordinate. -/
def theta (s : ℂ) : ℝ := (bipolarLog s).im

theorem eta_zero_iff_re_eq_half {s : ℂ} (hs : s ∈ punctured01) :
    eta s = 0 ↔ s.re = 1 / 2 := by
  simpa [eta, bipolarLog, Complex.log_re, crossRatio01,
    InfoGeometry.Apollonius.eta, InfoGeometry.Apollonius.crossRatio] using
    (InfoGeometry.Apollonius.eta_zero_iff_re_eq_half ⟨s, hs⟩)

lemma one_sub_ne_zero_of_mem {s : ℂ} (hs : s ∈ punctured01) :
    1 - s ≠ 0 := by
  exact sub_ne_zero.mpr hs.2.symm

lemma crossRatio01_ne_zero {s : ℂ} (hs : s ∈ punctured01) :
    crossRatio01 s ≠ 0 := by
  unfold crossRatio01 cayleyToFugacity
  exact div_ne_zero hs.1 (one_sub_ne_zero_of_mem hs)

lemma one_sub_mem_punctured01 {s : ℂ} (hs : s ∈ punctured01) :
    1 - s ∈ punctured01 := by
  constructor
  · exact one_sub_ne_zero_of_mem hs
  · intro h
    apply hs.1
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by ring

/-- Readback of the repository-owned source/sink inversion theorem. -/
theorem crossRatio01_one_sub {s : ℂ} (_hs : s ∈ punctured01) :
    crossRatio01 (1 - s) = (crossRatio01 s)⁻¹ :=
  cayleyToFugacity_one_sub_eq_inv s

/-- Reflection commutes exactly with the canonical Möbius coordinate. -/
theorem crossRatio01_conj (s : ℂ) :
    crossRatio01 ((starRingEnd ℂ) s) = (starRingEnd ℂ) (crossRatio01 s) := by
  change (starRingEnd ℂ) s / (1 - (starRingEnd ℂ) s) =
    (starRingEnd ℂ) (s / (1 - s))
  rw [map_div₀]
  simp only [map_sub, map_one]

/-- Exponentiating the principal logarithm recovers `q` on the punctured domain. -/
theorem exp_bipolarLog {s : ℂ} (hs : s ∈ punctured01) :
    Complex.exp (bipolarLog s) = crossRatio01 s := by
  exact Complex.exp_log (crossRatio01_ne_zero hs)

/-- The real and angular readouts are modulus-log and principal argument. -/
theorem bipolarLog_real_imag (s : ℂ) :
    eta s = Real.log ‖crossRatio01 s‖ ∧
      theta s = Complex.arg (crossRatio01 s) := by
  exact ⟨Complex.log_re _, Complex.log_im _⟩

/-- Principal-branch-safe form of `W(1-s) = -W(s) mod 2πi`. -/
theorem exp_swap_log_sum_eq_one {s : ℂ} (hs : s ∈ punctured01) :
    Complex.exp (bipolarLog (1 - s) + bipolarLog s) = 1 := by
  rw [Complex.exp_add, exp_bipolarLog (one_sub_mem_punctured01 hs), exp_bipolarLog hs]
  rw [crossRatio01_one_sub hs]
  exact inv_mul_cancel₀ (crossRatio01_ne_zero hs)

/-- The real logarithmic readout is odd under source/sink exchange. -/
theorem eta_one_sub {s : ℂ} (hs : s ∈ punctured01) :
    eta (1 - s) = -eta s := by
  rw [eta, bipolarLog, Complex.log_re, crossRatio01_one_sub hs]
  rw [norm_inv, Real.log_inv]
  simpa [eta] using (congrArg Neg.neg (bipolarLog_real_imag s).1).symm

/-- The vertical bisector of the distinguished pair. -/
def criticalLine (y : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I

@[simp] theorem criticalLine_re (y : ℝ) :
    (criticalLine y).re = 1 / 2 := by
  simp [criticalLine]

@[simp] theorem criticalLine_im (y : ℝ) :
    (criticalLine y).im = y := by
  simp [criticalLine]

theorem criticalLine_onCanonicalCriticalLine (y : ℝ) :
    OnCriticalLine (criticalLine y) := by
  simp [OnCriticalLine]

/-- Canonical squared-norm readback: the vertical bisector maps to the unit circle. -/
theorem normSq_crossRatio01_criticalLine (y : ℝ) :
    Complex.normSq (crossRatio01 (criticalLine y)) = 1 :=
  cayleyToFugacity_mem_unitCircle_of_criticalLine
    (criticalLine y) (by simp [OnCriticalLine])

/-- On the vertical bisector, subtraction from `1` is complex conjugation. -/
theorem one_sub_criticalLine (y : ℝ) :
    1 - criticalLine y = (starRingEnd ℂ) (criticalLine y) := by
  apply Complex.ext <;> simp [criticalLine] <;> ring

lemma criticalLine_ne_zero (y : ℝ) : criticalLine y ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [criticalLine] at hre

lemma criticalLine_ne_one (y : ℝ) : criticalLine y ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [criticalLine] at hre

lemma criticalLine_mem_punctured01 (y : ℝ) : criticalLine y ∈ punctured01 :=
  ⟨criticalLine_ne_zero y, criticalLine_ne_one y⟩

/-- Norm-one form of the canonical squared-norm theorem. -/
theorem norm_crossRatio01_criticalLine (y : ℝ) :
    ‖crossRatio01 (criticalLine y)‖ = 1 := by
  change ‖criticalLine y / (1 - criticalLine y)‖ = 1
  rw [norm_div, one_sub_criticalLine]
  have hnorm : ‖(starRingEnd ℂ) (criticalLine y)‖ = ‖criticalLine y‖ := by
    simp [Complex.star_def]
  rw [hnorm]
  exact div_self (by simpa using criticalLine_ne_zero y)

/-- Consequently the logarithmic radial coordinate vanishes identically there. -/
theorem eta_criticalLine (y : ℝ) : eta (criticalLine y) = 0 := by
  rw [eta, bipolarLog, Complex.log_re, norm_crossRatio01_criticalLine]
  simp

/-- Exact exponential decomposition `exp(eta + i theta) = q`. -/
theorem exp_eta_theta {s : ℂ} (hs : s ∈ punctured01) :
    Complex.exp ((eta s : ℂ) + (theta s : ℂ) * Complex.I) = crossRatio01 s := by
  have hsplit :
      ((eta s : ℂ) + (theta s : ℂ) * Complex.I) = bipolarLog s := by
    apply Complex.ext <;> simp [eta, theta]
  rw [hsplit]
  exact exp_bipolarLog hs

/-- Real logistic compactification. -/
def logistic (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t)

theorem logistic_pos (t : ℝ) : 0 < logistic t := by
  exact div_pos (Real.exp_pos t) (by positivity)

theorem logistic_lt_one (t : ℝ) : logistic t < 1 := by
  rw [logistic]
  exact (div_lt_one (by positivity)).2 (by linarith [Real.exp_pos t])

/-- On the real logistic slice, the canonical Möbius coordinate is `exp(t)`. -/
theorem crossRatio01_logistic (t : ℝ) :
    crossRatio01 (logistic t : ℂ) = (Real.exp t : ℂ) := by
  have hreal : logistic t / (1 - logistic t) = Real.exp t := by
    rw [div_eq_iff (ne_of_gt (sub_pos.mpr (logistic_lt_one t)))]
    rw [logistic]
    field_simp [ne_of_gt (by positivity : 0 < 1 + Real.exp t)]
    ring
  change (logistic t / (1 - logistic t) : ℂ) = (Real.exp t : ℂ)
  exact_mod_cast hreal
/-- The principal logarithmic radial coordinate inverts the real logistic map. -/
theorem eta_logistic (t : ℝ) : eta (logistic t : ℂ) = t := by
  rw [eta, bipolarLog, crossRatio01_logistic, Complex.log_re]
  simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos t), Real.log_exp]

end InfoGeometry.Analysis.BipolarCrossRatioLog
