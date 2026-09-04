import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

/-!
# Bipolar cross-ratio logarithmic coordinate

This file formalizes the complex-analytic core of the two-puncture construction
on `ℂ \ {0,1}`. It deliberately contains no electrostatic, thermodynamic, or
relativistic interpretation.

The primary coordinate is

`q(s) = s / (1 - s)`

and its principal logarithmic readout is

`W(s) = Complex.log (q(s)) = eta(s) + i theta(s)`.

Because `Complex.log` is the principal branch, source/sink exchange is recorded
first at the exact multiplicative level. We do not assert the globally false
principal-branch identity `W(1-s) = -W(s)`.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarCrossRatioLog

/-- The twice-punctured complex plane. -/
def punctured01 : Set ℂ := {s | s ≠ 0 ∧ s ≠ 1}

/-- Möbius coordinate sending `0 ↦ 0` and `1 ↦ ∞`. -/
def crossRatio01 (s : ℂ) : ℂ := s / (1 - s)

/-- Principal logarithmic coordinate associated with `crossRatio01`. -/
def bipolarLog (s : ℂ) : ℂ := Complex.log (crossRatio01 s)

/-- Real logarithmic coordinate. -/
def eta (s : ℂ) : ℝ := (bipolarLog s).re

/-- Angular principal-branch coordinate. -/
def theta (s : ℂ) : ℝ := (bipolarLog s).im

lemma one_sub_ne_zero_of_mem {s : ℂ} (hs : s ∈ punctured01) :
    1 - s ≠ 0 := by
  exact sub_ne_zero.mpr hs.2.symm

lemma crossRatio01_ne_zero {s : ℂ} (hs : s ∈ punctured01) :
    crossRatio01 s ≠ 0 := by
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

/-- Exchange of the two distinguished points acts by inversion on `q`. -/
theorem crossRatio01_one_sub {s : ℂ} (hs : s ∈ punctured01) :
    crossRatio01 (1 - s) = (crossRatio01 s)⁻¹ := by
  rcases hs with ⟨hs0, hs1⟩
  unfold crossRatio01
  have hden : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, hden]

/-- Reflection commutes exactly with the Möbius coordinate. -/
theorem crossRatio01_conj (s : ℂ) :
    crossRatio01 (Complex.conj s) = Complex.conj (crossRatio01 s) := by
  simp [crossRatio01]

/-- Exponentiating the principal logarithm recovers `q` on the punctured domain. -/
theorem exp_bipolarLog {s : ℂ} (hs : s ∈ punctured01) :
    Complex.exp (bipolarLog s) = crossRatio01 s := by
  exact Complex.exp_log (crossRatio01_ne_zero hs)

/-- The real and angular readouts are exactly modulus-log and principal argument. -/
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

/-- The vertical bisector of the distinguished pair. -/
def criticalLine (y : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I

@[simp] theorem criticalLine_re (y : ℝ) :
    (criticalLine y).re = 1 / 2 := by
  simp [criticalLine]

@[simp] theorem criticalLine_im (y : ℝ) :
    (criticalLine y).im = y := by
  simp [criticalLine]

/-- On the vertical bisector, subtraction from `1` is complex conjugation. -/
theorem one_sub_criticalLine (y : ℝ) :
    1 - criticalLine y = Complex.conj (criticalLine y) := by
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

/-- The vertical bisector is mapped by `q` to the unit circle. -/
theorem norm_crossRatio01_criticalLine (y : ℝ) :
    ‖crossRatio01 (criticalLine y)‖ = 1 := by
  rw [crossRatio01, norm_div, one_sub_criticalLine, Complex.norm_conj]
  exact div_self (by simpa using criticalLine_ne_zero y)

/-- Consequently the logarithmic radial coordinate vanishes identically there. -/
theorem eta_criticalLine (y : ℝ) : eta (criticalLine y) = 0 := by
  rw [eta, bipolarLog, Complex.log_re, norm_crossRatio01_criticalLine]
  simp

/-- The exponential decomposition is exact independently of how `eta` and `theta`
are subsequently interpreted. -/
theorem exp_eta_theta {s : ℂ} (hs : s ∈ punctured01) :
    Complex.exp ((eta s : ℂ) + (theta s : ℂ) * Complex.I) = crossRatio01 s := by
  have hsplit :
      ((eta s : ℂ) + (theta s : ℂ) * Complex.I) = bipolarLog s := by
    apply Complex.ext <;> simp [eta, theta]
  rw [hsplit]
  exact exp_bipolarLog hs

/-- Real logistic compactification, retained as a purely analytic coordinate map. -/
def logistic (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t)

theorem logistic_pos (t : ℝ) : 0 < logistic t := by
  exact div_pos (Real.exp_pos t) (by positivity)

theorem logistic_lt_one (t : ℝ) : logistic t < 1 := by
  rw [logistic]
  exact (div_lt_one (by positivity)).2 (by linarith [Real.exp_pos t])

/-- On the real logistic slice, the Möbius coordinate is exactly `exp(t)`. -/
theorem crossRatio01_logistic (t : ℝ) :
    crossRatio01 (logistic t : ℂ) = (Real.exp t : ℂ) := by
  have he : Real.exp t ≠ 0 := ne_of_gt (Real.exp_pos t)
  unfold crossRatio01 logistic
  push_cast
  field_simp [he]
  ring

/-- The principal logarithmic radial coordinate inverts the real logistic map. -/
theorem eta_logistic (t : ℝ) : eta (logistic t : ℂ) = t := by
  rw [eta, bipolarLog, crossRatio01_logistic, Complex.log_re]
  simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos t), Real.log_exp]

end InfoGeometry.Analysis.BipolarCrossRatioLog
