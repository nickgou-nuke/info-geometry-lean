import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Quantitative weak-value reconstruction bounds

These are finite, pointwise estimates on the numerator and denominator, not a
Navier--Stokes existence theorem. Complex norm amplification requires a
noncancelling numerator; real amplification additionally requires phase control.
A logarithmic overlap barrier is not identified with enstrophy.

Mathlib division and logarithm are totalized at zero. All physical pole and
barrier estimates below explicitly exclude the zero denominator.
-/

noncomputable section
namespace InfoGeometry.Canonical.WeakValuePoleBounds

/-- Real observable extracted from a complex transition quotient. -/
def realReadout (n d : ℂ) : ℝ := (n / d).re

/-- Scalar overlap barrier, not a spatial energy or a matrix log-det barrier. -/
def overlapBarrier (d : ℂ) : ℝ := -Real.log (Complex.normSq d)

/-- Exact finite-difference numerator; this records the possible cancellation. -/
theorem quotient_difference {𝕜 : Type*} [Field 𝕜]
    (n₀ n₁ d₀ d₁ : 𝕜) (h₀ : d₀ ≠ 0) (h₁ : d₁ ≠ 0) :
    n₁ / d₁ - n₀ / d₀ =
      (d₀ * (n₁ - n₀) - n₀ * (d₁ - d₀)) / (d₁ * d₀) := by
  field_simp [h₀, h₁]
  <;> ring

/-- Complex amplification under an explicit noncancellation inequality. -/
theorem norm_quotient_gt (n d : ℂ) (hd : d ≠ 0) (R : ℝ)
    (h : R * ‖d‖ < ‖n‖) : R < ‖n / d‖ := by
  rw [norm_div]
  exact (lt_div_iff₀ (norm_pos_iff.mpr hd)).2 h

/-- A uniform numerator lower bound gives a quantitative pole threshold. -/
theorem norm_quotient_gt_of_lower_bound (n d : ℂ) (hd : d ≠ 0)
    (R c : ℝ) (hn : c ≤ ‖n‖) (hsmall : R * ‖d‖ < c) :
    R < ‖n / d‖ :=
  norm_quotient_gt n d hd R (lt_of_lt_of_le hsmall hn)

/-- The phase-sensitive numerator of the real weak value. -/
theorem realReadout_eq (n d : ℂ) :
    realReadout n d = (n.re * d.re + n.im * d.im) / Complex.normSq d := by
  simp only [realReadout, Complex.div_re]
  ring

/-- The exact criterion for a real pole, not just a complex-modulus pole. -/
theorem realReadout_gt_iff (n d : ℂ) (hd : d ≠ 0) (R : ℝ) :
    R < realReadout n d ↔
      R * Complex.normSq d < n.re * d.re + n.im * d.im := by
  have hpos : 0 < Complex.normSq d := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hd) 2
  rw [realReadout_eq]
  exact lt_div_iff₀ hpos

/-- A purely imaginary quotient can have arbitrarily large norm and zero real part. -/
@[simp] theorem imaginary_numerator_realReadout (d : ℝ) :
    realReadout Complex.I (d : ℂ) = 0 := by
  simp [realReadout, Complex.div_ofReal_re]

/-- A denominator zero alone cannot force amplification: the numerator may cancel. -/
theorem equal_numerator_realReadout (d : ℂ) (hd : d ≠ 0) :
    realReadout d d = 1 := by
  simp [realReadout, hd]

/-- This is Mathlib's totalization, not a physical value assigned to a pole. -/
@[simp] theorem realReadout_zero_denominator (n : ℂ) :
    realReadout n 0 = 0 := by
  simp [realReadout]

/-- A finite threshold theorem for the logarithmic overlap barrier. -/
theorem overlapBarrier_gt_iff (d : ℂ) (hd : d ≠ 0) (B : ℝ) :
    B < overlapBarrier d ↔ Complex.normSq d < Real.exp (-B) := by
  have hpos : 0 < Complex.normSq d := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hd) 2
  unfold overlapBarrier
  rw [← Real.log_lt_iff_lt_exp hpos]
  constructor <;> intro h <;> linarith

/-- Native quotient differentiation: spatial or time profiles must be supplied. -/
theorem hasDerivAt_quotient {n d : ℝ → ℝ} {n' d' t : ℝ}
    (hn : HasDerivAt n n' t) (hd : HasDerivAt d d' t) (hd0 : d t ≠ 0) :
    HasDerivAt (fun s => n s / d s)
      ((n' * d t - n t * d') / (d t) ^ 2) t :=
  hn.div hd hd0

/-- An upper derivative bound; its divergence is not a blowup lower bound. -/
theorem quotient_derivative_abs_le (n d n' d' : ℝ) :
    |(n' * d - n * d') / d ^ 2| ≤
      (|n'| * |d| + |n| * |d'|) / d ^ 2 := by
  rw [abs_div, abs_of_nonneg (sq_nonneg d)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg d)
  simpa only [sub_eq_add_neg, abs_mul, abs_neg] using
    (abs_add (n' * d) (-(n * d')))

/-- Constant ratios have exactly zero derivative numerator, even near small overlaps. -/
theorem proportional_derivative_numerator (a d d' : ℝ) :
    (a * d') * d - (a * d) * d' = 0 := by
  ring

/-- A genuine finite weighted-gradient lower bound requires spatial weight as well
as a pointwise lower bound. This is not a continuum enstrophy claim. -/
theorem sampled_gradient_energy_lower_bound {ι : Type*} (s : Finset ι)
    (w g : ι → ℝ) (c : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hg : ∀ i ∈ s, c ^ 2 ≤ (g i) ^ 2) :
    (∑ i ∈ s, w i) * c ^ 2 ≤ ∑ i ∈ s, w i * (g i) ^ 2 := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hg i hi) (hw i hi))

end InfoGeometry.Canonical.WeakValuePoleBounds
