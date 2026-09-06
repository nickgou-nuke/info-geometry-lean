import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Exact bisector trace of the bipolar logarithmic potential

This file recovers the mathematical content behind the informal conductor/image
boundary calculation without introducing electrostatic units.

For real coordinates `s = x + i y`, define

`Phi(x,y) = 1/2 log(x^2+y^2) - 1/2 log((x-1)^2+y^2)`.

This is exactly `log |s| - log |1-s|` wherever both logarithms are defined.
The vertical bisector `x=1/2` is a zero trace, and the horizontal derivative
there is the Cauchy kernel

`1 / (1/4 + y^2)`.

Any physical surface-density factor is external to these theorems.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarBoundaryTrace

/-- Real-coordinate logarithmic bipolar potential. -/
def phiXY (x y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (x ^ 2 + y ^ 2) -
    (1 / 2 : ℝ) * Real.log ((x - 1) ^ 2 + y ^ 2)

/-- The vertical bisector is an exact zero trace. -/
@[simp] theorem phiXY_half (y : ℝ) : phiXY (1 / 2) y = 0 := by
  unfold phiXY
  congr 1
  norm_num
  ring

/-- Reflection across the bisector reverses the real logarithmic potential. -/
theorem phiXY_reflection (x y : ℝ) :
    phiXY (1 - x) y = -phiXY x y := by
  unfold phiXY
  have h0 : (1 - x) ^ 2 = (x - 1) ^ 2 := by ring
  have h1 : ((1 - x) - 1) ^ 2 = x ^ 2 := by ring
  rw [h0, h1]
  ring

/-- Horizontal derivative of the real-coordinate potential away from its two
real singular loci. -/
theorem hasDerivAt_phiXY
    {x y : ℝ}
    (h0 : x ^ 2 + y ^ 2 ≠ 0)
    (h1 : (x - 1) ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun t => phiXY t y)
      (x / (x ^ 2 + y ^ 2) - (x - 1) / ((x - 1) ^ 2 + y ^ 2)) x := by
  have hg0 : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id x).pow 2).add_const (y ^ 2)
  have hg1 : HasDerivAt (fun t : ℝ => (t - 1) ^ 2 + y ^ 2) (2 * (x - 1)) x := by
    have hsub : HasDerivAt (fun t : ℝ => t - 1) 1 x := by
      simpa using (hasDerivAt_id x).sub_const 1
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      (hsub.pow 2).add_const (y ^ 2)
  have hlog0 :
      HasDerivAt (fun t : ℝ => Real.log (t ^ 2 + y ^ 2))
        ((x ^ 2 + y ^ 2)⁻¹ * (2 * x)) x := by
    simpa using (Real.hasDerivAt_log h0).comp x hg0
  have hlog1 :
      HasDerivAt (fun t : ℝ => Real.log ((t - 1) ^ 2 + y ^ 2))
        (((x - 1) ^ 2 + y ^ 2)⁻¹ * (2 * (x - 1))) x := by
    simpa using (Real.hasDerivAt_log h1).comp x hg1
  have hmain :=
    (hlog0.const_mul (1 / 2 : ℝ)).sub (hlog1.const_mul (1 / 2 : ℝ))
  convert hmain using 1 <;> unfold phiXY <;> ring

/-- Exact normal derivative on the zero-trace bisector. -/
theorem hasDerivAt_phiXY_half (y : ℝ) :
    HasDerivAt (fun t => phiXY t y)
      (1 / ((1 / 4 : ℝ) + y ^ 2)) (1 / 2) := by
  have hpos : 0 < (1 / 4 : ℝ) + y ^ 2 := by
    nlinarith [sq_nonneg y]
  have h0 : ((1 / 2 : ℝ) ^ 2 + y ^ 2) ≠ 0 := by
    norm_num
    exact ne_of_gt hpos
  have h1 : (((1 / 2 : ℝ) - 1) ^ 2 + y ^ 2) ≠ 0 := by
    norm_num
    exact ne_of_gt hpos
  have h := hasDerivAt_phiXY (x := (1 / 2 : ℝ)) (y := y) h0 h1
  convert h using 1 <;> norm_num <;> field_simp [ne_of_gt hpos] <;> ring

/-- Ordinary derivative readout of the bisector trace. -/
theorem deriv_phiXY_half (y : ℝ) :
    deriv (fun t => phiXY t y) (1 / 2) = 1 / ((1 / 4 : ℝ) + y ^ 2) := by
  exact (hasDerivAt_phiXY_half y).deriv

/-- The boundary kernel is strictly positive. -/
theorem boundaryKernel_pos (y : ℝ) :
    0 < 1 / ((1 / 4 : ℝ) + y ^ 2) := by
  positivity

/-- Compact exact boundary packet. -/
theorem bipolar_boundary_trace_packet (y : ℝ) :
    phiXY (1 / 2) y = 0 ∧
      deriv (fun t => phiXY t y) (1 / 2) = 1 / ((1 / 4 : ℝ) + y ^ 2) ∧
      0 < 1 / ((1 / 4 : ℝ) + y ^ 2) := by
  exact ⟨phiXY_half y, deriv_phiXY_half y, boundaryKernel_pos y⟩

end InfoGeometry.Analysis.BipolarBoundaryTrace
