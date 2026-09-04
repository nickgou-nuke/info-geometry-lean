import InfoGeometry.Analysis.BipolarCrossRatioLog
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Determinant-one lift of the bipolar logarithmic coordinate

This file is a finite linear-algebra layer over
`InfoGeometry.Analysis.BipolarCrossRatioLog`.  It packages the multiplicative
coordinate `q` and the logarithmic coordinate `W` into diagonal `2 × 2` complex
matrices.  No Lorentz, spin, electromagnetic, or thermodynamic interpretation
is used in the definitions or theorems.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarLogSL2

open InfoGeometry.Analysis.BipolarCrossRatioLog

abbrev SL2Block := Matrix (Fin 2) (Fin 2) ℂ

/-- Exact multiplicative torus lift of `q(s)`. -/
def torusLift (s : ℂ) : SL2Block :=
  !![crossRatio01 s, 0;
     0, (crossRatio01 s)⁻¹]

/-- The torus lift has determinant one on the punctured domain. -/
theorem torusLift_det {s : ℂ} (hs : s ∈ punctured01) :
    Matrix.det (torusLift s) = 1 := by
  simp [torusLift, Matrix.det_fin_two, crossRatio01_ne_zero hs]

/-- Positive logarithmic half-weight. -/
def plusWeight (s : ℂ) : ℂ :=
  Complex.exp (bipolarLog s / 2)

/-- Negative logarithmic half-weight. -/
def minusWeight (s : ℂ) : ℂ :=
  Complex.exp (-bipolarLog s / 2)

/-- Principal-log diagonal half-lift. -/
def halfLogLift (s : ℂ) : SL2Block :=
  !![plusWeight s, 0;
     0, minusWeight s]

/-- The principal-log half-lift has determinant one for every complex input. -/
theorem halfLogLift_det (s : ℂ) :
    Matrix.det (halfLogLift s) = 1 := by
  rw [Matrix.det_fin_two]
  simp [halfLogLift, plusWeight, minusWeight]
  rw [← Complex.exp_add]
  have hzero : bipolarLog s / 2 + -bipolarLog s / 2 = 0 := by ring
  rw [hzero, Complex.exp_zero]

/-- The ratio of the two half-weights recovers the exact Möbius coordinate. -/
theorem plusWeight_div_minusWeight {s : ℂ} (hs : s ∈ punctured01) :
    plusWeight s / minusWeight s = crossRatio01 s := by
  apply (div_eq_iff (Complex.exp_ne_zero _)).2
  rw [plusWeight, minusWeight, ← exp_bipolarLog hs]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The product of the two logarithmic half-weights is exactly one. -/
theorem plusWeight_mul_minusWeight (s : ℂ) :
    plusWeight s * minusWeight s = 1 := by
  rw [plusWeight, minusWeight, ← Complex.exp_add]
  have hzero : bipolarLog s / 2 + -bipolarLog s / 2 = 0 := by ring
  rw [hzero, Complex.exp_zero]

/-- Exchange of `0` and `1` swaps the two exact torus weights. -/
theorem torusLift_one_sub {s : ℂ} (hs : s ∈ punctured01) :
    torusLift (1 - s) =
      !![(crossRatio01 s)⁻¹, 0;
         0, crossRatio01 s] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusLift, crossRatio01_one_sub hs, crossRatio01_ne_zero hs]

/-- On the vertical bisector, both exact torus weights have unit norm. -/
theorem torusLift_criticalLine_unit_norm (y : ℝ) :
    ‖(torusLift (criticalLine y)) 0 0‖ = 1 ∧
      ‖(torusLift (criticalLine y)) 1 1‖ = 1 := by
  constructor
  · simpa [torusLift] using norm_crossRatio01_criticalLine y
  · simp [torusLift, norm_crossRatio01_criticalLine y]

/-- On the real logistic slice, the exact torus lift becomes the standard
`diag(exp(t), exp(t)⁻¹)` one-parameter subgroup. -/
theorem torusLift_logistic (t : ℝ) :
    torusLift (logistic t : ℂ) =
      !![(Real.exp t : ℂ), 0;
         0, (Real.exp t : ℂ)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusLift, crossRatio01_logistic]

/-- The logarithmic half-lift on the real logistic slice is exactly
`diag(exp(t/2), exp(-t/2))`. -/
theorem halfLogLift_logistic (t : ℝ) :
    halfLogLift (logistic t : ℂ) =
      !![Complex.exp ((t : ℂ) / 2), 0;
         0, Complex.exp (-(t : ℂ) / 2)] := by
  have hlog : bipolarLog (logistic t : ℂ) = (t : ℂ) := by
    rw [bipolarLog, crossRatio01_logistic]
    rw [← Complex.ofReal_log (le_of_lt (Real.exp_pos t))]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfLogLift, plusWeight, minusWeight, hlog]

end InfoGeometry.Canonical.BipolarLogSL2
