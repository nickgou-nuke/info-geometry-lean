import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A small, real-valued character interface for additive rapidity and
positive multiplicative scale.  This file does not assert a KMS, KAN, or
Fourier/Mellin transform identification. -/

namespace InfoGeometry.OperatorAlgebra.RindlerCharacterBridge

noncomputable def additiveCharacter (s t : ℝ) : ℝ := Real.exp (s * t)

theorem additiveCharacter_zero (s : ℝ) :
    additiveCharacter s 0 = 1 := by
  simp [additiveCharacter]

theorem additiveCharacter_add (s t u : ℝ) :
    additiveCharacter s (t + u) =
      additiveCharacter s t * additiveCharacter s u := by
  unfold additiveCharacter
  rw [mul_add, Real.exp_add]

theorem additiveCharacter_neg (s t : ℝ) :
    additiveCharacter s (-t) = (additiveCharacter s t)⁻¹ := by
  unfold additiveCharacter
  rw [mul_neg, Real.exp_neg]

noncomputable def scaleCharacter (s x : ℝ) : ℝ :=
  Real.exp (s * Real.log x)

theorem scaleCharacter_mul (s x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    scaleCharacter s (x * y) =
      scaleCharacter s x * scaleCharacter s y := by
  unfold scaleCharacter
  rw [Real.log_mul hx hy, mul_add, Real.exp_add]

theorem scaleCharacter_exp (s t : ℝ) :
    scaleCharacter s (Real.exp t) = additiveCharacter s t := by
  unfold scaleCharacter additiveCharacter
  rw [Real.log_exp]

end InfoGeometry.OperatorAlgebra.RindlerCharacterBridge
