/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import InfoGeometry.ParaKahler.RapidityAngleApollonius

namespace InfoGeometry.ParaKahler.RapidityAngleApollonius

noncomputable section

/-- The logarithmic Dikin potential has derivative `2 * tanh`. -/
theorem hasDerivAt_dikinRapidityPotential (χ : ℝ) :
    HasDerivAt (fun x : ℝ => 2 * Real.log (Real.cosh x))
      (2 * Real.tanh χ) χ := by
  have h := (Real.hasDerivAt_cosh χ).log (Real.cosh_pos χ).ne'
  convert h.const_mul 2 using 1;
    simp [Real.tanh_eq_sinh_div_cosh]

/-- The derivative of the hyperbolic signature is `1 - tanh²`. -/
theorem hasDerivAt_souriauSignature (χ : ℝ) :
    HasDerivAt Real.tanh (1 - (Real.tanh χ) ^ 2) χ := by
  have h := (Real.hasDerivAt_sinh χ).div (Real.hasDerivAt_cosh χ)
    (Real.cosh_pos χ).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  convert h using 1
  · funext x
    exact Real.tanh_eq_sinh_div_cosh x
  · field_simp [Real.cosh_pos χ]

/-- The second derivative of the logarithmic Dikin potential is the Dikin metric. -/
theorem hasDerivAt_deriv_dikinRapidityPotential (χ : ℝ) :
    HasDerivAt
      (fun x : ℝ => deriv (fun y : ℝ => 2 * Real.log (Real.cosh y)) x)
      (dikinRapidityMetric χ) χ := by
  have hfun :
      (fun x : ℝ => deriv (fun y : ℝ => 2 * Real.log (Real.cosh y)) x) =
        (fun x : ℝ => 2 * Real.tanh x) := by
    funext x
    exact (hasDerivAt_dikinRapidityPotential x).deriv
  rw [hfun]
  have h := (hasDerivAt_souriauSignature χ).const_mul 2
  convert h using 1
  unfold dikinRapidityMetric souriauSignature
  ring

@[simp] theorem deriv_dikinRapidityPotential (χ : ℝ) :
    deriv (fun x : ℝ => 2 * Real.log (Real.cosh x)) χ = 2 * Real.tanh χ :=
  (hasDerivAt_dikinRapidityPotential χ).deriv

@[simp] theorem second_deriv_dikinRapidityPotential (χ : ℝ) :
    deriv (fun x : ℝ => deriv (fun y : ℝ => 2 * Real.log (Real.cosh y)) x) χ =
      dikinRapidityMetric χ :=
  (hasDerivAt_deriv_dikinRapidityPotential χ).deriv

end
end InfoGeometry.ParaKahler.RapidityAngleApollonius
