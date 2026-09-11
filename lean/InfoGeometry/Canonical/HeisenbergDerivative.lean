import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import InfoGeometry.Canonical.TopologicalKMSFlow

/-!
# The Heisenberg Derivative of the Modular Flow

This module establishes the explicit, pointwise time-derivatives of the KMS 
thermodynamic flow acting on the Witt basis.

We rigorously prove the Heisenberg-picture equations of motion:
  d/dt α_t(a) = -ω a
  d/dt α_t(a†) = ω a†

These derivatives are established natively and constructively over the
split-signature `Cl(4,4)` Lorentz boost representation, strictly using `HasDerivAt`.
-/

open InfoGeometry.Canonical.TopologicalKMSFlow
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Clifford

noncomputable section

namespace InfoGeometry.Canonical.HeisenbergDerivative

variable (E μ : Fin 4 → ℝ) (i : Fin 4)

/-- The exact continuous derivative of the descending exponential-like flow. -/
theorem hasDerivAt_cosh_sub_sinh (w t : ℝ) :
    HasDerivAt (fun t' => Real.cosh (t' * w) - Real.sinh (t' * w))
               (-w * (Real.cosh (t * w) - Real.sinh (t * w))) t := by
  have h1 : HasDerivAt (fun t' => Real.cosh (t' * w)) (Real.sinh (t * w) * w) t := by
    exact HasDerivAt.comp t (Real.hasDerivAt_cosh (t * w)) (hasDerivAt_mul_const w)
  have h2 : HasDerivAt (fun t' => Real.sinh (t' * w)) (Real.cosh (t * w) * w) t := by
    exact HasDerivAt.comp t (Real.hasDerivAt_sinh (t * w)) (hasDerivAt_mul_const w)
  have h3 := HasDerivAt.sub h1 h2
  convert h3 using 1
  ring

/-- The exact continuous derivative of the ascending exponential-like flow. -/
theorem hasDerivAt_cosh_add_sinh (w t : ℝ) :
    HasDerivAt (fun t' => Real.cosh (t' * w) + Real.sinh (t' * w))
               (w * (Real.cosh (t * w) + Real.sinh (t * w))) t := by
  have h1 : HasDerivAt (fun t' => Real.cosh (t' * w)) (Real.sinh (t * w) * w) t := by
    exact HasDerivAt.comp t (Real.hasDerivAt_cosh (t * w)) (hasDerivAt_mul_const w)
  have h2 : HasDerivAt (fun t' => Real.sinh (t' * w)) (Real.cosh (t * w) * w) t := by
    exact HasDerivAt.comp t (Real.hasDerivAt_sinh (t * w)) (hasDerivAt_mul_const w)
  have h3 := HasDerivAt.add h1 h2
  convert h3 using 1
  ring

/-- 
The Heisenberg equation of motion for the annihilation operators:
  d/dt α_t(a) = -ω a 
-/
theorem hasDerivAt_modularFlow_aVec (t : ℝ) :
    HasDerivAt (fun t' => boostFun E μ t' (aVec i))
               (-ω E μ i • boostFun E μ t (aVec i)) t := by
  have h_eq : (fun t' => boostFun E μ t' (aVec i)) = fun t' => (Real.cosh (t' * ω E μ i) - Real.sinh (t' * ω E μ i)) • aVec i := by
    funext t'
    exact modularFlow_aVec E μ t' i
  rw [h_eq]
  have hd := hasDerivAt_cosh_sub_sinh (ω E μ i) t
  have hd2 := HasDerivAt.smul_const hd (aVec i)
  rw [modularFlow_aVec E μ t i]
  convert hd2 using 1
  ext j
  simp only [Pi.smul_apply, smul_eq_mul, neg_mul]
  ring

/-- 
The Heisenberg equation of motion for the creation operators:
  d/dt α_t(a†) = ω a†
-/
theorem hasDerivAt_modularFlow_adagVec (t : ℝ) :
    HasDerivAt (fun t' => boostFun E μ t' (adagVec i))
               (ω E μ i • boostFun E μ t (adagVec i)) t := by
  have h_eq : (fun t' => boostFun E μ t' (adagVec i)) = fun t' => (Real.cosh (t' * ω E μ i) + Real.sinh (t' * ω E μ i)) • adagVec i := by
    funext t'
    exact modularFlow_adagVec E μ t' i
  rw [h_eq]
  have hd := hasDerivAt_cosh_add_sinh (ω E μ i) t
  have hd2 := HasDerivAt.smul_const hd (adagVec i)
  rw [modularFlow_adagVec E μ t i]
  convert hd2 using 1
  ext j
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end InfoGeometry.Canonical.HeisenbergDerivative
