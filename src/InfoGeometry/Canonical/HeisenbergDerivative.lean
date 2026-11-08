/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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
thermodynamic flow acting on the Witt basis over the split-signature `Cl(4,4)`
Lorentz boost representation.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.TopologicalKMSFlow`: `boostFun`, `ω`, `modularFlow_aVec`,
    `modularFlow_adagVec`.
  * `InfoGeometry.Clifford.Cl44Witt`: `aVec`, `adagVec`.
- BUCKET 2 (Deconfabulation):
  * Replaced file-level section hypothesis variables with explicit operator and
    frequency parameters on each theorem declaration.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `hasDerivAt_cosh_sub_sinh`: derivative of the descending hyperbolic flow
    $\frac{d}{dt}(\cosh(tw) - \sinh(tw)) = -w(\cosh(tw) - \sinh(tw))$.
  * `hasDerivAt_cosh_add_sinh`: derivative of the ascending hyperbolic flow
    $\frac{d}{dt}(\cosh(tw) + \sinh(tw)) = w(\cosh(tw) + \sinh(tw))$.
  * `hasDerivAt_cosh_sub_mul_add_sinh`: derivative of the paired product
    $(\cosh(tw) - \sinh(tw))(\cosh(tw) + \sinh(tw))$ vanishes identically.
  * `hasDerivAt_modularFlow_aVec`: Heisenberg equation of motion
    $\frac{d}{dt}\alpha_t(a_i) = -\omega_i \alpha_t(a_i)$.
  * `hasDerivAt_modularFlow_adagVec`: Heisenberg equation of motion
    $\frac{d}{dt}\alpha_t(a_i^\dagger) = \omega_i \alpha_t(a_i^\dagger)$.
-/

open InfoGeometry.Canonical.TopologicalKMSFlow
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Clifford

noncomputable section

namespace InfoGeometry.Canonical.HeisenbergDerivative

/-- The exact continuous derivative of the descending exponential-like hyperbolic flow. -/
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

/-- The exact continuous derivative of the ascending exponential-like hyperbolic flow. -/
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

/-- The paired product of the descending and ascending hyperbolic flows has
identically zero time derivative, reflecting the conservation of the Witt pairing
under the modular boost flow. -/
theorem hasDerivAt_cosh_sub_mul_add_sinh (w t : ℝ) :
    HasDerivAt
      (fun t' => (Real.cosh (t' * w) - Real.sinh (t' * w)) *
                 (Real.cosh (t' * w) + Real.sinh (t' * w)))
      0 t := by
  have hsub := hasDerivAt_cosh_sub_sinh w t
  have hadd := hasDerivAt_cosh_add_sinh w t
  have hmul := HasDerivAt.mul hsub hadd
  convert hmul using 1
  ring

/-- The Heisenberg equation of motion for the Witt annihilation operators:
$\frac{d}{dt} \alpha_t(a_i) = -\omega_i \alpha_t(a_i)$. -/
theorem hasDerivAt_modularFlow_aVec (E μ : Fin 4 → ℝ) (i : Fin 4) (t : ℝ) :
    HasDerivAt (fun t' => boostFun E μ t' (aVec i))
               (-ω E μ i • boostFun E μ t (aVec i)) t := by
  have h_eq : (fun t' => boostFun E μ t' (aVec i)) =
      fun t' => (Real.cosh (t' * ω E μ i) - Real.sinh (t' * ω E μ i)) • aVec i := by
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

/-- The Heisenberg equation of motion for the Witt creation operators:
$\frac{d}{dt} \alpha_t(a_i^\dagger) = \omega_i \alpha_t(a_i^\dagger)$. -/
theorem hasDerivAt_modularFlow_adagVec (E μ : Fin 4 → ℝ) (i : Fin 4) (t : ℝ) :
    HasDerivAt (fun t' => boostFun E μ t' (adagVec i))
               (ω E μ i • boostFun E μ t (adagVec i)) t := by
  have h_eq : (fun t' => boostFun E μ t' (adagVec i)) =
      fun t' => (Real.cosh (t' * ω E μ i) + Real.sinh (t' * ω E μ i)) • adagVec i := by
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
