/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Rotary.RotarySpiralBridge
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Differential equation and invertibility of the prescribed planar spiral

This file differentiates the existing `RotarySpiralBridge.loxodromicSpiralMatrix`.
The result is an actual `HasDerivAt` statement for its action on a real vector:
`x' = κ • x + ω • Jx`, with `J = !![0, -1; 1, 0]`.

The exponential scale and constant angular speed are hypotheses encoded in that
existing definition. They are not deduced from a Transformer residual layer,
from attention, or from a general metriplectic flow. The inverse law also makes
clear that exponential contraction does not destroy finite-time invertibility.
-/

noncomputable section

open Matrix
open InfoGeometry.RotarySpiralBridge

namespace InfoGeometry.RotaryAttentionFlow

/-- Real quarter-turn generator used by the differential equation below. -/
def rotationGenerator : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- Anisotropic damping used in the straight-ray counterexample. -/
def anisotropicDamping : Matrix (Fin 2) (Fin 2) ℝ := !![-6, 0; 0, -1]

/-- The prescribed exponential-scale rotation has identity value at zero. -/
theorem loxodromicSpiralMatrix_zero (rate ω : ℝ) :
    loxodromicSpiralMatrix rate ω 0 = 1 := by
  simp [loxodromicSpiralMatrix, ropeRotor_zero_right]

/-- Addition of real times composes the existing exponential-scale rotation. -/
theorem loxodromicSpiralMatrix_add (rate ω s t : ℝ) :
    loxodromicSpiralMatrix rate ω (s + t) =
      loxodromicSpiralMatrix rate ω s * loxodromicSpiralMatrix rate ω t := by
  unfold loxodromicSpiralMatrix
  rw [mul_add, Real.exp_add, ropeRotor_add, smul_mul_smul_comm]

/-- The inverse is the value at negative time, including in the contracting case. -/
theorem loxodromicSpiralMatrix_mul_neg (rate ω t : ℝ) :
    loxodromicSpiralMatrix rate ω t * loxodromicSpiralMatrix rate ω (-t) = 1 := by
  rw [← loxodromicSpiralMatrix_add, add_neg_cancel, loxodromicSpiralMatrix_zero]

/-- Negative time reverses the action on every real vector exactly. -/
theorem loxodromicSpiralMatrix_neg_apply (rate ω t : ℝ) (x : Fin 2 → ℝ) :
    loxodromicSpiralMatrix rate ω (-t) *ᵥ
        (loxodromicSpiralMatrix rate ω t *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← loxodromicSpiralMatrix_add,
    neg_add_cancel, loxodromicSpiralMatrix_zero, Matrix.one_mulVec]

/-- The affine chart of a boosted nonzero null coordinate is well-defined and
turns transverse rotation into the existing planar spiral.

The supplied coordinate action is `u ↦ exp(κ t) u`, `z ↦ R(ω t) z`.
Dividing the transverse coordinate by the null coordinate yields
`z/u ↦ exp(-κ t) R(ω t) (z/u)`. The first conjunct records the domain
condition; the theorem does not use totalized division to include the chart
boundary `u = 0`, nor does it construct a full Lorentz action.
-/
theorem boosted_null_chart_eq_loxodromicSpiralMatrix
    (κ ω t u : ℝ) (z : Fin 2 → ℝ) (hu : u ≠ 0) :
    Real.exp (κ * t) * u ≠ 0 ∧
      (Real.exp (κ * t) * u)⁻¹ • (ropeRotor ω t *ᵥ z) =
        loxodromicSpiralMatrix κ ω t *ᵥ (u⁻¹ • z) := by
  refine ⟨mul_ne_zero (Real.exp_ne_zero _) hu, ?_⟩
  unfold loxodromicSpiralMatrix
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
  congr 1
  rw [_root_.mul_inv_rev, neg_mul, Real.exp_neg, mul_comm]

/-- The exact real vector ODE of `exp(κ t) R(ω t) x₀`.

The minus sign in the existing matrix's damping parameter is made explicit:
`loxodromicSpiralMatrix (-κ) ω t = exp(κ t) • ropeRotor ω t`.
This proves the ODE for the prescribed path; it does not assert that an
arbitrary Transformer update has this form.
-/
theorem hasDerivAt_loxodromicSpiralMatrix_mulVec
    (κ ω t : ℝ) (x₀ : Fin 2 → ℝ) :
    HasDerivAt (fun s : ℝ => loxodromicSpiralMatrix (-κ) ω s *ᵥ x₀)
      (κ • (loxodromicSpiralMatrix (-κ) ω t *ᵥ x₀) +
        ω • (rotationGenerator *ᵥ
          (loxodromicSpiralMatrix (-κ) ω t *ᵥ x₀))) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (κ * s))
      (Real.exp (κ * t) * κ) t :=
    (Real.hasDerivAt_exp (κ * t)).comp t (hasDerivAt_const_mul κ)
  have hc : HasDerivAt (fun s : ℝ => Real.cos (s * ω))
      (-Real.sin (t * ω) * ω) t :=
    (hasDerivAt_mul_const (x := t) ω).cos
  have hs : HasDerivAt (fun s : ℝ => Real.sin (s * ω))
      (Real.cos (t * ω) * ω) t :=
    (hasDerivAt_mul_const (x := t) ω).sin
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert he.mul ((hc.mul_const (x₀ 0)).sub (hs.mul_const (x₀ 1))) using 1
    · ext s
      simp [loxodromicSpiralMatrix, ropeRotor, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
      ring
    · simp [loxodromicSpiralMatrix, ropeRotor, rotationGenerator, dotProduct,
        Fin.sum_univ_two]
      ring
  · convert he.mul ((hs.mul_const (x₀ 0)).add (hc.mul_const (x₀ 1))) using 1
    · ext s
      simp [loxodromicSpiralMatrix, ropeRotor, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
      ring
    · simp [loxodromicSpiralMatrix, ropeRotor, rotationGenerator, dotProduct,
        Fin.sum_univ_two]
      ring

/-- The corresponding ordinary derivative is the linear rotation-dilation field. -/
theorem deriv_loxodromicSpiralMatrix_mulVec
    (κ ω t : ℝ) (x₀ : Fin 2 → ℝ) :
    deriv (fun s : ℝ => loxodromicSpiralMatrix (-κ) ω s *ᵥ x₀) t =
      κ • (loxodromicSpiralMatrix (-κ) ω t *ᵥ x₀) +
        ω • (rotationGenerator *ᵥ
          (loxodromicSpiralMatrix (-κ) ω t *ᵥ x₀)) :=
  (hasDerivAt_loxodromicSpiralMatrix_mulVec κ ω t x₀).deriv

/-- Nonzero rotation plus anisotropic damping can have a straight invariant ray.
The matrix is `diag(-6,-1) + 2J`; the exhibited eigenvector prevents a universal
claim that a rotation term and a dissipative term force every orbit to spiral. -/
theorem anisotropic_damping_rotation_radial_eigenvector :
    (anisotropicDamping + (2 : ℝ) • rotationGenerator) *ᵥ ![1, -2] =
      (-2 : ℝ) • ![1, -2] := by
  ext i
  fin_cases i <;> norm_num [anisotropicDamping, rotationGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The anisotropic damping in the counterexample does not commute with the
rotation generator. Scalar damping, used in the prescribed spiral, does. -/
theorem anisotropic_damping_rotation_noncommute :
    anisotropicDamping * rotationGenerator ≠ rotationGenerator * anisotropicDamping := by
  intro h
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
  norm_num [anisotropicDamping, rotationGenerator, Matrix.mul_apply, Fin.sum_univ_two] at h01

end InfoGeometry.RotaryAttentionFlow
