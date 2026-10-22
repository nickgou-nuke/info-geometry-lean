/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.CompMul
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Algebraic.CartanExponentialFamily
import InfoGeometry.Canonical.AmariBinarySimplexBridge
import InfoGeometry.Analysis.LogOddsSimplexGeometry
import InfoGeometry.Krein.TomitaMatrixAtom

/-!
# Binary Cartan Massieu specialization

The two-state Cartan chart with parameters `a * u` and `-(a * u)` has
partition function `2 * cosh (a * u)`. Its Massieu potential is an affine
reparameterization of the existing binary Amari Massieu potential, yielding
finite first- and second-derivative formulas. This file makes no claim about a
thermodynamic limit or an operator exponential.
-/

noncomputable section

namespace InfoGeometry.Canonical.BinaryCartanMassieuBridge

open InfoGeometry.Algebraic.CartanExponentialFamily
open scoped BigOperators

abbrev BinaryIndex := Fin 2

def binaryParameters (a u : ℝ) : BinaryIndex → ℝ :=
  ![a * u, -(a * u)]

theorem binaryPartition_eq_two_mul_cosh (a u : ℝ) :
    Z (binaryParameters a u) = 2 * Real.cosh (a * u) := by
  unfold Z binaryParameters
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Real.cosh_eq]
  ring

theorem binaryPartition_pos (a u : ℝ) :
    0 < Z (binaryParameters a u) := by
  exact Z_pos (binaryParameters a u)

theorem binaryMassieu_eq_log_two_mul_cosh (a u : ℝ) :
    Phi (binaryParameters a u) = Real.log (2 * Real.cosh (a * u)) := by
  rw [Phi, binaryPartition_eq_two_mul_cosh]

/-- The Cartan two-sector Massieu potential is the binary Amari potential
at logit `2 * a * u`, minus its affine centering term. -/
theorem binaryMassieu_eq_amariMassieu_sub_linear (a u : ℝ) :
    Phi (binaryParameters a u) =
      InfoGeometry.Canonical.AmariBinarySimplexBridge.massieu (2 * a * u) - a * u := by
  rw [binaryMassieu_eq_log_two_mul_cosh]
  unfold InfoGeometry.Canonical.AmariBinarySimplexBridge.massieu
  have hexp2 : Real.exp (2 * (a * u)) = Real.exp (a * u) * Real.exp (a * u) := by
    rw [show 2 * (a * u) = a * u + a * u by ring, Real.exp_add]
  have hprod :
      2 * Real.cosh (a * u) =
        Real.exp (-(a * u)) * (1 + Real.exp (2 * (a * u))) := by
    rw [Real.cosh_eq, Real.exp_neg, hexp2]
    field_simp [Real.exp_ne_zero (a * u)]
    ring
  calc
    Real.log (2 * Real.cosh (a * u)) =
        Real.log (Real.exp (-(a * u)) * (1 + Real.exp (2 * (a * u)))) := by rw [hprod]
    _ = Real.log (Real.exp (-(a * u))) + Real.log (1 + Real.exp (2 * (a * u))) := by
      rw [Real.log_mul (Real.exp_ne_zero _) (by positivity)]
    _ = Real.log (1 + Real.exp (2 * a * u)) - a * u := by
      rw [Real.log_exp]
      ring_nf

/-- The derivative of the binary Cartan Massieu potential is
`a * tanh (a * u)`. -/
theorem binaryMassieu_hasDerivAt (a u : ℝ) :
    HasDerivAt (fun x : ℝ => Phi (binaryParameters a x))
      (a * Real.tanh (a * u)) u := by
  have hfun :
      (fun x : ℝ => Phi (binaryParameters a x)) =
        (fun x =>
          InfoGeometry.Canonical.AmariBinarySimplexBridge.massieu (2 * a * x) - a * x) := by
    funext x
    exact binaryMassieu_eq_amariMassieu_sub_linear a x
  rw [hfun]
  have harg : HasDerivAt (fun x : ℝ => 2 * a * x) (2 * a) u := by
    simpa [mul_assoc] using (hasDerivAt_id u).const_mul (2 * a)
  have hdiff :
      DifferentiableAt ℝ InfoGeometry.Canonical.AmariBinarySimplexBridge.massieu
        (2 * a * u) := by
    change DifferentiableAt ℝ (fun θ : ℝ => Real.log (1 + Real.exp θ)) (2 * a * u)
    have hinner :
        DifferentiableAt ℝ (fun θ : ℝ => 1 + Real.exp θ) (2 * a * u) := by
      fun_prop
    exact (Real.differentiableAt_log (by positivity)).comp (2 * a * u) hinner
  have hmass :
      HasDerivAt InfoGeometry.Canonical.AmariBinarySimplexBridge.massieu
        (InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic (2 * a * u))
        (2 * a * u) := by
    convert hdiff.hasDerivAt using 1
    rw [InfoGeometry.Canonical.AmariBinarySimplexBridge.deriv_massieu]
  have hlinear : HasDerivAt (fun x : ℝ => a * x) a u := by
    simpa using (hasDerivAt_id u).const_mul a
  have h := (hmass.comp u harg).sub hlinear
  have hlogistic :=
    InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic_eq_half_add_tanh_half
      (2 * a * u)
  have hhalf : (2 * a * u) / 2 = a * u := by ring
  rw [hhalf] at hlogistic
  have hderiv :
      InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic (2 * a * u) * (2 * a) - a =
        a * Real.tanh (a * u) := by
    rw [hlogistic]
    ring
  exact h.congr_deriv hderiv

/-- Scalar derivative readback for the binary Cartan Massieu potential. -/
theorem binaryMassieu_deriv (a u : ℝ) :
    deriv (fun x : ℝ => Phi (binaryParameters a x)) u =
      a * Real.tanh (a * u) :=
  (binaryMassieu_hasDerivAt a u).deriv

/-- The binary Amari Fisher variance in Cartan coordinates is the
hyperbolic susceptibility `((1 - tanh² (a*u))/4)`. -/
theorem amariFisher_two_mul_eq_tanh_susceptibility (a u : ℝ) :
    InfoGeometry.Canonical.AmariBinarySimplexBridge.fisherExp (2 * a * u) =
      (1 - (Real.tanh (a * u)) ^ 2) / 4 := by
  have hlogistic :=
    InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic_eq_half_add_tanh_half
      (2 * a * u)
  have hhalf : (2 * a * u) / 2 = a * u := by ring
  rw [hhalf] at hlogistic
  rw [InfoGeometry.Canonical.AmariBinarySimplexBridge.fisherExp_eq_logistic_mul_complement,
    hlogistic]
  ring

/-- The binary Cartan Massieu Hessian is its one-dimensional Fisher
susceptibility `a² (1 - tanh² (a u))`. -/
theorem binaryMassieu_second_deriv (a u : ℝ) :
    deriv (fun x : ℝ => deriv
      (fun y : ℝ => Phi (binaryParameters a y)) x) u =
        a ^ 2 * (1 - (Real.tanh (a * u)) ^ 2) := by
  have hfirst :
      (fun x : ℝ => deriv
        (fun y : ℝ => Phi (binaryParameters a y)) x) =
      (fun x : ℝ =>
        2 * a * InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic (2 * a * x) - a) := by
    funext x
    rw [binaryMassieu_deriv]
    have hlogistic :=
      InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic_eq_half_add_tanh_half
        (2 * a * x)
    have hhalf : (2 * a * x) / 2 = a * x := by ring
    rw [hhalf] at hlogistic
    rw [hlogistic]
    ring
  rw [hfirst]
  have hcomp :
      deriv (fun x : ℝ =>
        InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic ((2 * a) * x)) u =
        (2 * a) * deriv InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic
          ((2 * a) * u) := by
    simpa only [smul_eq_mul] using
      (deriv_comp_mul_left (2 * a)
        InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic u)
  calc
    deriv (fun x : ℝ =>
        2 * a * InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic (2 * a * x) - a) u =
        (2 * a) * deriv (fun x : ℝ =>
          InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic ((2 * a) * x)) u := by
      rw [deriv_sub_const, deriv_const_mul_field]
    _ = (2 * a) ^ 2 * deriv
        (fun x : ℝ => deriv InfoGeometry.Canonical.AmariBinarySimplexBridge.massieu x)
        (2 * a * u) := by
      rw [hcomp]
      have hsecond :
          deriv InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic (2 * a * u) =
            deriv (fun x : ℝ => deriv
              InfoGeometry.Canonical.AmariBinarySimplexBridge.massieu x) (2 * a * u) := by
        rw [InfoGeometry.Canonical.AmariBinarySimplexBridge.deriv_logistic,
          InfoGeometry.Canonical.AmariBinarySimplexBridge.deriv2_massieu]
      rw [hsecond]
      ring
    _ = (2 * a) ^ 2 *
        InfoGeometry.Canonical.AmariBinarySimplexBridge.fisherExp (2 * a * u) := by
      rw [InfoGeometry.Canonical.AmariBinarySimplexBridge.deriv2_massieu]
    _ = a ^ 2 * (1 - (Real.tanh (a * u)) ^ 2) := by
      rw [amariFisher_two_mul_eq_tanh_susceptibility]
      ring

/-- In Cartan coordinates, the binary Hessian is the Amari Fisher variance
scaled by the square of the coordinate slope. -/
theorem binaryMassieu_second_deriv_eq_scaled_fisher (a u : ℝ) :
    deriv (fun x : ℝ => deriv
      (fun y : ℝ => Phi (binaryParameters a y)) x) u =
        4 * a ^ 2 *
          InfoGeometry.Canonical.AmariBinarySimplexBridge.fisherExp (2 * a * u) := by
  rw [binaryMassieu_second_deriv, amariFisher_two_mul_eq_tanh_susceptibility]
  ring

/-- The binary Cartan Massieu Hessian is the variance of the Krein grading
in the corresponding finite thermal polarization, scaled by the square of
the Cartan coordinate slope. -/
theorem binaryMassieu_second_deriv_eq_thermal_grading_variance (a u : ℝ) :
    deriv (fun x : ℝ => deriv
      (fun y : ℝ => Phi (binaryParameters a y)) x) u =
        a ^ 2 * (1 - (Matrix.trace
          (InfoGeometry.Krein.TomitaMatrixAtom.thermalPolarization
            (Real.tanh (a * u)) * InfoGeometry.Krein.TomitaMatrixAtom.eps)) ^ 2) := by
  rw [binaryMassieu_second_deriv,
    InfoGeometry.Krein.TomitaMatrixAtom.thermalPolarization_grading_expectation]

/-- The binary Cartan Massieu Hessian is strictly positive exactly when its
scale parameter is nonzero. -/
theorem binaryMassieu_second_deriv_pos_iff (a u : ℝ) :
    0 < deriv (fun x : ℝ => deriv
      (fun y : ℝ => Phi (binaryParameters a y)) x) u ↔ a ≠ 0 := by
  rw [binaryMassieu_second_deriv_eq_scaled_fisher]
  constructor
  · intro h ha
    subst a
    norm_num at h
  · intro ha
    exact mul_pos
      (mul_pos (by norm_num : (0 : ℝ) < 4) (sq_pos_of_ne_zero ha))
      (InfoGeometry.Canonical.AmariBinarySimplexBridge.fisherExp_pos (2 * a * u))

/-- The Cartan Hessian equals the Fisher–Rao squared speed of the two
square-root amplitudes along its binary logistic chart. -/
theorem binaryMassieu_hessian_eq_fisherRao_amplitude_speed (a u : ℝ) :
    deriv (fun x : ℝ => deriv
      (fun y : ℝ => Phi (binaryParameters a y)) x) u =
      4 * ((deriv (fun t : ℝ => Real.sqrt
        (InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic (2 * a * t))) u) ^ 2 +
        (deriv (fun t : ℝ => Real.sqrt
          (1 - InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic (2 * a * t))) u) ^ 2) := by
  have hcurve :=
    InfoGeometry.Analysis.LogOddsSimplexGeometry.logistic_curve_amplitude_speed
      (2 * a) u
  calc
    _ = 4 * a ^ 2 *
        InfoGeometry.Canonical.AmariBinarySimplexBridge.fisherExp (2 * a * u) :=
      binaryMassieu_second_deriv_eq_scaled_fisher a u
    _ = (2 * a) ^ 2 *
        InfoGeometry.Canonical.AmariBinarySimplexBridge.fisherExp ((2 * a) * u) := by ring
    _ = 4 * ((deriv (fun t : ℝ => Real.sqrt
          (InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic (2 * a * t))) u) ^ 2 +
        (deriv (fun t : ℝ => Real.sqrt
          (1 - InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic (2 * a * t))) u) ^ 2) := by
      simpa [mul_assoc] using hcurve.symm

theorem binaryPartition_neg_eq (a u : ℝ) :
    Z (binaryParameters a (-u)) = Z (binaryParameters a u) := by
  rw [binaryPartition_eq_two_mul_cosh, binaryPartition_eq_two_mul_cosh]
  have h : a * -u = -(a * u) := by ring
  rw [h, Real.cosh_neg]

theorem binaryMassieu_neg_eq (a u : ℝ) :
    Phi (binaryParameters a (-u)) = Phi (binaryParameters a u) := by
  rw [binaryMassieu_eq_log_two_mul_cosh,
    binaryMassieu_eq_log_two_mul_cosh]
  have h : a * -u = -(a * u) := by ring
  rw [h, Real.cosh_neg]

end InfoGeometry.Canonical.BinaryCartanMassieuBridge
