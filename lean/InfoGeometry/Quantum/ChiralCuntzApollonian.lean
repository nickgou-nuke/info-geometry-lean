import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.ChiralCuntzApollonian

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def chiralCuntzLeftPhase (γ ξ θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((γ / 2) * (ξ + θ) : ℝ) : ℂ))

def chiralCuntzRightPhase (γ ξ θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((γ / 2) * (ξ - θ) : ℝ) : ℂ))

def chiralPrimeOperator (γ ξ θ : ℝ) : ℂ :=
  chiralCuntzLeftPhase γ ξ θ * (chiralCuntzRightPhase γ ξ θ)⁻¹

def tiltCoordinateGenerator (ξ θ : ℝ) : ℝ :=
  ((ξ + θ) + (ξ - θ)) / 2

def shiftCoordinateGenerator (ξ θ : ℝ) : ℝ :=
  ((ξ + θ) - (ξ - θ)) / 2

theorem tilt_generator_eq_rapidity (ξ θ : ℝ) :
    tiltCoordinateGenerator ξ θ = ξ := by
  unfold tiltCoordinateGenerator
  ring

theorem shift_generator_eq_angle (ξ θ : ℝ) :
    shiftCoordinateGenerator ξ θ = θ := by
  unfold shiftCoordinateGenerator
  ring

theorem chiral_prime_operator_eq_angular_phase (γ ξ θ : ℝ) :
    chiralPrimeOperator γ ξ θ = Complex.exp (Complex.I * ((γ * θ : ℝ) : ℂ)) := by
  unfold chiralPrimeOperator chiralCuntzLeftPhase chiralCuntzRightPhase
  have h_inv : (Complex.exp (Complex.I * (((γ / 2) * (ξ - θ) : ℝ) : ℂ)))⁻¹ =
               Complex.exp (- (Complex.I * (((γ / 2) * (ξ - θ) : ℝ) : ℂ))) :=
    (Complex.exp_neg (Complex.I * (((γ / 2) * (ξ - θ) : ℝ) : ℂ))).symm
  rw [h_inv, ← Complex.exp_add]
  have h_arg : Complex.I * (((γ / 2) * (ξ + θ) : ℝ) : ℂ) +
               - (Complex.I * (((γ / 2) * (ξ - θ) : ℝ) : ℂ)) =
               Complex.I * ((γ * θ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h_arg]

theorem chiral_prime_operator_unitary (γ ξ θ : ℝ) :
    ‖chiralPrimeOperator γ ξ θ‖ = 1 := by
  rw [chiral_prime_operator_eq_angular_phase]
  have h_re : (Complex.I * ((γ * θ : ℝ) : ℂ)).re = 0 := by
    simp only [mul_re, I_re, ofReal_re, I_im, ofReal_im, mul_zero, zero_mul, sub_self]
  have h_norm := Complex.norm_exp (Complex.I * ((γ * θ : ℝ) : ℂ))
  rw [h_re, Real.exp_zero] at h_norm
  exact h_norm

theorem chiral_prime_geodesic_phase (γ ξ p : ℝ) :
    chiralPrimeOperator γ ξ (Real.log p) =
    Complex.exp (Complex.I * ((γ * Real.log p : ℝ) : ℂ)) := by
  rw [chiral_prime_operator_eq_angular_phase]
