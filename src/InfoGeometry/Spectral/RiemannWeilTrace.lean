import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Spectral.RiemannWeilTrace

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def primeOrbitWeight (p : ℕ) (m : ℕ) : ℝ :=
  Real.log (p : ℝ) / (Real.rpow (p : ℝ) ((m : ℝ) / 2))

def primePhaseHolonomy (p : ℕ) (m : ℕ) (γ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((γ * (m : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ))

def monochromaticSpectralMode (γ τ : ℝ) : ℝ :=
  2 * Real.cos (γ * τ)

theorem prime_orbit_weight_pos (p : ℕ) (m : ℕ) (hp : 2 ≤ p) (hm : 1 ≤ m) :
    0 < primeOrbitWeight p m := by
  unfold primeOrbitWeight
  have hp_pos : 0 < (p : ℝ) := by positivity
  have h_log : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  have h_rpow : 0 < Real.rpow (p : ℝ) ((m : ℝ) / 2) := Real.rpow_pos_of_pos hp_pos _
  exact div_pos h_log h_rpow

theorem prime_phase_holonomy_unitary (p : ℕ) (m : ℕ) (γ : ℝ) :
    ‖primePhaseHolonomy p m γ‖ = 1 := by
  unfold primePhaseHolonomy
  have h_re : (Complex.I * ((γ * (m : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ)).re = 0 := by
    simp only [mul_re, I_re, ofReal_re, I_im, ofReal_im, mul_zero, zero_mul, sub_self]
  have h_norm := Complex.norm_exp (Complex.I * ((γ * (m : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ))
  rw [h_re, Real.exp_zero] at h_norm
  exact h_norm

theorem prime_phase_holonomy_multiplicative (p : ℕ) (m₁ m₂ : ℕ) (γ : ℝ) :
    primePhaseHolonomy p (m₁ + m₂) γ =
    primePhaseHolonomy p m₁ γ * primePhaseHolonomy p m₂ γ := by
  unfold primePhaseHolonomy
  rw [← Complex.exp_add]
  have : Complex.I * ((γ * ((m₁ + m₂ : ℕ) : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) =
         Complex.I * ((γ * (m₁ : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) +
         Complex.I * ((γ * (m₂ : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this]

theorem monochromatic_spectral_mode_even (γ τ : ℝ) :
    monochromaticSpectralMode (-γ) τ = monochromaticSpectralMode γ τ := by
  unfold monochromaticSpectralMode
  have : -γ * τ = - (γ * τ) := by ring
  rw [this, Real.cos_neg]
