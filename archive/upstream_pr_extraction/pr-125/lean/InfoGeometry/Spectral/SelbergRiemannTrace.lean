import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Spectral.SelbergRiemannTrace

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def primitiveGeodesicLength (p : ℝ) : ℝ :=
  Real.log p

def selbergHyperbolicWeight (p : ℝ) (k : ℕ) : ℝ :=
  (Real.log p) / (2 * Real.sinh ((k : ℝ) * Real.log p / 2))

def riemannWeilWeight (p : ℝ) (k : ℕ) : ℝ :=
  (Real.log p) / Real.exp ((k : ℝ) * Real.log p / 2)

def spectralHarmonicTerm (γ p : ℝ) : ℝ :=
  Real.cos (γ * Real.log p)

theorem primitive_geodesic_length_pos (p : ℝ) (hp : 2 ≤ p) :
    0 < primitiveGeodesicLength p := by
  unfold primitiveGeodesicLength
  have : 1 < p := by linarith
  exact Real.log_pos this

theorem selberg_hyperbolic_weight_pos (p : ℝ) (k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    0 < selbergHyperbolicWeight p k := by
  unfold selbergHyperbolicWeight
  have h_ln_pos : 0 < Real.log p := by
    have : 1 < p := by linarith
    exact Real.log_pos this
  have h_k_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have h_arg_pos : 0 < (k : ℝ) * Real.log p / 2 := by
    have : 0 < (k : ℝ) * Real.log p := mul_pos h_k_pos h_ln_pos
    linarith
  have h_sinh_pos : 0 < Real.sinh ((k : ℝ) * Real.log p / 2) := by
    rw [Real.sinh_eq]
    have h_lt : Real.exp (- ((k : ℝ) * Real.log p / 2)) < Real.exp ((k : ℝ) * Real.log p / 2) :=
      Real.exp_lt_exp.mpr (by linarith)
    linarith
  have h_den_pos : 0 < 2 * Real.sinh ((k : ℝ) * Real.log p / 2) := by linarith
  exact div_pos h_ln_pos h_den_pos

theorem prime_power_exponential_identity (p : ℝ) (k : ℕ) (hp : 0 < p) :
    Real.exp ((k : ℝ) * Real.log p / 2) = (Real.exp (Real.log p)) ^ ((k : ℝ) / 2) := by
  rw [← Real.exp_mul]
  have : Real.log p * ((k : ℝ) / 2) = (k : ℝ) * Real.log p / 2 := by ring
  rw [this]

theorem spectral_harmonic_bounded (γ p : ℝ) :
    |spectralHarmonicTerm γ p| ≤ 1 := by
  unfold spectralHarmonicTerm
  exact abs_le.mpr ⟨by linarith [Real.cos_le_one (γ * Real.log p), Real.neg_one_le_cos (γ * Real.log p)],
                    Real.cos_le_one (γ * Real.log p)⟩

theorem spectral_harmonic_even (γ p : ℝ) :
    spectralHarmonicTerm (-γ) p = spectralHarmonicTerm γ p := by
  unfold spectralHarmonicTerm
  have : -γ * Real.log p = - (γ * Real.log p) := by ring
  rw [this, Real.cos_neg]

theorem grand_selberg_riemann_trace_synthesis
    (p γ : ℝ) (k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (0 < primitiveGeodesicLength p) ∧
    (0 < selbergHyperbolicWeight p k) ∧
    (|spectralHarmonicTerm γ p| ≤ 1) ∧
    (spectralHarmonicTerm (-γ) p = spectralHarmonicTerm γ p) :=
  ⟨primitive_geodesic_length_pos p hp,
   selberg_hyperbolic_weight_pos p k hp hk,
   spectral_harmonic_bounded γ p,
   spectral_harmonic_even γ p⟩
