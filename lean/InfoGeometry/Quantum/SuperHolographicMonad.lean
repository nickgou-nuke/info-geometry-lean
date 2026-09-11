import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.SuperHolographicMonad

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {A : Type*} [CommRing A] [Algebra ℚ A]

def half : A := algebraMap ℚ A (1 / 2)

def P_vac (X : A) : A := 1 - X^4
def P_sym (X : A) : A := half * (X^4 + X^2)
def P_anti (X : A) : A := half * (X^4 - X^2)

theorem tripartite_completeness (X : A) : 
    P_vac X + P_sym X + P_anti X = 1 := by
  unfold P_vac P_sym P_anti half
  have h_half : algebraMap ℚ A (1 / 2) + algebraMap ℚ A (1 / 2) = 1 := by
    rw [← map_add]
    have : (1 / 2 : ℚ) + (1 / 2 : ℚ) = 1 := by norm_num
    rw [this, map_one]
  calc 1 - X^4 + algebraMap ℚ A (1 / 2) * (X^4 + X^2) + algebraMap ℚ A (1 / 2) * (X^4 - X^2)
    _ = 1 - X^4 + (algebraMap ℚ A (1 / 2) + algebraMap ℚ A (1 / 2)) * X^4 := by ring
    _ = 1 - X^4 + 1 * X^4 := by rw [h_half]
    _ = 1 := by ring

theorem chiral_orthogonality (X : A) (hX : X^5 = X) : 
    P_sym X * P_anti X = 0 := by
  unfold P_sym P_anti
  have h8 : X^8 = X^4 := by
    calc X^8 = X^5 * X^3 := by ring
      _ = X * X^3 := by rw [hX]
      _ = X^4 := by ring
  calc half * (X^4 + X^2) * (half * (X^4 - X^2))
    _ = half * half * (X^8 - X^4) := by ring
    _ = half * half * (X^4 - X^4) := by rw [h8]
    _ = 0 := by ring

def chiralCharge (N_L N_R : ℝ) : ℝ := N_L - N_R

theorem anomaly_free_vacuum (N_L N_R : ℝ) 
    (h_parity_inv : chiralCharge N_L N_R = - chiralCharge N_L N_R) :
    N_L = N_R := by
  unfold chiralCharge at h_parity_inv
  linarith

def loxodromicMap (ξ θ : ℝ) : ℂ := Complex.exp (↑ξ + ↑θ * Complex.I)

theorem loxodromic_confinement (ξ θ : ℝ) 
    (h_unitary : ‖loxodromicMap ξ θ‖ = 1) : 
    ξ = 0 := by
  unfold loxodromicMap at h_unitary
  have h_norm := Complex.norm_exp (↑ξ + ↑θ * Complex.I)
  have h_re : (↑ξ + ↑θ * Complex.I : ℂ).re = ξ := by
    simp [mul_re, I_re, ofReal_re, I_im, ofReal_im]
  rw [h_norm, h_re] at h_unitary
  have h_exp : Real.exp ξ = Real.exp 0 := by rw [h_unitary, Real.exp_zero]
  exact Real.exp_injective h_exp

def spectralParameter (ξ : ℝ) : ℝ := 1 / 2 + ξ

theorem bifurcate_horizon_symmetry (ξ : ℝ) :
    spectralParameter ξ + spectralParameter (-ξ) = 1 := by
  unfold spectralParameter
  ring

/- theorem GRAND_ARITHMETIC_HOLOGRAPHY
    (X : A) (hX : X^5 = X)
    (N_L N_R : ℝ)
    (h_parity : chiralCharge N_L N_R = - chiralCharge N_L N_R)
    (θ : ℝ)
    (h_casimir : ∃ (ξ : ℝ), ξ = chiralCharge N_L N_R ∧ ‖loxodromicMap ξ θ‖ = 1) :
    (P_vac X + P_sym X + P_anti X = 1) ∧
    (P_sym X * P_anti X = 0) ∧
    (N_L = N_R) ∧
    (∀ ξ, ξ = chiralCharge N_L N_R → ξ = 0) ∧
    (∀ ξ, ξ = chiralCharge N_L N_R → spectralParameter ξ = 1 / 2) ∧
    (∀ ξ, spectralParameter ξ + spectralParameter (-ξ) = 1) := by
  rcases h_casimir with ⟨ξ, h_xi_eq, h_unitary⟩
  have h_complete := tripartite_completeness X
  have h_ortho := chiral_orthogonality X hX
  have h_balance := anomaly_free_vacuum N_L N_R h_parity
  have h_xi_zero : ∀ ξ, ξ = chiralCharge N_L N_R → ξ = 0 := by
    intro x hx
    unfold chiralCharge at hx
    linarith [h_balance]
  have h_RH : ∀ ξ, ξ = chiralCharge N_L N_R → spectralParameter ξ = 1 / 2 := by
    intro x hx
    have hx0 := h_xi_zero x hx
    unfold spectralParameter
    rw [hx0, add_zero]
  have h_func := bifurcate_horizon_symmetry
  exact ⟨h_complete, h_ortho, h_balance, h_xi_zero, h_RH, h_func⟩ -/
