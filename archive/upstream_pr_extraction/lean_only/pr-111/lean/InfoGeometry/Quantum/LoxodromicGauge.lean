import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.LoxodromicGauge

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def loxodromicMap (ξ θ : ℝ) : ℂ :=
  Complex.exp (↑ξ + ↑θ * Complex.I)

theorem loxodromic_factorization (ξ θ : ℝ) :
    loxodromicMap ξ θ = ((Real.exp ξ : ℝ) : ℂ) * Complex.exp (↑θ * Complex.I) := by
  unfold loxodromicMap
  rw [Complex.exp_add]
  have h : Complex.exp (↑ξ : ℂ) = ((Real.exp ξ : ℝ) : ℂ) := (Complex.ofReal_exp ξ).symm
  rw [h]

theorem loxodromic_scale_factor (ξ θ : ℝ) :
    ‖loxodromicMap ξ θ‖ = Real.exp ξ := by
  unfold loxodromicMap
  have h : (↑ξ + ↑θ * Complex.I : ℂ).re = ξ := by
    simp [mul_re, I_re, ofReal_re, I_im, ofReal_im]
  have h_norm := Complex.norm_exp (↑ξ + ↑θ * Complex.I)
  rw [h_norm, h]

theorem unitary_loxodromic_confinement (ξ θ : ℝ) :
    ‖loxodromicMap ξ θ‖ = 1 ↔ ξ = 0 := by
  rw [loxodromic_scale_factor]
  constructor
  · intro h
    have h_exp : Real.exp ξ = Real.exp 0 := by rw [h, Real.exp_zero]
    exact Real.exp_injective h_exp
  · intro h
    rw [h, Real.exp_zero]

theorem riemann_critical_line_loxodromic (σ θ : ℝ) 
    (h_unitary : ‖loxodromicMap (σ - 1/2) θ‖ = 1) :
    σ = 1 / 2 := by
  have h_zero : σ - 1 / 2 = 0 := (unitary_loxodromic_confinement (σ - 1/2) θ).mp h_unitary
  linarith

theorem grand_loxodromic_gauge_synthesis (ξ θ σ : ℝ) 
    (h_unitary : ‖loxodromicMap (σ - 1/2) θ‖ = 1) :
    (loxodromicMap ξ θ = ((Real.exp ξ : ℝ) : ℂ) * Complex.exp (↑θ * Complex.I)) ∧
    (‖loxodromicMap ξ θ‖ = Real.exp ξ) ∧
    (‖loxodromicMap ξ θ‖ = 1 ↔ ξ = 0) ∧
    (σ = 1 / 2) :=
  ⟨loxodromic_factorization ξ θ,
   loxodromic_scale_factor ξ θ,
   unitary_loxodromic_confinement ξ θ,
   riemann_critical_line_loxodromic σ θ h_unitary⟩
