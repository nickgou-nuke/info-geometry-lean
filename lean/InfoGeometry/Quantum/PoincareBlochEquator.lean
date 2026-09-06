import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.PoincareBlochEquator

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def stokesCircularAsymmetry (ξ : ℝ) : ℝ :=
  Real.tanh ξ

def isEquatorialBlochState (ξ : ℝ) : Prop :=
  stokesCircularAsymmetry ξ = 0

def vacuumZeroPointEnergy : ℝ := 1 / 2

theorem stokes_asymmetry_zero_iff (ξ : ℝ) :
    stokesCircularAsymmetry ξ = 0 ↔ ξ = 0 := by
  unfold stokesCircularAsymmetry
  rw [Real.tanh_eq_sinh_div_cosh]
  have h_cosh_pos : 0 < Real.cosh ξ := Real.cosh_pos ξ
  have h_cosh_nz : Real.cosh ξ ≠ 0 := ne_of_gt h_cosh_pos
  constructor
  · intro h
    have h_sinh : Real.sinh ξ = 0 := by
      have : Real.sinh ξ / Real.cosh ξ * Real.cosh ξ = 0 * Real.cosh ξ := by rw [h]
      rw [div_mul_cancel₀ (Real.sinh ξ) h_cosh_nz, zero_mul] at this
      exact this
    rw [Real.sinh_eq] at h_sinh
    have h_sub : Real.exp ξ - Real.exp (-ξ) = 0 := by linarith
    have h_eq : Real.exp ξ = Real.exp (-ξ) := sub_eq_zero.mp h_sub
    have h_exp_inj := Real.exp_injective h_eq
    linarith
  · intro h
    rw [h, Real.sinh_zero, zero_div]

theorem poincare_equator_critical_line (σ : ℝ)
    (h_equator : isEquatorialBlochState (σ - 1/2)) :
    σ = 1 / 2 := by
  unfold isEquatorialBlochState at h_equator
  have h_zero : σ - 1 / 2 = 0 := (stokes_asymmetry_zero_iff (σ - 1 / 2)).mp h_equator
  linarith

theorem vacuum_energy_equals_critical_pole :
    vacuumZeroPointEnergy = 1 / 2 := rfl
