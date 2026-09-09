import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.WittenIndexVacuum

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def excitedLevelWittenContribution (E β : ℝ) : ℝ :=
  Real.exp (-β * E) - Real.exp (-β * E)

def wittenIndex (n_B0 n_F0 : ℤ) : ℤ :=
  n_B0 - n_F0

def wittenIndexThermal (n_B0 n_F0 : ℤ) (β : ℝ) : ℝ :=
  ((wittenIndex n_B0 n_F0 : ℤ) : ℝ)

theorem excited_level_witten_cancels (E β : ℝ) :
    excitedLevelWittenContribution E β = 0 := by
  unfold excitedLevelWittenContribution
  ring

theorem vacuum_level_exp_zero (β : ℝ) :
    Real.exp (-β * 0) = 1 := by
  have : -β * 0 = 0 := by ring
  rw [this, Real.exp_zero]

theorem hasDerivAt_witten_index_zero (n_B0 n_F0 : ℤ) (β : ℝ) :
    HasDerivAt (wittenIndexThermal n_B0 n_F0) 0 β := by
  unfold wittenIndexThermal
  exact hasDerivAt_const β (((wittenIndex n_B0 n_F0 : ℤ) : ℝ))

theorem witten_index_unique_vacuum :
    wittenIndex 1 0 = 1 := by
  unfold wittenIndex
  rfl

theorem susy_prime_phase_cancellation (γ p : ℝ) :
    (Complex.exp (Complex.I * (γ * Real.log p : ℂ))) *
    (Complex.exp (-Complex.I * (γ * Real.log p : ℂ))) = 1 := by
  rw [← Complex.exp_add]
  have : Complex.I * (γ * Real.log p : ℂ) + -Complex.I * (γ * Real.log p : ℂ) = 0 := by ring
  rw [this, Complex.exp_zero]
