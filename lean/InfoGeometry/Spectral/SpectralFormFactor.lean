import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Spectral.SpectralFormFactor

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def spectralFormFactor (τ : ℝ) : ℝ :=
  if |τ| < 1 then |τ| else 1

theorem sff_at_zero :
    spectralFormFactor 0 = 0 := by
  unfold spectralFormFactor
  simp

theorem sff_even (τ : ℝ) :
    spectralFormFactor (-τ) = spectralFormFactor τ := by
  unfold spectralFormFactor
  rw [abs_neg]

theorem sff_ramp (τ : ℝ) (h_nonneg : 0 ≤ τ) (h_lt : τ < 1) :
    spectralFormFactor τ = τ := by
  unfold spectralFormFactor
  have h_abs : |τ| = τ := abs_of_nonneg h_nonneg
  rw [h_abs]
  simp [h_lt]
