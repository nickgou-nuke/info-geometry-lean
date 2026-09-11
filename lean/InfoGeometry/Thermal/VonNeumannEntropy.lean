import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Thermal.VonNeumannEntropy

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def probVacuum (p : ℕ) (β : ℝ) : ℝ :=
  1 / (1 + Real.rpow (p : ℝ) (-β))

def probOccupied (p : ℕ) (β : ℝ) : ℝ :=
  Real.rpow (p : ℝ) (-β) / (1 + Real.rpow (p : ℝ) (-β))

def vonNeumannEntropy (p : ℕ) (β : ℝ) : ℝ :=
  Real.log (1 + Real.rpow (p : ℝ) (-β)) +
  β * Real.log (p : ℝ) / (1 + Real.rpow (p : ℝ) β)

theorem prob_sum_eq_one (p : ℕ) (β : ℝ) (hp : 2 ≤ p) :
    probVacuum p β + probOccupied p β = 1 := by
  unfold probVacuum probOccupied
  have hp_pos : 0 < (p : ℝ) := by positivity
  have h_rpow_pos : 0 < Real.rpow (p : ℝ) (-β) := Real.rpow_pos_of_pos hp_pos _
  have h_den : 1 + Real.rpow (p : ℝ) (-β) ≠ 0 := by linarith
  have h_sum : 1 / (1 + Real.rpow (p : ℝ) (-β)) + Real.rpow (p : ℝ) (-β) / (1 + Real.rpow (p : ℝ) (-β)) =
               (1 + Real.rpow (p : ℝ) (-β)) / (1 + Real.rpow (p : ℝ) (-β)) := by ring
  rw [h_sum, div_self h_den]

end
end InfoGeometry.Thermal.VonNeumannEntropy
