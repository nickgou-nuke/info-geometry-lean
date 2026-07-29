import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Real Finset

/-- A quantum system with finite energy spectrum E_i and inverse temperature β. -/
structure QuantumSystem (n : Type*) [Fintype n] [DecidableEq n] where
  E : n → ℝ
  β : ℝ
  β_pos : 0 < β

namespace QuantumSystem

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (sys : QuantumSystem n)

/-- Canonical partition function Z(β) = ∑_i exp(-β E_i) -/
def Z : ℝ := ∑ i : n, Real.exp (-sys.β * sys.E i)

/-- Partition function positivity guarantee -/
lemma Z_pos : 0 < sys.Z := by
  dsimp [Z]
  apply Finset.sum_pos
  · intro i _
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- Reduced density matrix eigenvalues: p_i = exp(-β E_i) / Z -/
def p (i : n) : ℝ := Real.exp (-sys.β * sys.E i) / sys.Z

/-- Normalization of reduced state eigenvalues: ∑ p_i = 1 -/
theorem sum_p_eq_one : ∑ i : n, sys.p i = 1 := by
  dsimp [p]
  have h_sum : (∑ i : n, Real.exp (-sys.β * sys.E i) / sys.Z) = (∑ i : n, Real.exp (-sys.β * sys.E i)) / sys.Z := by
    calc (∑ i : n, Real.exp (-sys.β * sys.E i) / sys.Z)
      _ = ∑ i : n, (Real.exp (-sys.β * sys.E i) * (1 / sys.Z)) := by congr 1; ext; ring
      _ = (∑ i : n, Real.exp (-sys.β * sys.E i)) * (1 / sys.Z) := by rw [← Finset.sum_mul]
      _ = (∑ i : n, Real.exp (-sys.β * sys.E i)) / sys.Z := by ring
  rw [h_sum]
  dsimp [Z]
  exact div_self (ne_of_gt sys.Z_pos)

/-- Average thermal energy ⟨E⟩ = ∑_i p_i E_i -/
def avgEnergy : ℝ := ∑ i : n, sys.p i * sys.E i

/-- von Neumann Entanglement Entropy S(ρ_L) = - ∑_i p_i ln(p_i) -/
def vonNeumannEntropy : ℝ := - ∑ i : n, sys.p i * Real.log (sys.p i)

/-- Eigenvalue logarithmic identity: ln(p_i) = -β E_i - ln Z -/
lemma log_p (i : n) : Real.log (sys.p i) = -sys.β * sys.E i - Real.log sys.Z := by
  dsimp [p]
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt sys.Z_pos)]
  rw [Real.log_exp]

/-- Fundamental state entropy relation: S = β ⟨E⟩ + ln Z -/
theorem vonNeumannEntropy_eq_thermalEntropy :
    sys.vonNeumannEntropy = sys.β * sys.avgEnergy + Real.log sys.Z := by
  dsimp [vonNeumannEntropy, avgEnergy]
  have h_log (i : n) : sys.p i * Real.log (sys.p i) =
                       -sys.β * (sys.p i * sys.E i) - sys.p i * Real.log sys.Z := by
    rw [sys.log_p]
    ring
  have h_sum : (∑ i : n, sys.p i * Real.log (sys.p i)) =
               -sys.β * (∑ i : n, sys.p i * sys.E i) - (∑ i : n, sys.p i) * Real.log sys.Z := by
    rw [Finset.sum_congr rfl (fun i _ => h_log i)]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [h_sum, sys.sum_p_eq_one]
  ring

/-- **Helmholtz Free Energy Definition**: F = -ln(Z) / β -/
def freeEnergy : ℝ := - Real.log sys.Z / sys.β

/-- Logarithmic partition relation: ln(Z) = -β * F -/
theorem log_Z_eq_neg_beta_mul_freeEnergy :
    Real.log sys.Z = -sys.β * sys.freeEnergy := by
  dsimp [freeEnergy]
  have hβ : sys.β ≠ 0 := ne_of_gt sys.β_pos
  field_simp

/-- **Main Theorem 1**: S = β * (⟨E⟩ - F) -/
theorem entropy_eq_beta_mul_avgEnergy_sub_freeEnergy :
    sys.vonNeumannEntropy = sys.β * (sys.avgEnergy - sys.freeEnergy) := by
  rw [sys.vonNeumannEntropy_eq_thermalEntropy]
  rw [sys.log_Z_eq_neg_beta_mul_freeEnergy]
  ring

/-- **Main Theorem 2**: Classical formulation F = ⟨E⟩ - T * S where T = 1/β -/
theorem freeEnergy_eq_avgEnergy_sub_temperature_mul_entropy :
    sys.freeEnergy = sys.avgEnergy - (1 / sys.β) * sys.vonNeumannEntropy := by
  have hS := sys.entropy_eq_beta_mul_avgEnergy_sub_freeEnergy
  have hβ : sys.β ≠ 0 := ne_of_gt sys.β_pos
  rw [hS]
  have h1 : (1 / sys.β) * (sys.β * (sys.avgEnergy - sys.freeEnergy)) = (1 / sys.β * sys.β) * (sys.avgEnergy - sys.freeEnergy) := by ring
  rw [h1, one_div_mul_cancel hβ, one_mul]
  ring

end QuantumSystem
