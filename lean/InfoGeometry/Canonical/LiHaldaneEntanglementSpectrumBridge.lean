import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Real Finset

namespace LiHaldane

/-- Bipartite density matrix spectrum p_i > 0 normalized to ∑ p_i = 1. -/
structure EntanglementSpectrum (n : Type*) [Fintype n] [DecidableEq n] where
  p : n → ℝ             -- Eigenvalues of reduced density matrix ρ_A
  p_pos : ∀ i, 0 < p i
  p_le_one : ∀ i, p i ≤ 1
  sum_p : ∑ i : n, p i = 1

namespace EntanglementSpectrum

variable {n : Type*} [Fintype n] [DecidableEq n] (spec : EntanglementSpectrum n)

/-- Entanglement Spectrum Energy Levels ξ_i = -ln(p_i) -/
def entanglementEnergy (i : n) : ℝ :=
  - Real.log (spec.p i)

/-- **Theorem**: Entanglement energy levels are non-negative for p_i ≤ 1: ξ_i ≥ 0. -/
theorem entanglement_energy_nonneg (i : n) : 0 ≤ spec.entanglementEnergy i := by
  dsimp [entanglementEnergy]
  have hp : 0 ≤ spec.p i := le_of_lt (spec.p_pos i)
  have h1 : spec.p i ≤ 1 := spec.p_le_one i
  have hlog : Real.log (spec.p i) ≤ 0 := Real.log_nonpos hp h1
  linarith

/-- Entanglement Entropy S_ent = ∑_i p_i ξ_i = - ∑_i p_i ln(p_i) -/
def vonNeumannEntropy : ℝ :=
  ∑ i : n, spec.p i * spec.entanglementEnergy i

/-- **Theorem**: Entanglement entropy is non-negative: S_ent ≥ 0. -/
theorem entropy_nonneg : 0 ≤ spec.vonNeumannEntropy := by
  dsimp [vonNeumannEntropy]
  apply Finset.sum_nonneg
  intro i _
  have hp : 0 ≤ spec.p i := le_of_lt (spec.p_pos i)
  have he : 0 ≤ spec.entanglementEnergy i := spec.entanglement_energy_nonneg i
  exact mul_nonneg hp he

/-- Li-Haldane CFT Edge State Spectrum Level Matching Δξ_i = ξ_i - ξ_0. -/
def cftEdgeEnergyGap (i i0 : n) : ℝ :=
  spec.entanglementEnergy i - spec.entanglementEnergy i0

/-- **Theorem**: Low-lying entanglement energy gap identity: Δξ_i = ln(p_0 / p_i). -/
theorem cft_edge_energy_gap_log (i i0 : n) :
    spec.cftEdgeEnergyGap i i0 = Real.log (spec.p i0 / spec.p i) := by
  dsimp [cftEdgeEnergyGap, entanglementEnergy]
  rw [Real.log_div (ne_of_gt (spec.p_pos i0)) (ne_of_gt (spec.p_pos i))]
  ring

end EntanglementSpectrum

end LiHaldane
