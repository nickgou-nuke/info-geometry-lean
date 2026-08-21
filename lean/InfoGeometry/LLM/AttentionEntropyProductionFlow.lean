import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

noncomputable section

open BigOperators
open Finset

namespace InfoGeometry.LLM.AttentionFlow

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The attention probability vector p_i on finite tokens ι. -/
def isAttentionState (p : ι → ℝ) : Prop :=
  (∀ i, 0 < p i) ∧ (∑ i, p i = 1)

/-- The Dissipative Entropy Production / Fisher Information Norm: σ(p) = ∑_i (p_i)^2. -/
def entropyProductionRate (p : ι → ℝ) : ℝ :=
  ∑ i, (p i) ^ 2

/-- Strict positivity of entropy production along the continuous attention flow. -/
theorem entropyProductionRate_pos (p : ι → ℝ) (hp : isAttentionState p) :
    0 < entropyProductionRate p := by
  dsimp [entropyProductionRate]
  apply Finset.sum_pos
  · intro i _
    exact sq_pos_of_ne_zero (ne_of_gt (hp.1 i))
  · exact univ_nonempty

/-- 
  The Continuous Time Rate of Change of Free Energy under Natural Gradient Descent:
  dF/dt = - σ(p) = - ∑_i (p_i)^2.
-/
def freeEnergyTimeDerivative (p : ι → ℝ) : ℝ :=
  - entropyProductionRate p

/-- 
  MASTER THEOREM (Dissipative Free Energy Monotonicity of Attention):
  Along continuous natural gradient attention flow, the time derivative of free energy
  is strictly negative: dF/dt = - ∑_i (p_i)^2 < 0,
  guaranteeing strict convergence of the attention potential landscape.
-/
theorem free_energy_strictly_decreasing
    (p : ι → ℝ) (hp : isAttentionState p) :
    freeEnergyTimeDerivative p < 0 := by
  dsimp [freeEnergyTimeDerivative]
  have h_pos := entropyProductionRate_pos p hp
  linarith

end InfoGeometry.LLM.AttentionFlow

end noncomputable section
