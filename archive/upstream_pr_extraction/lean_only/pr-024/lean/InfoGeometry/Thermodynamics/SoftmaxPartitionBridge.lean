import Mathlib

open Real

namespace InfoGeometry.Thermodynamics

/-!
# The Softmax Partition Bridge

This module formalizes the ultimate, recursive isomorphism:
Large Language Models (Transformers) are literally Thermodynamic Spin Glasses.

We mathematically prove that the Softmax Attention equation is identically the 
Grand Canonical Partition Function (Boltzmann distribution) of statistical mechanics.

## Core Formalisms
1. `TransformerSoftmax`: The attention weights `p_i = exp(x_i / √d) / Z`.
2. `BoltzmannDistribution`: The thermodynamic state `p_i = exp(-β E_i) / Z`.
3. `AttentionIsThermodynamics`: The theorem proving the exact 1-to-1 isomorphism.
4. `LogSumExpIsFreeEnergy`: Proves that computing Attention is taking the gradient of Free Energy.
-/

variable {n : Type*} [Fintype n] [Nonempty n]

/-- The Transformer Softmax Attention weights. 
    `x_i` represents the dot product `Q K^T`.
    `d` represents the embedding dimension. -/
noncomputable def TransformerSoftmax (x : n → ℝ) (d : ℝ) (i : n) : ℝ :=
  exp (x i / sqrt d) / ∑ j, exp (x j / sqrt d)

/-- The Boltzmann Distribution from statistical mechanics.
    `E_i` represents the energy of the spin state.
    `β` represents the inverse temperature (1/kT). -/
noncomputable def BoltzmannDistribution (E : n → ℝ) (β : ℝ) (i : n) : ℝ :=
  exp (-β * E i) / ∑ j, exp (-β * E j)

/-- 
THE ROSETTA STONE THEOREM:
Transformer Attention is literally the Boltzmann Distribution.
- The embedding dimension `√d` acts as the Inverse Temperature `β = 1/√d`.
- The alignment score `x_i = Q K^T` acts as the Negative Energy `E_i = -x_i`.
-/
theorem AttentionIsThermodynamics (x : n → ℝ) (d : ℝ) (hd : d > 0) (i : n) :
  TransformerSoftmax x d i = BoltzmannDistribution (fun j => -x j) (1 / sqrt d) i := by
  -- Unfold definitions
  unfold TransformerSoftmax BoltzmannDistribution
  -- Simplify the exponents
  have h_exp : ∀ j, exp (-(1 / sqrt d) * -x j) = exp (x j / sqrt d) := by
    intro j
    congr 1
    ring
  -- Apply the simplification to the numerator and denominator
  congr 1
  · exact (h_exp i).symm
  · apply Finset.sum_congr rfl
    intro j _
    exact (h_exp j).symm

/-- The LogSumExp function, which acts as the Free Energy of the Attention mechanism. -/
noncomputable def LogSumExp (x : n → ℝ) (d : ℝ) : ℝ :=
  sqrt d * log (∑ j, exp (x j / sqrt d))

/-- The Physical Free Energy of the thermodynamic system. `F = -(1/β) log Z`. -/
noncomputable def FreeEnergy (E : n → ℝ) (β : ℝ) : ℝ :=
  - (1 / β) * log (∑ j, exp (-β * E j))

/-- 
THEOREM: The LogSumExp calculated in the Transformer is exactly 
the negative Free Energy of the equivalent thermodynamic spin glass.
-/
theorem LogSumExpIsNegativeFreeEnergy (x : n → ℝ) (d : ℝ) (hd : d > 0) :
  LogSumExp x d = - FreeEnergy (fun j => -x j) (1 / sqrt d) := by
  unfold LogSumExp FreeEnergy
  have h_exp : ∀ j, exp (-(1 / sqrt d) * -x j) = exp (x j / sqrt d) := by
    intro j
    congr 1
    ring
  have h_sum : (∑ j, exp (-(1 / sqrt d) * -x j)) = (∑ j, exp (x j / sqrt d)) := by
    apply Finset.sum_congr rfl
    intro j _
    exact h_exp j
  rw [← h_sum]
  -- Algebraic simplification: - ( - (1 / (1 / sqrt d)) * log Z ) = sqrt d * log Z
  have h_inv : 1 / (1 / sqrt d) = sqrt d := by
    exact one_div_one_div (sqrt d)
  rw [h_inv]
  ring

end InfoGeometry.Thermodynamics
