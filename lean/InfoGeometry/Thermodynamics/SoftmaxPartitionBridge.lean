import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Real

namespace InfoGeometry.Thermodynamics

/-!
# Algebraic correspondence between softmax and Gibbs weights

For a finite nonempty outcome type, this module defines a scaled softmax
distribution and a Gibbs distribution. `AttentionIsThermodynamics` proves
that their weights agree after the parameter substitution
`E = -x` and `β = 1 / sqrt d`, assuming `d > 0`. This is an equality of
finite exponential-family formulas; it does not assert that a transformer
is a physical spin glass.

`LogSumExpIsNegativeFreeEnergy` proves the corresponding scalar identity
between the defined log-sum-exp and free-energy functions. This file does not
prove that attention is the gradient of free energy; derivative statements
belong to the analytic log-sum-exp developments.
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

/-- Under the displayed parameter substitution, the scaled softmax weight
equals the Gibbs weight. -/
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

/-- A scaled log-partition function for the finite score family. -/
noncomputable def LogSumExp (x : n → ℝ) (d : ℝ) : ℝ :=
  sqrt d * log (∑ j, exp (x j / sqrt d))

/-- The Gibbs free-energy expression `-(1 / β) log Z` for the supplied
energy function. -/
noncomputable def FreeEnergy (E : n → ℝ) (β : ℝ) : ℝ :=
  - (1 / β) * log (∑ j, exp (-β * E j))

/-- The two scalar functions are negatives of one another under the same
parameter substitution as `AttentionIsThermodynamics`. -/
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
