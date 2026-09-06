import Mathlib.Tactic

open Real

namespace InfoGeometry.Thermodynamics

/-!
# Softmax and finite Boltzmann readouts

This module proves two elementary finite-sum identities.  It does not define
a transformer, a spin glass, a probability measure, or a gradient-flow
interpretation.
-/

variable {n : Type*} [Fintype n]

/-- A finite softmax-style normalized exponential readout. -/
noncomputable def TransformerSoftmax (x : n → ℝ) (d : ℝ) (i : n) : ℝ :=
  exp (x i / sqrt d) / ∑ j, exp (x j / sqrt d)

/-- A finite Boltzmann-style normalized exponential readout. -/
noncomputable def BoltzmannDistribution (E : n → ℝ) (β : ℝ) (i : n) : ℝ :=
  exp (-β * E i) / ∑ j, exp (-β * E j)

/-- The two readouts coincide under the displayed parameter substitution. -/
theorem AttentionIsThermodynamics (x : n → ℝ) (d : ℝ) (i : n) :
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

/-- A finite log-sum-exp scalar. -/
noncomputable def LogSumExp (x : n → ℝ) (d : ℝ) : ℝ :=
  sqrt d * log (∑ j, exp (x j / sqrt d))

/-- A finite logarithmic partition readout. -/
noncomputable def FreeEnergy (E : n → ℝ) (β : ℝ) : ℝ :=
  - (1 / β) * log (∑ j, exp (-β * E j))

/-- The two finite logarithmic readouts agree under the same substitution. -/
theorem LogSumExpIsNegativeFreeEnergy (x : n → ℝ) (d : ℝ) :
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
