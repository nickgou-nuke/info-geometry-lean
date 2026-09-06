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

/-- The finite softmax readout is normalized on a nonempty index type. -/
theorem transformerSoftmax_sum_eq_one [Nonempty n]
    (x : n → ℝ) (d : ℝ) :
    ∑ i, TransformerSoftmax x d i = 1 := by
  unfold TransformerSoftmax
  rw [show (∑ i, exp (x i / sqrt d) / ∑ j, exp (x j / sqrt d)) =
      (∑ i, exp (x i / sqrt d)) * (∑ j, exp (x j / sqrt d))⁻¹ by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]]
  exact mul_inv_cancel₀ (by positivity)

/-- Every finite softmax weight is strictly positive on a nonempty index type. -/
theorem transformerSoftmax_pos [Nonempty n]
    (x : n → ℝ) (d : ℝ) (i : n) :
    0 < TransformerSoftmax x d i := by
  unfold TransformerSoftmax
  exact div_pos (Real.exp_pos _) (by positivity)

/-- A finite Boltzmann-style normalized exponential readout. -/
noncomputable def BoltzmannDistribution (E : n → ℝ) (β : ℝ) (i : n) : ℝ :=
  exp (-β * E i) / ∑ j, exp (-β * E j)

/-- The finite Boltzmann readout is normalized when the index type is nonempty. -/
theorem boltzmannDistribution_sum_eq_one [Nonempty n]
    (E : n → ℝ) (β : ℝ) :
    ∑ i, BoltzmannDistribution E β i = 1 := by
  unfold BoltzmannDistribution
  rw [show (∑ i, exp (-β * E i) / ∑ j, exp (-β * E j)) =
      (∑ i, exp (-β * E i)) * (∑ j, exp (-β * E j))⁻¹ by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]]
  exact mul_inv_cancel₀ (by positivity)

/- Every coordinate of the finite Boltzmann readout is strictly positive. -/
theorem boltzmannDistribution_pos [Nonempty n]
    (E : n → ℝ) (β : ℝ) (i : n) :
    0 < BoltzmannDistribution E β i := by
  unfold BoltzmannDistribution
  exact div_pos (Real.exp_pos _) (by positivity)

/- A normalized Boltzmann readout preserves constant value contractions. -/
theorem boltzmannDistribution_constant_expectation [Nonempty n]
    (E : n → ℝ) (β c : ℝ) :
    (∑ i, BoltzmannDistribution E β i * c) = c := by
  rw [← Finset.sum_mul, boltzmannDistribution_sum_eq_one]
  simp

/- Reindexing the finite state space transports the normalized readout. -/
theorem boltzmannDistribution_equivariance
    (E : n → ℝ) (β : ℝ) (sigma : n ≃ n) (i : n) :
    BoltzmannDistribution (E ∘ sigma) β i =
      BoltzmannDistribution E β (sigma i) := by
  unfold BoltzmannDistribution
  have hsum :
      (∑ j, Real.exp (-β * (E ∘ sigma) j)) =
        ∑ j, Real.exp (-β * E j) := by
    simpa [Function.comp_apply] using
      (Equiv.sum_comp sigma (fun j => Real.exp (-β * E j)))
  rw [hsum]
  rfl

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
