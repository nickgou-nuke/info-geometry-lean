import InfoGeometry.Probability.FiniteDeformationEntropyReadout

noncomputable section

namespace InfoGeometry.Probability.FiniteGibbsDeformationReadout

open scoped BigOperators
open InfoGeometry.Analysis.DeformationNormalizationGauge
open InfoGeometry.Probability.FiniteDeformationEntropyReadout

variable {X : Type*}

/-- Finite Gibbs weight `exp (-β E(x))`. -/
def gibbsWeight
    (energy : X → ℝ)
    (β : ℝ)
    (x : X) : ℝ :=
  Real.exp (-β * energy x)

/-- Finite Gibbs partition function. -/
def gibbsPartition
    [Fintype X]
    (energy : X → ℝ)
    (β : ℝ) : ℝ :=
  partitionFunction (gibbsWeight energy β)

/-- Normalized finite Gibbs distribution. -/
def gibbsDistribution
    [Fintype X]
    (energy : X → ℝ)
    (β : ℝ)
    (x : X) : ℝ :=
  normalizedDistribution (gibbsWeight energy β) x

/-- Expected energy in the normalized finite Gibbs distribution. -/
def meanEnergy
    [Fintype X]
    (energy : X → ℝ)
    (β : ℝ) : ℝ :=
  ∑ x, gibbsDistribution energy β x * energy x

/-- Shannon entropy of the normalized finite Gibbs distribution. -/
def gibbsEntropy
    [Fintype X]
    (energy : X → ℝ)
    (β : ℝ) : ℝ :=
  ∑ x,
    gibbsDistribution energy β x *
      (-Real.log (gibbsDistribution energy β x))

/-- Finite Gibbs weights are strictly positive. -/
theorem gibbsWeight_pos
    (energy : X → ℝ)
    (β : ℝ)
    (x : X) :
    0 < gibbsWeight energy β x :=
  Real.exp_pos _

/-- The finite Gibbs partition function is strictly positive. -/
theorem gibbsPartition_pos
    [Fintype X]
    [Nonempty X]
    (energy : X → ℝ)
    (β : ℝ) :
    0 < gibbsPartition energy β :=
  partitionFunction_pos
    (gibbsWeight energy β)
    (gibbsWeight_pos energy β)

/-- The normalized Gibbs distribution sums to one. -/
theorem sum_gibbsDistribution
    [Fintype X]
    [Nonempty X]
    (energy : X → ℝ)
    (β : ℝ) :
    ∑ x, gibbsDistribution energy β x = 1 :=
  sum_normalizedDistribution
    (gibbsWeight energy β)
    (gibbsWeight_pos energy β)

/-- Primitive Gibbs-weight surprisal is `β E(x)`. -/
theorem gibbsWeight_surprisal
    (energy : X → ℝ)
    (β : ℝ)
    (x : X) :
    -Real.log (gibbsWeight energy β x) =
      β * energy x := by
  unfold gibbsWeight
  rw [Real.log_exp]
  ring

/-- Normalized Gibbs surprisal is `β E(x) + log Z`. -/
theorem gibbs_normalizedSurprisal
    [Fintype X]
    [Nonempty X]
    (energy : X → ℝ)
    (β : ℝ)
    (x : X) :
    -Real.log (gibbsDistribution energy β x) =
      β * energy x +
        Real.log (gibbsPartition energy β) := by
  have hZ :
      partitionFunction (gibbsWeight energy β) ≠ 0 :=
    (partitionFunction_pos
      (gibbsWeight energy β)
      (gibbsWeight_pos energy β)).ne'
  unfold gibbsDistribution normalizedDistribution gibbsPartition
  rw [Real.log_div
    (ne_of_gt (gibbsWeight_pos energy β x))
    hZ]
  have hw := gibbsWeight_surprisal energy β x
  linarith

/-- Finite Gibbs entropy is `β ⟨E⟩ + log Z`. -/
theorem gibbsEntropy_eq
    [Fintype X]
    [Nonempty X]
    (energy : X → ℝ)
    (β : ℝ) :
    gibbsEntropy energy β =
      β * meanEnergy energy β +
        Real.log (gibbsPartition energy β) := by
  unfold gibbsEntropy meanEnergy
  simp_rw [gibbs_normalizedSurprisal]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [sum_gibbsDistribution]
  have hsum :
      (∑ x, gibbsDistribution energy β x * (β * energy x)) =
        β * ∑ x, gibbsDistribution energy β x * energy x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  ring

/-- Finite Gibbs free energy at inverse temperature `β`. -/
def gibbsFreeEnergy
    [Fintype X]
    (energy : X → ℝ)
    (β : ℝ) : ℝ :=
  meanEnergy energy β -
    β⁻¹ * gibbsEntropy energy β

/-- Finite Gibbs free energy equals `-β⁻¹ log Z` for nonzero `β`. -/
theorem gibbsFreeEnergy_eq_neg_logPartition
    [Fintype X]
    [Nonempty X]
    (energy : X → ℝ)
    (β : ℝ)
    (hβ : β ≠ 0) :
    gibbsFreeEnergy energy β =
      -β⁻¹ * Real.log (gibbsPartition energy β) := by
  unfold gibbsFreeEnergy
  rw [gibbsEntropy_eq]
  field_simp [hβ]
  ring

end InfoGeometry.Probability.FiniteGibbsDeformationReadout
