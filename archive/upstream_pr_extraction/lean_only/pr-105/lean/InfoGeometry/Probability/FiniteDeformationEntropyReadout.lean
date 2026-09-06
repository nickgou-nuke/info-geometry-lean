import InfoGeometry.Analysis.DeformationNormalizationGauge
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Probability.FiniteDeformationEntropyReadout

open scoped BigOperators
open InfoGeometry.Analysis.DeformationNormalizationGauge

variable {X : Type*} [Fintype X] [Nonempty X]

/-- Partition sum of a finite unnormalized positive weight. -/
def partitionFunction
    (weight : X → ℝ) : ℝ :=
  ∑ x, weight x

/-- Finite distribution obtained by dividing a weight by its partition sum. -/
def normalizedDistribution
    (weight : X → ℝ)
    (x : X) : ℝ :=
  weight x / partitionFunction weight

/-- Normalized expectation of the primitive unnormalized surprisal. -/
def expectedUnnormalizedSurprisal
    (weight : X → ℝ) : ℝ :=
  ∑ x,
    normalizedDistribution weight x *
      unnormalizedSurprisal weight x

/-- Entropy readout formed from the normalized pointwise surprisal. -/
def normalizedEntropy
    (weight : X → ℝ) : ℝ :=
  ∑ x,
    normalizedDistribution weight x *
      normalizedSurprisal weight
        (partitionFunction weight) x

/-- A finite sum of strictly positive weights is strictly positive. -/
theorem partitionFunction_pos
    (weight : X → ℝ)
    (hw : ∀ x : X, 0 < weight x) :
    0 < partitionFunction weight := by
  unfold partitionFunction
  exact Finset.sum_pos
    (fun x _ => hw x)
    Finset.univ_nonempty

/-- The normalized finite distribution sums to one. -/
theorem sum_normalizedDistribution
    (weight : X → ℝ)
    (hw : ∀ x : X, 0 < weight x) :
    ∑ x, normalizedDistribution weight x = 1 := by
  have hZ :
      partitionFunction weight ≠ 0 :=
    (partitionFunction_pos weight hw).ne'
  unfold normalizedDistribution
  calc
    ∑ x : X, weight x / partitionFunction weight =
        (∑ x : X, weight x) / partitionFunction weight := by
      symm
      simpa using
        (Finset.sum_div
          (s := (Finset.univ : Finset X))
          (f := weight)
          (a := partitionFunction weight))
    _ = partitionFunction weight / partitionFunction weight := by
      rfl
    _ = 1 := div_self hZ

/--
Finite normalized entropy equals the normalized expectation of primitive
surprisal plus the scalar normalization gauge `log Z`.
-/
theorem normalizedEntropy_eq_expected_add_logPartition
    (weight : X → ℝ)
    (hw : ∀ x : X, 0 < weight x) :
    normalizedEntropy weight =
      expectedUnnormalizedSurprisal weight +
        Real.log (partitionFunction weight) := by
  have hZ :
      0 < partitionFunction weight :=
    partitionFunction_pos weight hw
  unfold normalizedEntropy expectedUnnormalizedSurprisal
  simp_rw [normalizedSurprisal_eq_unnormalized_add_log_of_pos
    weight (partitionFunction weight) _ (hw _) hZ]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [sum_normalizedDistribution weight hw]
  ring

/-- Expanded finite Shannon-entropy decomposition. -/
theorem finite_shannon_entropy_decomposition
    (weight : X → ℝ)
    (hw : ∀ x : X, 0 < weight x) :
    (∑ x,
        normalizedDistribution weight x *
          (-Real.log (normalizedDistribution weight x))) =
      (∑ x,
          normalizedDistribution weight x *
            (-Real.log (weight x))) +
        Real.log (partitionFunction weight) := by
  simpa [normalizedEntropy, expectedUnnormalizedSurprisal,
    normalizedSurprisal, normalizedWeight,
    unnormalizedSurprisal, normalizedDistribution] using
    normalizedEntropy_eq_expected_add_logPartition weight hw

end InfoGeometry.Probability.FiniteDeformationEntropyReadout
