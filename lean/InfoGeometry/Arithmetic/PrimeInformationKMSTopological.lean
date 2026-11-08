import InfoGeometry.Arithmetic.PrimeInformationKMS
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Topological finite prime KMS readouts

The arithmetic owner supplies finite-cutoff Boltzmann normalization.  This
companion exposes the same partition and probability functions as continuous
maps in inverse temperature.  No infinite Euler product or analytic
continuation is introduced.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeInformationKMS

open FinitePrimeInformationKMSPacket (boltzmannWeight)

/-- Finite prime partition function on a mode set. -/
def partition (modes : Finset ℕ) (beta : ℝ) : ℝ :=
  ∑ p ∈ modes, boltzmannWeight beta p

/-- The partition function is positive on a nonempty mode set. -/
theorem partition_pos (modes : Finset ℕ) (beta : ℝ) (h_nonempty : modes.Nonempty) :
    0 < partition modes beta := by
  unfold partition boltzmannWeight
  exact Finset.sum_pos
    (fun p _ => Real.exp_pos _)
    h_nonempty

/-- Normalized prime probability on a mode set. -/
def normalizedProbability (modes : Finset ℕ) (beta : ℝ) (p : ℕ) : ℝ :=
  boltzmannWeight beta p / partition modes beta

/-- The normalized finite probabilities sum to one. -/
theorem normalizedProbability_sum_eq_one (modes : Finset ℕ) (beta : ℝ) (h_nonempty : modes.Nonempty) :
    ∑ p ∈ modes, normalizedProbability modes beta p = 1 := by
  unfold normalizedProbability
  have hZne : partition modes beta ≠ 0 := (partition_pos modes beta h_nonempty).ne'
  calc
    ∑ p ∈ modes, boltzmannWeight beta p / partition modes beta =
      (∑ p ∈ modes, boltzmannWeight beta p) / partition modes beta := by
        symm
        exact Finset.sum_div (s := modes) (f := fun p => boltzmannWeight beta p) (a := partition modes beta)
    _ = 1 := div_self hZne

noncomputable def partitionContinuousMap
    (modes : Finset ℕ) : C(ℝ, ℝ) :=
  ContinuousMap.mk
    (partition modes)
    (by
      unfold partition boltzmannWeight
      refine continuous_finset_sum modes ?_
      intro p hp
      fun_prop)

@[simp] theorem partitionContinuousMap_apply
    (modes : Finset ℕ) (beta : ℝ) :
    partitionContinuousMap modes beta = partition modes beta :=
  rfl

noncomputable def normalizedProbabilityContinuousMap
    (modes : Finset ℕ) (h_nonempty : modes.Nonempty) (p : ℕ) : C(ℝ, ℝ) :=
  ContinuousMap.mk
    (fun beta => normalizedProbability modes beta p)
    (by
      unfold normalizedProbability boltzmannWeight
      apply Continuous.div
      · fun_prop
      · exact (partitionContinuousMap modes).continuous
      · intro beta
        exact (partition_pos modes beta h_nonempty).ne')

@[simp] theorem normalizedProbabilityContinuousMap_apply
    (modes : Finset ℕ) (h_nonempty : modes.Nonempty) (p : ℕ) (beta : ℝ) :
    normalizedProbabilityContinuousMap modes h_nonempty p beta =
      normalizedProbability modes beta p :=
  rfl

theorem normalizedProbabilityContinuousMap_sum_eq_one
    (modes : Finset ℕ) (h_nonempty : modes.Nonempty) (beta : ℝ) :
    ∑ p ∈ modes, normalizedProbabilityContinuousMap modes h_nonempty p beta = 1 := by
  simpa only [normalizedProbabilityContinuousMap_apply] using
    normalizedProbability_sum_eq_one modes beta h_nonempty

end InfoGeometry.Arithmetic.PrimeInformationKMS
