import InfoGeometry.Arithmetic.PrimeInformationKMS
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
