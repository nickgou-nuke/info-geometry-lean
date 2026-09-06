/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Canonical.FinitePartitionCumulantReadback
import InfoGeometry.Physics.StateFamilyBKMBridge
import InfoGeometry.Topology.FiniteGibbsFisherBridge

noncomputable section
open scoped BigOperators

namespace InfoGeometry.Canonical.FinitePartitionBKMCumulantBridge

open InfoGeometry.GrandCanonical
open InfoGeometry.Canonical.FinitePartitionCumulantReadback
open InfoGeometry.Topology.FiniteGibbsFisherBridge
open InfoGeometry.Physics.StateFamilyBKM

variable {α : Type*} [Fintype α] [Nonempty α]
local instance : DecidableEq α := Classical.decEq α

def thermalDiagonalQuantumState (K : α → ℝ) (β : ℝ) :
    DiagonalQuantumState α where
  prob := GrandCanonical.gibbsWeight K β
  prob_nonneg := GrandCanonical.gibbsWeight_nonneg K β
  prob_sum_one := GrandCanonical.gibbsWeight_sum_one K β

@[simp] theorem thermalDiagonalQuantumState_prob
    (K : α → ℝ) (β : ℝ) (i : α) :
    (thermalDiagonalQuantumState K β).prob i =
      GrandCanonical.gibbsWeight K β i := rfl

theorem diagonalMean_thermal_eq_mean (K : α → ℝ) (β : ℝ) :
    diagonalMean (thermalDiagonalQuantumState K β) K =
      GrandCanonical.mean K β := rfl

theorem grandCanonical_variance_eq_finiteGibbsVariance
    (K : α → ℝ) (β : ℝ) :
    GrandCanonical.variance K β =
      finiteGibbsVariance (GrandCanonical.gibbsWeight K β) K := by
  unfold GrandCanonical.variance finiteGibbsVariance
  rfl

theorem grandCanonical_variance_eq_centered_bkm
    (K : α → ℝ) (β : ℝ) :
    GrandCanonical.variance K β =
      bkmMetric (thermalDiagonalQuantumState K β)
        (Matrix.diagonal (fun i => K i - GrandCanonical.mean K β))
        (Matrix.diagonal (fun i => K i - GrandCanonical.mean K β)) := by
  rw [grandCanonical_variance_eq_finiteGibbsVariance]
  have hcov := diagonalCovariance_self_eq_finiteGibbsVariance
    (thermalDiagonalQuantumState K β) K
  change finiteGibbsVariance
    (thermalDiagonalQuantumState K β).prob K = _
  rw [← hcov]
  simpa [diagonalMean_thermal_eq_mean] using
    diagonalCovariance_eq_bkm_centered
      (thermalDiagonalQuantumState K β) K K

theorem bkmMetric_thermal_generator_eq_secondMoment
    (K : α → ℝ) (β : ℝ) :
    bkmMetric (thermalDiagonalQuantumState K β)
        (Matrix.diagonal K) (Matrix.diagonal K) =
      GrandCanonical.secondMoment K β := by
  rw [bkmMetric_diagonal_eq_weighted_sum]
  unfold GrandCanonical.secondMoment
  apply Finset.sum_congr rfl
  intro i hi
  simp [thermalDiagonalQuantumState, GrandCanonicalParams.energy]
  ring

theorem logPartition_deriv_eq_neg_diagonalMean
    (K : α → ℝ) (β : ℝ) :
    deriv (FinitePartitionCumulantReadback.logPartition K) β =
      -diagonalMean (thermalDiagonalQuantumState K β) K := by
  rw [FinitePartitionCumulantReadback.logPartition_deriv_eq_neg_mean,
    diagonalMean_thermal_eq_mean]

theorem logPartition_hessian_eq_centered_bkm
    (K : α → ℝ) (β : ℝ) :
    GrandCanonical.hessian K β =
      bkmMetric (thermalDiagonalQuantumState K β)
        (Matrix.diagonal (fun i => K i - GrandCanonical.mean K β))
        (Matrix.diagonal (fun i => K i - GrandCanonical.mean K β)) := by
  rw [FinitePartitionCumulantReadback.logPartition_second_deriv_eq_variance]
  exact grandCanonical_variance_eq_centered_bkm K β

theorem logPartition_hessian_nonneg (K : α → ℝ) (β : ℝ) :
    0 ≤ GrandCanonical.hessian K β := by
  rw [FinitePartitionCumulantReadback.logPartition_second_deriv_eq_variance]
  exact GrandCanonical.variance_nonneg K β

theorem centered_bkm_thermal_nonneg (K : α → ℝ) (β : ℝ) :
    0 ≤ bkmMetric (thermalDiagonalQuantumState K β)
      (Matrix.diagonal (fun i => K i - GrandCanonical.mean K β))
      (Matrix.diagonal (fun i => K i - GrandCanonical.mean K β)) := by
  rw [← grandCanonical_variance_eq_centered_bkm]
  exact GrandCanonical.variance_nonneg K β

theorem logPartition_hessian_pos_of_generator_ne
    (K : α → ℝ) (β : ℝ) {i j : α}
    (hij : K i ≠ K j) :
    0 < GrandCanonical.hessian K β := by
  rw [FinitePartitionCumulantReadback.logPartition_second_deriv_eq_variance]
  exact GrandCanonical.variance_pos_of_energy_ne K β hij

end InfoGeometry.Canonical.FinitePartitionBKMCumulantBridge
