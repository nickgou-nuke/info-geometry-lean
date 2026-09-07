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
  prob := GrandCanonical.gibbsWeight (canonicalParams K) β
  prob_nonneg := GrandCanonical.gibbsWeight_nonneg (canonicalParams K) β
  prob_sum_one := GrandCanonical.gibbsWeight_sum_one (canonicalParams K) β

@[simp] theorem thermalDiagonalQuantumState_prob
    (K : α → ℝ) (β : ℝ) (i : α) :
    (thermalDiagonalQuantumState K β).prob i =
      GrandCanonical.gibbsWeight (canonicalParams K) β i := rfl

theorem diagonalMean_thermal_eq_mean (K : α → ℝ) (β : ℝ) :
    diagonalMean (thermalDiagonalQuantumState K β) K =
      GrandCanonical.mean (canonicalParams K) β := rfl

omit [Nonempty α] in
theorem grandCanonical_variance_eq_finiteGibbsVariance
    (K : α → ℝ) (β : ℝ) :
    GrandCanonical.variance (canonicalParams K) β =
      finiteGibbsVariance (GrandCanonical.gibbsWeight (canonicalParams K) β) K := by
  unfold GrandCanonical.variance finiteGibbsVariance
  rfl

theorem grandCanonical_variance_eq_centered_bkm
    (K : α → ℝ) (β : ℝ) :
    GrandCanonical.variance (canonicalParams K) β =
      bkmMetric (thermalDiagonalQuantumState K β)
        (Matrix.diagonal (fun i => K i - GrandCanonical.mean (canonicalParams K) β))
        (Matrix.diagonal (fun i => K i - GrandCanonical.mean (canonicalParams K) β)) := by
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
      GrandCanonical.secondMoment (canonicalParams K) β := by
  rw [bkmMetric_diagonal_eq_weighted_sum]
  unfold GrandCanonical.secondMoment
  apply Finset.sum_congr rfl
  intro i hi
  simp [thermalDiagonalQuantumState, canonicalParams]
  ring

theorem logPartition_deriv_eq_neg_diagonalMean
    (K : α → ℝ) (β : ℝ) :
    deriv (FinitePartitionCumulantReadback.logPartition K) β =
      -diagonalMean (thermalDiagonalQuantumState K β) K := by
  rw [FinitePartitionCumulantReadback.logPartition_deriv_eq_neg_mean,
    diagonalMean_thermal_eq_mean]

theorem logPartition_hessian_eq_centered_bkm
    (K : α → ℝ) (β : ℝ) :
    GrandCanonical.hessian (canonicalParams K) β =
      bkmMetric (thermalDiagonalQuantumState K β)
        (Matrix.diagonal (fun i => K i - GrandCanonical.mean (canonicalParams K) β))
        (Matrix.diagonal (fun i => K i - GrandCanonical.mean (canonicalParams K) β)) := by
  rw [FinitePartitionCumulantReadback.logPartition_second_deriv_eq_variance]
  exact grandCanonical_variance_eq_centered_bkm K β

theorem logPartition_hessian_nonneg (K : α → ℝ) (β : ℝ) :
    0 ≤ GrandCanonical.hessian (canonicalParams K) β := by
  rw [FinitePartitionCumulantReadback.logPartition_second_deriv_eq_variance]
  exact GrandCanonical.variance_nonneg (canonicalParams K) β

theorem centered_bkm_thermal_nonneg (K : α → ℝ) (β : ℝ) :
    0 ≤ bkmMetric (thermalDiagonalQuantumState K β)
      (Matrix.diagonal (fun i => K i - GrandCanonical.mean (canonicalParams K) β))
      (Matrix.diagonal (fun i => K i - GrandCanonical.mean (canonicalParams K) β)) := by
  rw [← grandCanonical_variance_eq_centered_bkm]
  exact GrandCanonical.variance_nonneg (canonicalParams K) β

theorem logPartition_hessian_pos_of_generator_ne
    (K : α → ℝ) (β : ℝ) {i j : α}
    (hij : K i ≠ K j) :
    0 < GrandCanonical.hessian (canonicalParams K) β := by
  rw [FinitePartitionCumulantReadback.logPartition_second_deriv_eq_variance]
  have hnonneg := GrandCanonical.variance_nonneg (canonicalParams K) β
  rcases lt_or_eq_of_le hnonneg with hpos | heq
  · exact hpos
  · exfalso
    have hconst :=
      (GrandCanonical.variance_eq_zero_iff_energy_eq_mean (canonicalParams K) β).mp heq.symm
    have hi : K i = GrandCanonical.mean (canonicalParams K) β := hconst i
    have hj : K j = GrandCanonical.mean (canonicalParams K) β := hconst j
    exact hij (hi.trans hj.symm)

end InfoGeometry.Canonical.FinitePartitionBKMCumulantBridge
