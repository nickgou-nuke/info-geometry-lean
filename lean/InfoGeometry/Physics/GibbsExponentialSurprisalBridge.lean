/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic
import InfoGeometry.ExponentialFamily.Class
import InfoGeometry.Topology.FiniteGibbsFisherBridge
import InfoGeometry.Physics.StateFamilyBKMBridge

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Physics.GibbsExponentialSurprisalBridge

open Finset
open InfoGeometry.Topology.FiniteGibbsFisherBridge
open InfoGeometry.Physics.StateFamilyBKM

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def gibbsPartition (K : ι → ℝ) : ℝ := ∑ i, Real.exp (-K i)

theorem gibbsPartition_pos (K : ι → ℝ) : 0 < gibbsPartition K := by
  unfold gibbsPartition
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

theorem gibbsPartition_ne_zero (K : ι → ℝ) : gibbsPartition K ≠ 0 :=
  ne_of_gt (gibbsPartition_pos K)

def gibbsProbability (K : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (-K i) / gibbsPartition K

theorem gibbsProbability_pos (K : ι → ℝ) (i : ι) :
    0 < gibbsProbability K i :=
  div_pos (Real.exp_pos _) (gibbsPartition_pos K)

theorem gibbsProbability_nonneg (K : ι → ℝ) (i : ι) :
    0 ≤ gibbsProbability K i :=
  le_of_lt (gibbsProbability_pos K i)

theorem gibbsProbability_sum_one (K : ι → ℝ) :
    ∑ i, gibbsProbability K i = 1 := by
  unfold gibbsProbability gibbsPartition
  rw [← Finset.sum_div]
  exact div_self (gibbsPartition_ne_zero K)

def gibbsSurprisal (K : ι → ℝ) (i : ι) : ℝ :=
  -Real.log (gibbsProbability K i)

theorem gibbsSurprisal_eq (K : ι → ℝ) (i : ι) :
    gibbsSurprisal K i = K i + Real.log (gibbsPartition K) := by
  unfold gibbsSurprisal gibbsProbability
  rw [Real.log_div (ne_of_gt (Real.exp_pos _))
    (gibbsPartition_ne_zero K), Real.log_exp]
  ring

theorem gibbsProbability_eq_exp_neg_surprisal (K : ι → ℝ) (i : ι) :
    gibbsProbability K i = Real.exp (-gibbsSurprisal K i) := by
  rw [gibbsSurprisal_eq]
  rw [neg_add, Real.exp_add, Real.exp_neg]
  have hZ : Real.exp (-Real.log (gibbsPartition K)) =
      (gibbsPartition K)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (gibbsPartition_pos K)]
  rw [hZ]
  unfold gibbsProbability
  rw [Real.exp_neg]
  ring

def gibbsExpectation (K : ι → ℝ) : ℝ :=
  finiteGibbsMean (gibbsProbability K) K

def gibbsEntropy (K : ι → ℝ) : ℝ :=
  ∑ i, gibbsProbability K i * gibbsSurprisal K i

theorem gibbsEntropy_eq_expectation_add_logPartition (K : ι → ℝ) :
    gibbsEntropy K = gibbsExpectation K + Real.log (gibbsPartition K) := by
  unfold gibbsEntropy gibbsExpectation finiteGibbsMean
  simp_rw [gibbsSurprisal_eq, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, gibbsProbability_sum_one]
  ring

def gibbsDiagonalQuantumState (K : ι → ℝ) : DiagonalQuantumState ι where
  prob := gibbsProbability K
  prob_nonneg := gibbsProbability_nonneg K
  prob_sum_one := gibbsProbability_sum_one K

@[simp] theorem gibbsDiagonalQuantumState_prob (K : ι → ℝ) (i : ι) :
    (gibbsDiagonalQuantumState K).prob i = gibbsProbability K i := rfl

theorem diagonalMean_gibbs_eq_expectation (K : ι → ℝ) :
    diagonalMean (gibbsDiagonalQuantumState K) K = gibbsExpectation K := rfl

theorem gibbsVariance_eq_secondMoment_sub_mean_sq (K : ι → ℝ) :
    finiteGibbsVariance (gibbsProbability K) K =
      (∑ i, gibbsProbability K i * K i ^ 2) -
        (gibbsExpectation K) ^ 2 := by
  simpa [gibbsExpectation] using
    finiteGibbsVariance_eq_usual (gibbsProbability K) K
      (gibbsProbability_sum_one K)

theorem gibbsVariance_nonneg (K : ι → ℝ) :
    0 ≤ finiteGibbsVariance (gibbsProbability K) K :=
  finiteGibbsVariance_nonnegative _ _ (gibbsProbability_nonneg K)

end InfoGeometry.Physics.GibbsExponentialSurprisalBridge
