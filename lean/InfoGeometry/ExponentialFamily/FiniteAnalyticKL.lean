/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.ExponentialFamily.KLBregman
import InfoGeometry.Analytic.LogSumExp

/-!
# Analytic KL--Bregman closure for a finite exponential family

The family retains its explicit positive reference distribution `F.base`.
Its partition sum is the already differentiated finite weighted log-sum-exp
partition. Consequently the mean identity needed by `KLBregman` follows from
native calculus, rather than being supplied as an additional compatibility
hypothesis. The same identification gives the centered score and variance.

These are scalar-parameter finite families. No claim about infinite-dimensional
distribution spaces or noncommuting operator exponential families is made here.
-/

namespace InfoGeometry.ExponentialFamily

open scoped BigOperators
open InfoGeometry.Analytic

variable {α : Type*} [Fintype α] [Nonempty α]

omit [Nonempty α] in
/-- The existing partition is the native weighted log-sum-exp function. -/
theorem familyLogPartition_eq_logSumExp (F : FiniteExponentialFamilyData α) :
    familyLogPartition F = logSumExp (fun i => (F.base i).toReal) F.stat := rfl

/-- The actual finite-family log-partition has derivative equal to its mean
sufficient statistic, with the reference distribution kept explicit. -/
theorem hasDerivAt_familyLogPartition
    (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    HasDerivAt (familyLogPartition F) (statMean F θ) θ := by
  rw [familyLogPartition_eq_logSumExp]
  have h := hasDerivAt_logSumExp (fun i => (F.base i).toReal) F.stat F.base_pos θ
  rw [logSumExpMean_eq_weighted_sum _ _ F.base_pos θ] at h
  simpa only [logSumExpPartition, logSumExpWeight,
    familyPartition, statMean, familyDensity] using h

/-- The previously assumed derivative--mean compatibility is a theorem for
every finite family with the existing positive-reference data. -/
theorem statMean_eq_deriv_familyLogPartition
    (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    statMean F θ = deriv (familyLogPartition F) θ :=
  (hasDerivAt_familyLogPartition F θ).deriv.symm

/-- KL equals the Bregman divergence of the actual log-partition, with reversed
parameter order. No derivative--mean premise remains. -/
theorem KLParam_eq_bregman
    (F : FiniteExponentialFamilyData α) (θ η : ℝ) :
    KLParam F θ η = (logPotential F).bregman η θ :=
  KLParam_eq_LogPotential_bregman_of_statMean_eq_deriv F θ η
    (statMean_eq_deriv_familyLogPartition F θ)

/-- The second derivative of the log-partition is the centered statistic
variance under the actual family density. -/
theorem secondDeriv_familyLogPartition_eq_variance
    (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    deriv (deriv (familyLogPartition F)) θ =
      ∑ i, familyDensity F θ i * (F.stat i - statMean F θ) ^ 2 := by
  rw [familyLogPartition_eq_logSumExp]
  have h := logSumExp_secondDeriv_eq_variance
    (fun i => (F.base i).toReal) F.stat F.base_pos θ
  rw [logSumExpVariance_eq_centered _ _ F.base_pos θ] at h
  simpa only [logSumExpPartition, logSumExpWeight,
    familyPartition, familyDensity, statMean] using h

/-- Differentiating a normalized family density gives density times its
centered sufficient statistic. -/
theorem deriv_familyDensity_eq_centered
    (F : FiniteExponentialFamilyData α) (θ : ℝ) (i : α) :
    deriv (fun t => familyDensity F t i) θ =
      familyDensity F θ i * (F.stat i - statMean F θ) := by
  have h := logSumExpWeight_deriv
    (fun j => (F.base j).toReal) F.stat F.base_pos θ i
  rw [logSumExpMean_eq_weighted_sum _ _ F.base_pos θ] at h
  simpa only [logSumExpWeight, logSumExpPartition,
    familyDensity, familyPartition, statMean] using h

end InfoGeometry.ExponentialFamily
