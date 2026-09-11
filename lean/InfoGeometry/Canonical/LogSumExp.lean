import InfoGeometry.ExponentialFamily.Analytic.LogSumExp
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.LogSumExp

Canonical facade for finite log-sum-exp potentials and scaled Gibbs/OT bridges.
-/

namespace InfoGeometry.Canonical.LogSumExp

export InfoGeometry.Analytic (
  logSumExpPartition
  logSumExp
  logSumExpWeight
  logSumExpMoment1
  logSumExpMoment2
  logSumExpMean
  logSumExpSecondMoment
  logSumExpVariance
  logSumExpScaledPartition
  logSumExpScaled
  logSumExpScaledWeight
  logSumExpScaledMean
  logSumExpScaledKL
  logSumExpScaledBregman
  logSumExpScaledEntropicTransportObjective
  logSumExpScaledEntropicTransportPotentialGap
  logSumExpScaledEntropicTransportObjective_eq
  logSumExpScaledEntropicTransportPotentialGap_eq
  logSumExp_sum_pos
  logSumExpScaledPartition_pos
  logSumExpWeight_sum_one
  logSumExpWeight_pos
  logSumExpScaledWeight_sum_one
  logSumExpScaledWeight_pos
)

@[simp] theorem logSumExp_eq_log_partition
    {ι : Type _} [Fintype ι] (w a : ι → ℝ) (θ : ℝ) :
    logSumExp w a θ = Real.log (logSumExpPartition w a θ) := rfl

end InfoGeometry.Canonical.LogSumExp
