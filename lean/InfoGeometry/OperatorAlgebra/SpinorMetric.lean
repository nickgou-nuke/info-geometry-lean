import InfoGeometry.Canonical.CStarMatrixTowerIsometry
import InfoGeometry.QuantumGeometry.SLDLyapunov

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SpinorMetric

open CStarStateColimit.Native
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.CStarMatrixTowerIsometry
open scoped ComplexOrder

variable {Algebra : Type*} [CStarAlgebra Algebra]
variable [PartialOrder Algebra] [StarOrderedRing Algebra]

def helstromMetric (state : State Algebra) (first second : selfAdjoint Algebra) : ℝ :=
  (state.functional ((1 / 2 : ℂ) •
    ((first : Algebra) * second + (second : Algebra) * first))).re

def buresMetric (state : State Algebra) (first second : selfAdjoint Algebra) : ℝ :=
  (1 / 4 : ℝ) * helstromMetric state first second

theorem helstromMetric_symm (state : State Algebra) (first second : selfAdjoint Algebra) :
    helstromMetric state first second = helstromMetric state second first := by
  unfold helstromMetric
  rw [add_comm ((first : Algebra) * second)]

theorem helstromMetric_self (state : State Algebra) (score : selfAdjoint Algebra) :
    helstromMetric state score score =
      (state.functional (star (score : Algebra) * score)).re := by
  have half_double (element : Algebra) : (1 / 2 : ℂ) • (element + element) = element := by
    rw [← two_smul ℂ element, smul_smul]
    norm_num
  unfold helstromMetric
  rw [half_double, score.property]

theorem helstromMetric_nonneg (state : State Algebra) (score : selfAdjoint Algebra) :
    0 ≤ helstromMetric state score score := by
  rw [helstromMetric_self]
  exact CStarStateColimit.PositiveState.gns_state_pos state.functional score

theorem buresMetric_symm (state : State Algebra) (first second : selfAdjoint Algebra) :
    buresMetric state first second = buresMetric state second first := by
  unfold buresMetric
  rw [helstromMetric_symm]

theorem buresMetric_nonneg (state : State Algebra) (score : selfAdjoint Algebra) :
    0 ≤ buresMetric state score score :=
  mul_nonneg (by norm_num) (helstromMetric_nonneg state score)

theorem finite_trace_metric_positive (stage : ℕ)
    (score : selfAdjoint (CStarMatrixStage stage)) (nonzero : (score : CStarMatrixStage stage) ≠ 0) :
    0 < helstromMetric (cstarMatrixTraceState stage) score score := by
  rw [helstromMetric_self]
  exact cstarMatrixTraceState_strictly_positive stage score nonzero

theorem finite_trace_bures_positive (stage : ℕ)
    (score : selfAdjoint (CStarMatrixStage stage)) (nonzero : (score : CStarMatrixStage stage) ≠ 0) :
    0 < buresMetric (cstarMatrixTraceState stage) score score :=
  mul_pos (by norm_num) (finite_trace_metric_positive stage score nonzero)

end InfoGeometry.OperatorAlgebra.SpinorMetric
