import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.AnomalyTubuleStability
import InfoGeometry.Algebra.WittProjectiveClosureHonest

open InfoGeometry.OperatorAlgebra.AnomalyTubuleStability
open InfoGeometry.Algebra.WittProjectiveClosureHonest

/--
A concrete Lean proof instance demonstrating that the Weyl anomaly variation is
strictly non-zero for the Virasoro operator geometry outside the projective
closure, for example at level `m = 2`.
-/
def VirasoroLevelTwoAnomaly : WeylAnomaly ℝ where
  D := 1
  conformalVariation x := x
  zetaResidue _ := 0
  determinantVariation := (anomalyFactor 2 : ℝ)
  determinantVariation_nonzero := by
    unfold anomalyFactor
    norm_num

lemma VirasoroLevelTwoAnomaly_nonzero : (anomalyFactor 2 : ℝ) ≠ 0 := by
  -- Evaluate the anomalyFactor at m = 2
  unfold anomalyFactor
  norm_num
