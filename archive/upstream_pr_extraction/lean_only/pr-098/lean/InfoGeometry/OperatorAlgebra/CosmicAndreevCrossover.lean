/-
InfoGeometry/OperatorAlgebra/CosmicAndreevCrossover.lean

Andreev-style conformal crossover carrier.

This module does not assert that the Big Bang is literally an Andreev
reflection. It records the algebraic pattern:

  old crossover datum ↔ new crossover datum

through a closure involution, and proves that the diagonal survives.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.AndreevBoundary

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CosmicAndreevCrossover

open InfoGeometry.OperatorAlgebra.AndreevBoundary
open InfoGeometry.OperatorAlgebra.ClosureInvolution

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Involutivity transports an explicit old-to-new closure equation backwards. -/
theorem closure_newMetric_to_oldNull
    (boundary : AndreevBoundaryDatum V)
    (oldNullData newMetricData : V)
    (hreflection : boundary.closure.theta oldNullData = newMetricData) :
    boundary.closure.theta newMetricData = oldNullData := by
  have h := boundary.closure.theta_involutive oldNullData
  rw [hreflection] at h
  exact h

/-- The sum of explicitly related crossover data lies in the fixed subspace. -/
theorem closure_crossover_diagonal_fixed
    (boundary : AndreevBoundaryDatum V)
    (oldNullData newMetricData : V)
    (hreflection : boundary.closure.theta oldNullData = newMetricData) :
    oldNullData + newMetricData ∈ boundary.closure.Fixed := by
  exact boundary.closure.diagonal_fixed_of_swap hreflection
    (closure_newMetric_to_oldNull boundary oldNullData newMetricData hreflection)

/-- The difference of explicitly related crossover data is anti-fixed. -/
theorem closure_crossover_imbalance_anti_fixed
    (boundary : AndreevBoundaryDatum V)
    (oldNullData newMetricData : V)
    (hreflection : boundary.closure.theta oldNullData = newMetricData) :
    boundary.closure.theta (oldNullData - newMetricData) =
      -(oldNullData - newMetricData) := by
  exact boundary.closure.difference_anti_fixed_of_swap hreflection
    (closure_newMetric_to_oldNull boundary oldNullData newMetricData hreflection)

end InfoGeometry.OperatorAlgebra.CosmicAndreevCrossover
