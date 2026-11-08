/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorLimitExactConnection
import InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
import InfoGeometry.Canonical.Cl11FiniteTraceGNSAction
import InfoGeometry.Canonical.TensorExactCurvatureNonzero
import InfoGeometry.OperatorAlgebra.DerivationGaugeTransport
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# The normalized trace of exact CE curvature on the tensor colimit

The cyclicity proof uses the existing normalized matrix traces and the actual
algebraic colimit.  It imposes no commutativity on the matrix operators.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorExactCurvatureTrace

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Canonical.Cl11FiniteTraceGNSAction
open InfoGeometry.Canonical.Cl11FiniteNormalizedTraceState
open InfoGeometry.Canonical.TensorExactCurvatureNonzero
open InfoGeometry.Canonical.RealStarColimitUniversal
open InfoGeometry.Examples.RealMatrixModeWitness
open InfoGeometry.Geometry.AssociativeGaugeConnection

/-- The existing normalized trace is cyclic on the actual tensor colimit. -/
theorem normalizedTraceLimit_cyclic (X Y : Limit) :
    normalizedTraceLimit (X * Y) = normalizedTraceLimit (Y * X) := by
  induction X, Y using DirectLimit.induction₂ with
  | _ n A B =>
      rw [DirectLimit.mul_def, DirectLimit.mul_def]
      change normalizedTrace n (A * B) = normalizedTrace n (B * A)
      unfold normalizedTrace
      rw [Matrix.trace_mul_comm]

/-- The colimit trace is nonnegative on every adjoint square. -/
theorem normalizedTraceLimit_star_mul_self_nonneg (X : Limit) :
    0 ≤ normalizedTraceLimit (star X * X) := by
  induction X using DirectLimit.induction with
  | _ n A =>
      rw [limit_star_mk, DirectLimit.mul_def]
      change 0 ≤ normalizedTrace n (star A * A)
      exact normalizedTraceState_positive n A

/-- Faithfulness descends from the finite full-matrix trace to the actual
algebraic tensor colimit. -/
theorem normalizedTraceLimit_star_mul_self_eq_zero_iff (X : Limit) :
    normalizedTraceLimit (star X * X) = 0 ↔ X = 0 := by
  induction X using DirectLimit.induction with
  | _ n A =>
      rw [limit_star_mk, DirectLimit.mul_def]
      change normalizedTrace n (star A * A) = 0 ↔ ofStage n A = 0
      rw [normalizedTrace_star_mul_self_eq_zero_iff, ofStage_eq_zero_iff]

/-- The exact CE curvature has zero normalized trace for arbitrary colimit
Leibniz derivation directions. -/
theorem normalizedTraceLimit_exactCurvature (P : Limit)
    (D E : limitDerivationsLane.L) :
    normalizedTraceLimit
      (connectionCurvature limitDerivationsLane
        (exteriorDerivativeZero limitDerivationsLane P) D E) = 0 := by
  rw [limit_exactCurvature_all_directions, map_sub, normalizedTraceLimit_cyclic, sub_self]

/-- The same trace cancellation holds for the explicit inner directions. -/
theorem normalizedTraceLimit_innerExactCurvature (P X Y : Limit) :
    normalizedTraceLimit (limitExactCurvature P X Y) = 0 := by
  exact normalizedTraceLimit_exactCurvature P (limitInnerLieHom X) (limitInnerLieHom Y)

/-- The faithful quadratic trace is invariant under unitary conjugation on
the actual, potentially noncommutative, colimit. -/
theorem normalizedTraceLimit_unitary_conjugate_square (u : unitary Limit) (X : Limit) :
    normalizedTraceLimit
      (star (conjugate (Unitary.toUnits u) X) * conjugate (Unitary.toUnits u) X) =
    normalizedTraceLimit (star X * X) := by
  let e := Unitary.conjStarAlgAut ℝ Limit u
  change normalizedTraceLimit (star (e X) * e X) = _
  rw [← map_star e X, ← map_mul e (star X) X]
  change normalizedTraceLimit
    ((↑(Unitary.toUnits u) : Limit) * (star X * X) *
      (↑((Unitary.toUnits u)⁻¹) : Limit)) = _
  rw [normalizedTraceLimit_cyclic]
  simp only [← mul_assoc, Units.inv_mul, one_mul]

/-- Gauge transport preserves the quadratic curvature readout for every pair
of derivations and every unitary on the actual colimit. -/
theorem normalizedTraceLimit_gauge_curvature_square
    (Γ : OneForm limitDerivationsLane) (u : unitary Limit)
    (D E : limitDerivationsLane.L) :
    normalizedTraceLimit
      (star (connectionCurvature limitDerivationsLane
        (gaugeOneForm limitDerivationsLane Γ (Unitary.toUnits u)) D E) *
        connectionCurvature limitDerivationsLane
          (gaugeOneForm limitDerivationsLane Γ (Unitary.toUnits u)) D E) =
    normalizedTraceLimit
      (star (connectionCurvature limitDerivationsLane Γ D E) *
        connectionCurvature limitDerivationsLane Γ D E) := by
  rw [connectionCurvature_gaugeOneForm]
  exact normalizedTraceLimit_unitary_conjugate_square u _

/-- The dense curvature has zero linear trace but a strictly positive
quadratic trace, witnessing that trace cancellation does not imply flatness. -/
theorem denseMode_curvature_trace_and_positive_square :
    let F := limitExactCurvature (ofStage 2 p) (ofStage 2 x) (ofStage 2 (star x))
    normalizedTraceLimit F = 0 ∧ 0 < normalizedTraceLimit (star F * F) := by
  dsimp only
  constructor
  · exact normalizedTraceLimit_innerExactCurvature _ _ _
  · apply lt_of_le_of_ne (normalizedTraceLimit_star_mul_self_nonneg _)
    intro hz
    apply denseMode_limitExactCurvature_ne_zero
    exact (normalizedTraceLimit_star_mul_self_eq_zero_iff _).mp hz.symm

end InfoGeometry.Canonical.TensorExactCurvatureTrace

end
