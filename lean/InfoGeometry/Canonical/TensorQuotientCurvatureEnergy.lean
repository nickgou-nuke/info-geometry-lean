/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorQuotientOppositeModes
import InfoGeometry.Canonical.TensorTangentCurvatureGeometry

/-! # Faithful trace energy of tangent quotient curvature

The exact quotient curvature has zero linear trace but its adjoint-square
trace is faithful and unitarily invariant. The dense noncommuting witness
has strictly positive energy, equal to a concrete finite-stage matrix trace.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorQuotientCurvatureEnergy

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.TensorCurvatureTangentQuotient
open InfoGeometry.Canonical.TensorTangentCurvatureGeometry
open InfoGeometry.Canonical.TensorExactCurvatureTrace
open InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
open InfoGeometry.Canonical.Cl11FiniteNormalizedTraceState
open InfoGeometry.Canonical.Cl11FiniteTraceGNSAction
open InfoGeometry.Canonical.TensorQuotientActionWitness
open InfoGeometry.Canonical.TensorQuotientOppositeModes
open InfoGeometry.Examples.RealMatrixModeWitness
open InfoGeometry.Geometry.AssociativeGaugeConnection

/-- The faithful quadratic trace of the descended curvature. -/
def quotientCurvatureEnergy (P : Limit)
    (u v : LimitDeriv ⧸ (cutEvaluation P).ker) : ℝ :=
  normalizedTraceLimit (star (quotientCurvature P u v) * quotientCurvature P u v)

/-- The energy is nonnegative and vanishes exactly on a zero curvature. -/
theorem quotientCurvatureEnergy_nonneg_and_faithful (P : Limit)
    (u v : LimitDeriv ⧸ (cutEvaluation P).ker) :
    0 ≤ quotientCurvatureEnergy P u v ∧
      (quotientCurvatureEnergy P u v = 0 ↔ quotientCurvature P u v = 0) := by
  exact ⟨normalizedTraceLimit_star_mul_self_nonneg _,
    normalizedTraceLimit_star_mul_self_eq_zero_iff _⟩

/-- Unitary conjugation preserves the quadratic curvature trace. -/
theorem quotientCurvatureEnergy_unitary (P : Limit)
    (u v : LimitDeriv ⧸ (cutEvaluation P).ker) (g : unitary Limit) :
    normalizedTraceLimit
      (star (conjugate (Unitary.toUnits g) (quotientCurvature P u v)) *
        conjugate (Unitary.toUnits g) (quotientCurvature P u v)) =
      quotientCurvatureEnergy P u v :=
  normalizedTraceLimit_unitary_conjugate_square g _

/-- The dense opposite-weight curvature has zero linear trace but strictly
positive faithful quadratic energy. -/
theorem dense_quotient_trace_and_energy :
    normalizedTraceLimit (quotientCurvature (ofStage 2 p) denseQuotient denseQuotientAdjoint) = 0 ∧
      0 < quotientCurvatureEnergy (ofStage 2 p) denseQuotient denseQuotientAdjoint := by
  constructor
  · exact quotientCurvature_trace_zero _ _ _
  · apply lt_of_le_of_ne (quotientCurvatureEnergy_nonneg_and_faithful _ _ _).1
    intro hz
    exact dense_opposite_quotient_curvature.2
      ((quotientCurvatureEnergy_nonneg_and_faithful _ _ _).2.mp hz.symm)

/-- The positive colimit energy equals the normalized trace of the actual
full stage-two matrix commutator's adjoint square. -/
theorem dense_quotient_energy_eq_stage :
    quotientCurvatureEnergy (ofStage 2 p) denseQuotient denseQuotientAdjoint =
      normalizedTrace 2 (star (x * star x - star x * x) * (x * star x - star x * x)) := by
  unfold quotientCurvatureEnergy
  rw [dense_opposite_quotient_curvature.1, ← ofStage_star, ← map_mul]
  rfl

end InfoGeometry.Canonical.TensorQuotientCurvatureEnergy

end
