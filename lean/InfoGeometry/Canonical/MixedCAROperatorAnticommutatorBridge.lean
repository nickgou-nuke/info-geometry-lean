/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.MixedCAROperatorAnticommutatorBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- The actual mixed creation-contraction anticommutator on exterior forms. -/
def mixedCARAnticommutator (u : U) (alpha : U →ₗ[R] R)
    (omega : ExteriorAlgebra R (U →ₗ[R] R)) : ExteriorAlgebra R (U →ₗ[R] R) :=
  (contractionOp (evaluationLinear u)) (creationOp alpha omega) +
  creationOp alpha ((contractionOp (evaluationLinear u)) omega)

/-- Native contraction and creation realize the evaluation CAR on every form. -/
theorem mixed_car_operator_identity (u : U) (alpha : U →ₗ[R] R)
    (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    mixedCARAnticommutator u alpha omega = alpha u • omega := by
  simpa only [mixedCARAnticommutator, creationOp, evaluation_linear_apply] using
    (contraction_op_mixed_car (R := R) (V := U →ₗ[R] R)
      (evaluationLinear (R := R) u) alpha omega)

/-- The scalar evaluation identity, preserved for existing consumers. -/
theorem mixed_car_evaluation_bridge (u : U) (alpha : U →ₗ[R] R)
    (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    (evaluationLinear u alpha) • omega = alpha u • omega :=
  rfl

/-- The original evaluation compatibility packet retains its statement. -/
theorem master_mixed_car_operator_anticommutator_synthesis
    (u : U) (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    (evaluationLinear u alpha = alpha u) ∧
    ((evaluationLinear u alpha) • omega = alpha u • omega) :=
  ⟨rfl, rfl⟩

end InfoGeometry.Canonical.MixedCAROperatorAnticommutatorBridge
