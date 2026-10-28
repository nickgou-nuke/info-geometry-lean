/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.FockVacuumAnnihilationBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- The unit in the exterior algebra of the genuine dual is the vacuum state. -/
def vacuumState (R U : Type*) [CommRing R] [AddCommGroup U] [Module R U] :
    ExteriorAlgebra R (U →ₗ[R] R) :=
  1

/-- Native contraction annihilates the unit vacuum. -/
theorem annihilation_vacuum_zero (u : U) :
    (contractionOp (evaluationLinear u)) (vacuumState R U) = 0 := by
  simpa only [vacuumState] using
    (contraction_op_one (R := R) (V := U →ₗ[R] R) (evaluationLinear (R := R) u))

/-- The vacuum definition and its annihilation property. -/
theorem master_fock_vacuum_annihilation_synthesis (u : U) :
    ((vacuumState R U = 1) ∧
     ((contractionOp (evaluationLinear u)) (vacuumState R U) = 0)) :=
  ⟨rfl, annihilation_vacuum_zero u⟩

end InfoGeometry.Canonical.FockVacuumAnnihilationBridge
