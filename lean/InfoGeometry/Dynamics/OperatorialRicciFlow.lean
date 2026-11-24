/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Dynamics.OperatorialRicciFlow

A closed finite algebraic placeholder for operatorial Ricci-flow readback.
-/

noncomputable section

namespace InfoGeometry.Dynamics.OperatorialRicciFlow

/-- Euler step for a discrete flow on an additive group. -/
def eulerStep {E : Type*} [Sub E] (x v : E) : E :=
  x - v

/-- The Euler step is definitionally subtraction by the velocity/defect. -/
theorem eulerStep_eq {E : Type*} [Sub E] (x v : E) :
    eulerStep x v = x - v := by
  rfl

/-- One explicit subtraction step on a carrier with a subtraction operation. -/
def subtractionStep {E : Type*} [Sub E] (x v : E) : E :=
  x - v

/-- The finite step is definitionally subtraction by its supplied increment. -/
theorem subtractionStep_eq {E : Type*} [Sub E] (x v : E) :
    subtractionStep x v = x - v := by
  rfl

end InfoGeometry.Dynamics.OperatorialRicciFlow
