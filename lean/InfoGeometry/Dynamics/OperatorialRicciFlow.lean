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

section NonCommOperatorEuler

variable {B : Type*} [Ring B]

/-- One unit-step Euler update by the fixed operator `A` in a possibly noncommutative ring. -/
def operatorEulerStep (A x : B) : B :=
  x * (1 - A)

/-- The state after `n` repeated Euler updates by the same operator. -/
def operatorEulerIterate (A : B) : ℕ → B → B
  | 0, x => x
  | n + 1, x => operatorEulerStep A (operatorEulerIterate A n x)

/-- Exact closed form for repeated Euler updates by `A`: `x * (1 - A)^n`. -/
theorem operatorEulerIterate_eq_pow (A x : B) (n : ℕ) :
    operatorEulerIterate A n x = x * (1 - A) ^ n := by
  induction n with
  | zero => simp [operatorEulerIterate]
  | succ n ih =>
    simp [operatorEulerIterate, operatorEulerStep, ih, pow_succ, mul_assoc]

end NonCommOperatorEuler

end InfoGeometry.Dynamics.OperatorialRicciFlow
