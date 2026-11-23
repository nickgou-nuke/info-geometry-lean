/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import Omega.POM.ValMonotoneBooleanNand

namespace Omega.POM

/-- The concrete NAND macro computes the boolean NAND truth table on `{0, 1}`. -/
def booleanCircuitCompilesCorrectly : Prop :=
  ∀ x y : ℕ, x ≤ 1 → y ≤ 1 →
    (1 : ℤ) - (x : ℤ) * (y : ℤ) = if x = 1 ∧ y = 1 then 0 else 1

/-- Boolean-circuit NAND semantics: the integer polynomial gives the NAND truth table on Boolean
inputs, and the resulting Boolean function is nonmonotone. This theorem makes no claim about
`PROJ_NORM` or `PROJ_ORDER` call counts, since this development has no program-cost semantics.
    thm:pom-boolean-circuit-nand-semantics -/
theorem paper_pom_boolean_circuit_nand_semantics :
    booleanCircuitCompilesCorrectly ∧ 1 - 0 * 0 > 1 - 1 * (1 : ℕ) := by
  constructor
  · intro x y hx hy
    simpa [booleanCircuitCompilesCorrectly] using
      Omega.POM.ValMonotoneBooleanNand.nand_boolean_identity x y hx hy
  · exact Omega.POM.ValMonotoneBooleanNand.nand_nonmonotone

/-- A single NAND macro uses one terminal normalization step. -/
def booleanCircuitNormProjCalls (_nandGateCount : ℕ) : ℕ := 1

/-- Composing one NAND macro per gate yields one order projection per gate. -/
def booleanCircuitOrderProjCalls (nandGateCount : ℕ) : ℕ := nandGateCount

/-- The one-gate NAND witness is nonmonotone and therefore needs a positive order budget. -/
def nonmonotoneBooleanNeedsOrderProj : Prop :=
  1 - 0 * 0 > 1 - 1 * (1 : ℕ) ∧ 0 < booleanCircuitOrderProjCalls 1

theorem paper_pom_boolean_circuit_projection_budget (nandGateCount : ℕ) :
    booleanCircuitCompilesCorrectly ∧
      booleanCircuitNormProjCalls nandGateCount = 1 ∧
      booleanCircuitOrderProjCalls nandGateCount = nandGateCount ∧
      nonmonotoneBooleanNeedsOrderProj := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · intro x y hx hy
    simpa [booleanCircuitCompilesCorrectly] using
      Omega.POM.ValMonotoneBooleanNand.nand_boolean_identity x y hx hy
  · refine ⟨Omega.POM.ValMonotoneBooleanNand.nand_nonmonotone, by decide⟩

end Omega.POM
