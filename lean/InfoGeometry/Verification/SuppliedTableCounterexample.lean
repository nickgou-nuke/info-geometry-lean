/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Int.Basic

/-!
# Counterexamples to the supplied multiplication table

This verification-only file specializes the attachment's exact `octMul`
formula to the integers. It does not define a production split-octonion
carrier. The finite calculations below expose the source sign errors before
any claim of composition, alternativity, or a Clifford lift is accepted.

Source: `Pasted text(20261124-132544).txt`, supplied 2026-11-24.
Status at authoring: source candidate; not yet elaborated.
-/

namespace InfoGeometry.Verification.SuppliedTableCounterexample

private def rawMul (x y : Fin 8 → ℤ) : Fin 8 → ℤ :=
  ![ x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3 + x 4 * y 4 + x 5 * y 5 + x 6 * y 6 + x 7 * y 7,
     x 0 * y 1 + x 1 * y 0 + x 2 * y 3 - x 3 * y 2 - x 4 * y 5 + x 5 * y 4 + x 6 * y 7 - x 7 * y 6,
     x 0 * y 2 - x 1 * y 3 + x 2 * y 0 + x 3 * y 1 - x 4 * y 6 - x 5 * y 7 + x 6 * y 4 + x 7 * y 5,
     x 0 * y 3 + x 1 * y 2 - x 2 * y 1 + x 3 * y 0 - x 4 * y 7 + x 5 * y 6 - x 6 * y 5 + x 7 * y 4,
     x 0 * y 4 + x 1 * y 5 + x 2 * y 6 + x 3 * y 7 + x 4 * y 0 - x 5 * y 1 - x 6 * y 2 - x 7 * y 3,
     x 0 * y 5 - x 1 * y 4 - x 2 * y 7 + x 3 * y 6 + x 4 * y 1 + x 5 * y 0 + x 6 * y 3 - x 7 * y 2,
     x 0 * y 6 + x 1 * y 7 - x 2 * y 4 - x 3 * y 5 + x 4 * y 2 - x 5 * y 3 + x 6 * y 0 + x 7 * y 1,
     x 0 * y 7 - x 1 * y 6 + x 2 * y 5 - x 3 * y 4 + x 4 * y 3 + x 5 * y 2 - x 6 * y 1 + x 7 * y 0 ]

private def e (i : Fin 8) : Fin 8 → ℤ := fun j => if i = j then 1 else 0

private def rawConj (x : Fin 8 → ℤ) : Fin 8 → ℤ :=
  ![x 0, -x 1, -x 2, -x 3, -x 4, -x 5, -x 6, -x 7]

private def rawNorm (x : Fin 8 → ℤ) : ℤ :=
  x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 -
    x 4 ^ 2 - x 5 ^ 2 - x 6 ^ 2 - x 7 ^ 2

/-- The two sides of left alternativity disagree in coordinate one. -/
theorem supplied_left_alternativity_counterexample :
    rawMul (e 4) (rawMul (e 4) (e 1)) 1 = -1 ∧
      rawMul (rawMul (e 4) (e 4)) (e 1) 1 = 1 := by
  decide

/-- The first advertised conjugate-contraction identity is false. -/
theorem supplied_conjugate_contraction_counterexample :
    rawMul (e 4) (rawMul (rawConj (e 4)) (e 1)) 1 = 1 ∧
      rawNorm (e 4) * e 1 1 = -1 := by
  decide

/-- Two null inputs have a non-null product for the supplied table. -/
theorem supplied_norm_composition_counterexample :
    rawNorm (e 0 + e 4) = 0 ∧ rawNorm (e 1 + e 5) = 0 ∧
      rawNorm (rawMul (e 0 + e 4) (e 1 + e 5)) = -4 := by
  decide

/-- The table cannot be left alternative. -/
theorem supplied_not_left_alternative :
    ¬ ∀ x y : Fin 8 → ℤ, rawMul x (rawMul x y) = rawMul (rawMul x x) y := by
  intro h
  have hn : rawMul (e 4) (rawMul (e 4) (e 1)) 1 ≠
      rawMul (rawMul (e 4) (e 4)) (e 1) 1 := by decide
  exact hn (congrArg (fun z : Fin 8 → ℤ => z 1) (h (e 4) (e 1)))

private theorem raw_step_7_2 : rawMul (e 7) (e 2) = -(e 5) := by decide
private theorem raw_step_6_neg5 : rawMul (e 6) (-(e 5)) = e 3 := by decide
private theorem raw_step_5_3 : rawMul (e 5) (e 3) = -(e 6) := by decide
private theorem raw_step_4_neg6 : rawMul (e 4) (-(e 6)) = e 2 := by decide
private theorem raw_step_3_2 : rawMul (e 3) (e 2) = -(e 1) := by decide
private theorem raw_step_2_neg1 : rawMul (e 2) (-(e 1)) = e 3 := by decide
private theorem raw_step_1_3 : rawMul (e 1) (e 3) = -(e 2) := by decide

/-- The advertised integer seven-operator product fails on the second
imaginary basis vector; rightmost left multiplication is applied first. -/
theorem supplied_seven_operator_volume_counterexample :
    rawMul (e 1) (rawMul (e 2) (rawMul (e 3) (rawMul (e 4)
      (rawMul (e 5) (rawMul (e 6) (rawMul (e 7) (e 2))))))) = -(e 2) := by
  rw [raw_step_7_2, raw_step_6_neg5, raw_step_5_3, raw_step_4_neg6,
    raw_step_3_2, raw_step_2_neg1, raw_step_1_3]

end InfoGeometry.Verification.SuppliedTableCounterexample
