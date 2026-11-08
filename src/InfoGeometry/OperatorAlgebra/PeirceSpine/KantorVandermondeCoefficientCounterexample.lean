/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorFifthChargeClosure

/-!
# Concrete counterexample to an incorrectly scaled grade-`+1` projector

The scale-12 Lagrange channel is `4 (4 Δ² - Δ⁴)`, not `4 Δ² - Δ⁴`.
The matrix witness below refutes the version missing the outer factor `4`.
The canonical corrected channel is already proved for every idempotent by
`archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

abbrev KantorWitnessMatrix := Matrix (Fin 2) (Fin 2) ℤ

private def projectorWitness : KantorWitnessMatrix :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

private def upperWitness : KantorWitnessMatrix :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

private def lowerWitness : KantorWitnessMatrix :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- The unscaled grade-`+1` formula from the intake is false in `M₂(ℤ)`.
Here `P` is an idempotent, `N₊ = E₀₁`, `N₋ = 0`, and the test input is `E₁₀`.
The two sides evaluate to `3 (E₀₀ - E₁₁)` and `12 (E₀₀ - E₁₁)`. -/
theorem unscaled_grade_plus_one_projector_formula_false :
    let P := projectorWitness
    let A := upperWitness
    let C : KantorWitnessMatrix := 0
    let X := lowerWitness
    (4 : ℤ) • kantorDelta2 P A C X - kantorDelta4 P A C X ≠
      (12 : ℤ) • (kantorGp1 P A X + kantorGm1 P C X) := by
  decide

/-- The corrected scale-12 channel retains the outer factor and equals the
grade-`±1` sum, as proved by the generic Kantor–Peirce interpolation theorem. -/
theorem corrected_scale12_grade_plus_one_channel
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B) :
    golay12Root P A C X = (12 : ℤ) • comm (genPhi P A C) X := by
  exact (archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes
    hP A C X).2.2.1

end InfoGeometry.OperatorAlgebra.PeirceSpine
