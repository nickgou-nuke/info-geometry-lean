/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl22RealDiracCarrier

namespace InfoGeometry.Synthesis.Cl22RealDiracCarrier

open Matrix

/-- Right multiplication by the cross-sheet Andreev rotors acts on the first
sheet generator by the complementary planar formulas. -/
theorem e0_mul_andreevRotor (c s : ℝ) :
    e0 * andreevRotorRev c s = c • e0 - s • e2 ∧
    e0 * andreevRotor c s = c • e0 + s • e2 := by
  rcases J_geom_action_on_e0_e2 with ⟨he0_J, _, _, _⟩
  constructor
  · unfold andreevRotorRev
    rw [mul_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one,
      he0_J]
  · unfold andreevRotor
    rw [mul_add, Matrix.mul_smul, Matrix.mul_smul, mul_one,
      he0_J]

end InfoGeometry.Synthesis.Cl22RealDiracCarrier
