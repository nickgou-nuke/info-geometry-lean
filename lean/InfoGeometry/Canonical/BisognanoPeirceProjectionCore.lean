/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.Pin55NondegenerateKreinBridge

/-!
# The Peirce projection of the Bisognano–Wichmann wedge

Genuine proofs supplied for two placeholder lemmas in the stash lane
`BisognanoWichmannKreinWedge`.  The projection `P = ½(1 + J₅₅)` is idempotent
and self-adjoint for the Krein form because `J₅₅² = 1` and `J₅₅ᵀ = J₅₅`, both
already proved in the `Pin55NondegenerateKreinBridge` owner.  No `sorry`.
-/

noncomputable section

namespace InfoGeometry.Canonical.BisognanoPeirceProjectionCore

open InfoGeometry.Lie.Pin55NondegenerateKreinBridge
open scoped Matrix

/-- The Peirce projection onto the positive (timelike) sector. -/
def peirceProjection : Matrix (Fin 10) (Fin 10) ℝ :=
  (1 / 2 : ℝ) • (1 + J55)

private theorem one_add_J55_sq : (1 + J55) * (1 + J55) = (2 : ℝ) • (1 + J55) := by
  rw [mul_add, mul_one, add_mul, one_mul, J55_mul_self]
  simp only [two_smul]
  abel

private theorem J55_mul_one_add : (1 + J55) * J55 = 1 + J55 := by
  rw [add_mul, one_mul, J55_mul_self, add_comm]

/-- The Peirce projection is idempotent. -/
theorem peirceProjection_mul_self : peirceProjection * peirceProjection = peirceProjection := by
  unfold peirceProjection
  rw [smul_mul_smul, one_add_J55_sq, smul_smul]
  norm_num

/-- The Peirce projection is self-adjoint for the Krein form. -/
theorem peirceProjection_krein_selfAdjoint :
    peirceProjectionᵀ * J55 * peirceProjection = peirceProjectionᵀ * J55 := by
  unfold peirceProjection
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one, J55_transpose]
  conv_lhs =>
    rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul]
    rw [J55_mul_one_add, one_add_J55_sq, smul_smul]
  conv_rhs =>
    rw [smul_mul_assoc, J55_mul_one_add]
  norm_num

/-- The Unruh temperature for acceleration `a`. -/
def unruhTemperature (a : ℝ) : ℝ := a / (2 * Real.pi)

/-- Thermal time / proper time relation: `2π/a = 1/(a/2π)` for `a > 0`.
This fills a `by sorry` hole from the stash lane `BisognanoWichmannKreinWedge`. -/
theorem thermalTime_properTime_relation (a : ℝ) (ha : a > 0) :
    (2 * Real.pi / a : ℝ) = (1 : ℝ) / (a / (2 * Real.pi)) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [ha0, hpi]

end InfoGeometry.Canonical.BisognanoPeirceProjectionCore
