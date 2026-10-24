/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.SuperSheafOddAnnihilation
import InfoGeometry.Core.PeirceTangentCounterexample

/-!
# Noncommuting matrix boundary for signed-pullback vanishing

Reuse the existing characteristic-two operator pair. Every matrix-valued
triple is invariant under the signed identity pullback, including a middle
component which does not commute with the existing projection. No new scalar
or diagonal model is substituted for the noncommutative operator algebra.
-/

namespace InfoGeometry.SuperGrassmannian.SheafAnnihilation

open InfoGeometry.Core.PeirceTangent

/-- Signed identity pullback is the identity on all triples of characteristic-two
matrix-valued functions, not just constant or commuting ones. -/
theorem matrix_signed_identity_pullback {M : Type*}
    (f : GradedSuperField M (Matrix (Fin 2) (Fin 2) (ZMod 2))) :
    moebiusPullback id f = f := by
  apply identity_pullback_invariant_of_two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.ofNat_apply]

/-- The previously defined noncommuting matrix direction survives unchanged as
the sign-changing component. Its noncommutation proves it is nonzero. -/
theorem noncommuting_middle_component_survives {M : Type*} (x : M) :
    let f : GradedSuperField M (Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
      ⟨fun _ => matrixBoundaryProjection, fun _ => matrixBoundaryDirection,
        fun _ => 0⟩
    moebiusPullback id f = f ∧
      f.odd1 x ≠ 0 ∧
      f.body x * f.odd1 x ≠ f.odd1 x * f.body x := by
  intro f
  have hnc := matrix_reflection_anticommutation_not_tangent.2.1
  refine ⟨matrix_signed_identity_pullback f, ?_, hnc⟩
  intro hz
  change matrixBoundaryDirection = 0 at hz
  apply hnc
  rw [hz, mul_zero, zero_mul]

end InfoGeometry.SuperGrassmannian.SheafAnnihilation
