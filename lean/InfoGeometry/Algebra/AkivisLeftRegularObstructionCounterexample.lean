/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.AkivisLeftRegularBridge
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Concrete nonzero left-regular commutator defect

The generic Akivis bridge identifies the defect with the negative associator
under the alternative associator-swap law. The native Zorn carrier supplies a
nonzero associator triple, so its left-regular commutator defect is nonzero.
This is a finite algebraic witness, not a representation theorem.
-/

namespace InfoGeometry.Algebra.AkivisLeftRegularObstructionCounterexample

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

theorem zorn_leftRegular_commutator_obstruction_nonzero :
    ∃ x y : ZornVectorMatrix ℝ,
      leftRegularCommutatorObstruction x y ≠ 0 := by
  refine ⟨U 0, U 1, ?_⟩
  intro hzero
  have heval := congrArg (fun f : ZornVectorMatrix ℝ →ₗ[ℝ] ZornVectorMatrix ℝ =>
    f (U 2)) hzero
  have hdefect := leftRegular_commutator_obstruction_apply
    zornVectorMatrix_alternative_associator_swap12 (U 0) (U 1) (U 2)
  rw [hdefect] at heval
  exact ZornVectorMatrix.associator_U_zero_U_one_U_two_ne_zero
    (neg_eq_zero.mp heval)

end InfoGeometry.Algebra.AkivisLeftRegularObstructionCounterexample
