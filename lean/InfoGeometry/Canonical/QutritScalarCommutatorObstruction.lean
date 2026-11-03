/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.QutritSU3AdjointDecomposition

/-! A qutrit commutator has no nonzero scalar component. -/

namespace InfoGeometry.Canonical.QutritScalarCommutatorObstruction

open InfoGeometry.Canonical.QutritSU3AdjointDecomposition

theorem scalar_commutator_eq_zero (A B : QutritMatrix)
    (h : A * B - B * A ∈ scalar) : A * B - B * A = 0 := by
  have ht : A * B - B * A ∈ traceless := by
    change Matrix.trace (A * B - B * A) = 0
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  have hd := scalar_traceless_disjoint
  exact (Submodule.disjoint_def.mp hd) _ h ht

/-- An SU(3) conjugate of a commutator belongs to the scalar sector exactly
when it is zero. -/
theorem adjoint_commutator_scalar_iff_zero (g : SU3) (A B : QutritMatrix) :
    adjoint g (A * B - B * A) ∈ scalar ↔ adjoint g (A * B - B * A) = 0 := by
  have ht : A * B - B * A ∈ traceless := by
    change Matrix.trace (A * B - B * A) = 0
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  have hgt : adjoint g (A * B - B * A) ∈ traceless :=
    adjoint_preserves_traceless g ⟨_, ht, rfl⟩
  constructor
  · intro hs
    exact (Submodule.disjoint_def.mp scalar_traceless_disjoint) _ hs hgt
  · intro hz
    rw [hz]
    exact Submodule.zero_mem scalar

end InfoGeometry.Canonical.QutritScalarCommutatorObstruction
