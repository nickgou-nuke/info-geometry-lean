/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.Algebra.Group.Equiv.Opposite

/-!
Local compatibility port for the general-linear inverse-transpose automorphism
used by the external CFSG sources. The construction is on the actual GL group
of invertible matrices; transpose is transported through the opposite ring and
combined with group inversion.
-/

public noncomputable section

namespace Matrix.GeneralLinearGroup

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- The inverse-transpose multiplicative equivalence of a general linear
operator group, ported locally for the pinned Mathlib version. -/
def inverseTranspose : GL n K ≃* GL n K :=
  (Units.mapEquiv (Matrix.transposeRingEquiv n K).toMulEquiv).trans
    (Units.opEquiv.trans (MulEquiv.inv' (GL n K)).symm)

/-- On underlying operators, inverse-transpose is matrix inverse followed by
transpose. -/
@[simp]
theorem coe_inverseTranspose (A : GL n K) :
    ((inverseTranspose A : GL n K) : Matrix n n K) = (A : Matrix n n K)⁻¹ᵀ := by
  simp [inverseTranspose, Matrix.transposeRingEquiv]
  rw [← Matrix.transpose_nonsing_inv]

@[simp]
theorem inverseTranspose_inverseTranspose (A : GL n K) :
    inverseTranspose (inverseTranspose A) = A := by
  apply Units.ext
  simp [Matrix.transpose_nonsing_inv]

end Matrix.GeneralLinearGroup
