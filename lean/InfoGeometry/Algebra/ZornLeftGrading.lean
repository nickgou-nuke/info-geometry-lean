/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornDerivationBridge

/-! # Left-regular Zorn grading

The carrier and `L_map` are reused from `ZornDerivationBridge` and
`AlternativeDerivations`. The real CAR lift already belongs to `ZornLeftCAR`;
these results work over every commutative coefficient ring. The projector is
left multiplication by the existing `E11`, as in `FirstQuantizedSplitOctonions`.
No Grassmannian functor or Lie-superalgebra classification is asserted.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

noncomputable section

/-- The left action of the native diagonal difference gives the correct four-plus-four signs. -/
theorem left_diagonal_difference_apply (X : ZornVectorMatrix R) :
    L_map (R := R) (diagonal 1 (-1)) X = ⟨X.a, X.v, -X.w, -X.b⟩ := by
  change mul (diagonal 1 (-1)) X = _
  ext i <;> simp [mul, diagonal, ZornVec3.dot, ZornVec3.cross]

/-- The positive projector is the existing left Peirce action, not a new carrier. -/
theorem left_E11_apply (X : ZornVectorMatrix R) :
    L_map (R := R) E11 X = ⟨X.a, X.v, 0, 0⟩ := by
  change mul E11 X = _
  ext i <;> simp [mul, E11, ZornVec3.dot, ZornVec3.cross]

theorem left_E11_idempotent :
    L_map (R := R) (E11 : ZornVectorMatrix R) * L_map (R := R) E11 =
      L_map (R := R) E11 := by
  apply LinearMap.ext
  intro X
  change L_map (R := R) E11 (L_map (R := R) E11 X) = L_map (R := R) E11 X
  simp only [left_E11_apply]

/-- No inverse of two is needed to construct this involution. -/
theorem left_diagonal_difference_involution :
    L_map (R := R) (diagonal 1 (-1) : ZornVectorMatrix R) *
      L_map (R := R) (diagonal 1 (-1)) = 1 := by
  apply LinearMap.ext
  intro X
  change L_map (R := R) (diagonal 1 (-1))
    (L_map (R := R) (diagonal 1 (-1)) X) = X
  rw [left_diagonal_difference_apply, left_diagonal_difference_apply]
  ext i <;> simp

theorem left_diagonal_difference_eq_two_projector_sub_one :
    L_map (R := R) (diagonal 1 (-1) : ZornVectorMatrix R) =
      2 • L_map (R := R) E11 - 1 := by
  apply LinearMap.ext
  intro X
  simp only [two_nsmul, LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply]
  rw [left_diagonal_difference_apply, left_E11_apply]
  simp only [_root_.sub_eq_add_neg, zvm_add_def, zvm_neg_def]
  ext i <;> simp [add, neg]

/-- Every off-diagonal left action is odd for the left diagonal-difference grading. -/
theorem left_diagonal_difference_anticommutes_offDiagonal (u v : ZornVec3 R) :
    L_map (R := R) (diagonal 1 (-1)) * L_map (R := R) (offDiagonal u v) +
      L_map (R := R) (offDiagonal u v) * L_map (R := R) (diagonal 1 (-1)) = 0 := by
  apply LinearMap.ext
  intro X
  change add (mul (diagonal 1 (-1)) (mul (offDiagonal u v) X))
    (mul (offDiagonal u v) (mul (diagonal 1 (-1)) X)) = zero
  ext i <;> (try fin_cases i) <;> simp [mul, diagonal, offDiagonal, add, zero,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

/-- The projector tangent equation holds directly in every characteristic. -/
theorem left_E11_tangent_offDiagonal (u v : ZornVec3 R) :
    L_map (R := R) E11 * L_map (R := R) (offDiagonal u v) +
      L_map (R := R) (offDiagonal u v) * L_map (R := R) E11 =
      L_map (R := R) (offDiagonal u v) := by
  apply LinearMap.ext
  intro X
  change add (mul E11 (mul (offDiagonal u v) X))
    (mul (offDiagonal u v) (mul E11 X)) = mul (offDiagonal u v) X
  ext i <;> simp [mul, E11, offDiagonal, add,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

end
end InfoGeometry.Algebra.ZornVectorMatrix
