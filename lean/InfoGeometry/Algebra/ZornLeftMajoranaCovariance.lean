/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornLeftMajorana
import InfoGeometry.Algebra.ChiralCARTransport

/-! Quadratic covariance of the native positive and negative Clifford vectors.
The difference of their quadratic products acts with the same sign on each
family. These are algebraic commutators, without star or unitary assumptions. -/
namespace InfoGeometry.Algebra.ZornVectorMatrix
variable {R : Type*} [CommRing R]
noncomputable section

/-- The difference of same-signature quadratic products. -/
def leftMajoranaCurrent (u v : ZornVec3 R) : Module.End R (ZornVectorMatrix R) :=
  leftMajoranaPlus u * leftMajoranaPlus v - leftMajoranaMinus u * leftMajoranaMinus v

theorem leftMajoranaCurrent_action_plus (u v w : ZornVec3 R) :
    leftMajoranaCurrent u v * leftMajoranaPlus w -
      leftMajoranaPlus w * leftMajoranaCurrent u v =
      (2 * ZornVec3.dot v w) • leftMajoranaPlus u -
        (2 * ZornVec3.dot u w) • leftMajoranaPlus v := by
  have hm (x : ZornVec3 R) :
      leftMajoranaMinus x * leftMajoranaPlus w +
        leftMajoranaPlus w * leftMajoranaMinus x = 0 := by
    simpa only [_root_.add_comm] using leftMajorana_mixed_anticommutator w x
  unfold leftMajoranaCurrent
  calc
    _ = ((leftMajoranaPlus u * leftMajoranaPlus v) * leftMajoranaPlus w -
        leftMajoranaPlus w * (leftMajoranaPlus u * leftMajoranaPlus v)) -
      ((leftMajoranaMinus u * leftMajoranaMinus v) * leftMajoranaPlus w -
        leftMajoranaPlus w * (leftMajoranaMinus u * leftMajoranaMinus v)) := by noncomm_ring
    _ = _ := by
      rw [ChiralCARTransport.quadratic_commutator, ChiralCARTransport.quadratic_commutator,
        leftMajoranaPlus_anticommutator, leftMajoranaPlus_anticommutator, hm, hm]
      simp

theorem leftMajoranaCurrent_action_minus (u v w : ZornVec3 R) :
    leftMajoranaCurrent u v * leftMajoranaMinus w -
      leftMajoranaMinus w * leftMajoranaCurrent u v =
      (2 * ZornVec3.dot v w) • leftMajoranaMinus u -
        (2 * ZornVec3.dot u w) • leftMajoranaMinus v := by
  unfold leftMajoranaCurrent
  calc
    _ = ((leftMajoranaPlus u * leftMajoranaPlus v) * leftMajoranaMinus w -
        leftMajoranaMinus w * (leftMajoranaPlus u * leftMajoranaPlus v)) -
      ((leftMajoranaMinus u * leftMajoranaMinus v) * leftMajoranaMinus w -
        leftMajoranaMinus w * (leftMajoranaMinus u * leftMajoranaMinus v)) := by noncomm_ring
    _ = _ := by
      rw [ChiralCARTransport.quadratic_commutator, ChiralCARTransport.quadratic_commutator,
        leftMajorana_mixed_anticommutator, leftMajorana_mixed_anticommutator,
        leftMajoranaMinus_anticommutator, leftMajoranaMinus_anticommutator]
      simp [_root_.neg_mul, neg_smul]
      abel

theorem leftMajoranaCurrent_commutes_grading (u v : ZornVec3 R) :
    Commute (leftMajoranaCurrent u v)
      (L_map (R := R) (diagonal (R := R) 1 (-1))) := by
  have hp (x : ZornVec3 R) :
      leftMajoranaPlus x * L_map (R := R) (diagonal (R := R) 1 (-1)) +
        L_map (R := R) (diagonal (R := R) 1 (-1)) * leftMajoranaPlus x = 0 := by
    simpa only [leftMajoranaPlus, _root_.add_comm] using
      left_diagonal_difference_anticommutes_offDiagonal x x
  have hm (x : ZornVec3 R) :
      leftMajoranaMinus x * L_map (R := R) (diagonal (R := R) 1 (-1)) +
        L_map (R := R) (diagonal (R := R) 1 (-1)) * leftMajoranaMinus x = 0 := by
    simpa only [leftMajoranaMinus, _root_.add_comm] using
      left_diagonal_difference_anticommutes_offDiagonal x (-x)
  apply sub_eq_zero.mp
  unfold leftMajoranaCurrent
  calc
    _ = ((leftMajoranaPlus u * leftMajoranaPlus v) * L_map (R := R) (diagonal (R := R) 1 (-1)) -
        L_map (R := R) (diagonal (R := R) 1 (-1)) * (leftMajoranaPlus u * leftMajoranaPlus v)) -
      ((leftMajoranaMinus u * leftMajoranaMinus v) * L_map (R := R) (diagonal (R := R) 1 (-1)) -
        L_map (R := R) (diagonal (R := R) 1 (-1)) * (leftMajoranaMinus u * leftMajoranaMinus v)) := by noncomm_ring
    _ = 0 := by
      rw [ChiralCARTransport.quadratic_commutator, ChiralCARTransport.quadratic_commutator,
        hp, hp, hm, hm]
      simp

/-- Both signatures obey the direct projector tangent equation. -/
theorem leftMajoranaPlus_tangent (u : ZornVec3 R) :
    L_map (R := R) (E11 : ZornVectorMatrix R) * leftMajoranaPlus u +
      leftMajoranaPlus u * L_map (R := R) E11 = leftMajoranaPlus u :=
  left_E11_tangent_offDiagonal u u

theorem leftMajoranaMinus_tangent (u : ZornVec3 R) :
    L_map (R := R) (E11 : ZornVectorMatrix R) * leftMajoranaMinus u +
      leftMajoranaMinus u * L_map (R := R) E11 = leftMajoranaMinus u :=
  left_E11_tangent_offDiagonal u (-u)

theorem leftMajoranaPlus_odd (u : ZornVec3 R) :
    L_map (R := R) (diagonal (R := R) 1 (-1)) * leftMajoranaPlus u +
      leftMajoranaPlus u * L_map (R := R) (diagonal (R := R) 1 (-1)) = 0 :=
  left_diagonal_difference_anticommutes_offDiagonal u u

theorem leftMajoranaMinus_odd (u : ZornVec3 R) :
    L_map (R := R) (diagonal (R := R) 1 (-1)) * leftMajoranaMinus u +
      leftMajoranaMinus u * L_map (R := R) (diagonal (R := R) 1 (-1)) = 0 :=
  left_diagonal_difference_anticommutes_offDiagonal u (-u)

theorem leftMajorana_mode_product_square (i : Fin 3) :
    (leftMajoranaMinus (ZornVec3.basis (R := R) i) * leftMajoranaPlus (ZornVec3.basis i)) *
      (leftMajoranaMinus (ZornVec3.basis i) * leftMajoranaPlus (ZornVec3.basis i)) = 1 := by
  rw [← mul_assoc, leftMajorana_mode_flip_minus, leftMajoranaPlus_basis_square]

end
end InfoGeometry.Algebra.ZornVectorMatrix
