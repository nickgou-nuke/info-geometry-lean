/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ChiralCARTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornLeftMajorana
import InfoGeometry.Algebra.ZornColorBilinears

/-! # Rotation covariance of native Zorn Majorana operators

The difference of the two signature bivectors rotates both Majorana families
with the same sign. For general nonorthogonal vectors the generator also has
a central scalar component; it is not an alternating bilinear map. All products
are compositions of native linear maps.
-/
namespace InfoGeometry.Algebra.ZornVectorMatrix

open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section NonCommRingMajoranaRotations

variable {B : Type*} [Ring B]

/-- Difference of two chiral bivector products `γplus_u * γplus_v - γminus_u * γminus_v`
in an arbitrary non-commutative ring `[Ring B]`. -/
def majoranaRotationRing (γplus_u γplus_v γminus_u γminus_v : B) : B :=
  γplus_u * γplus_v - γminus_u * γminus_v

/-- Universal derivation-to-anticommutator identity in any non-commutative ring `[Ring B]`:
`(A * C) * D - D * (A * C) = A * (C * D + D * C) - (A * D + D * A) * C`. -/
theorem quadratic_commutator_ring (A C D : B) :
    (A * C) * D - D * (A * C) = A * (C * D + D * C) - (A * D + D * A) * C := by
  noncomm_ring

/-- In any non-commutative ring `[Ring B]`, if `γminus_u` and `γminus_v` anticommute
with `γplus_w`, then the commutator of `majoranaRotationRing γplus_u γplus_v γminus_u γminus_v`
with `γplus_w` reduces to `γplus_u * {γplus_v, γplus_w} - {γplus_u, γplus_w} * γplus_v`. -/
theorem majoranaRotationRing_action_plus
    (γplus_u γplus_v γplus_w γminus_u γminus_v : B)
    (huw : γminus_u * γplus_w + γplus_w * γminus_u = 0)
    (hvw : γminus_v * γplus_w + γplus_w * γminus_v = 0) :
    majoranaRotationRing γplus_u γplus_v γminus_u γminus_v * γplus_w -
      γplus_w * majoranaRotationRing γplus_u γplus_v γminus_u γminus_v =
        γplus_u * (γplus_v * γplus_w + γplus_w * γplus_v) -
          (γplus_u * γplus_w + γplus_w * γplus_u) * γplus_v := by
  have hsplit :
      majoranaRotationRing γplus_u γplus_v γminus_u γminus_v * γplus_w -
        γplus_w * majoranaRotationRing γplus_u γplus_v γminus_u γminus_v =
      ((γplus_u * γplus_v) * γplus_w - γplus_w * (γplus_u * γplus_v)) -
        ((γminus_u * γminus_v) * γplus_w - γplus_w * (γminus_u * γminus_v)) := by
    dsimp [majoranaRotationRing]
    noncomm_ring
  rw [hsplit, quadratic_commutator_ring γplus_u γplus_v γplus_w,
    quadratic_commutator_ring γminus_u γminus_v γplus_w, huw, hvw]
  noncomm_ring

end NonCommRingMajoranaRotations

variable {R : Type*} [CommRing R]
noncomputable section

/-- A vector-parametric rotation generator on the existing Zorn module. -/
def leftMajoranaRotation (u v : ZornVec3 R) : Module.End R (ZornVectorMatrix R) :=
  leftMajoranaPlus u * leftMajoranaPlus v - leftMajoranaMinus u * leftMajoranaMinus v

theorem leftMajoranaRotation_action_plus (u v w : ZornVec3 R) :
    leftMajoranaRotation u v * leftMajoranaPlus w -
      leftMajoranaPlus w * leftMajoranaRotation u v =
        (2 * ZornVec3.dot v w) • leftMajoranaPlus u -
          (2 * ZornVec3.dot u w) • leftMajoranaPlus v := by
  have hm (x y : ZornVec3 R) :
      leftMajoranaMinus x * leftMajoranaPlus y +
        leftMajoranaPlus y * leftMajoranaMinus x = 0 := by
    simpa only [_root_.add_comm] using leftMajorana_mixed_anticommutator y x
  calc
    _ = (leftMajoranaPlus u * leftMajoranaPlus v * leftMajoranaPlus w -
          leftMajoranaPlus w * (leftMajoranaPlus u * leftMajoranaPlus v)) -
        (leftMajoranaMinus u * leftMajoranaMinus v * leftMajoranaPlus w -
          leftMajoranaPlus w * (leftMajoranaMinus u * leftMajoranaMinus v)) := by
      unfold leftMajoranaRotation
      noncomm_ring
    _ = _ := by
      rw [InfoGeometry.Algebra.ChiralCARTransport.quadratic_commutator, InfoGeometry.Algebra.ChiralCARTransport.quadratic_commutator,
        leftMajoranaPlus_anticommutator, leftMajoranaPlus_anticommutator, hm, hm]
      simp

theorem leftMajoranaRotation_action_minus (u v w : ZornVec3 R) :
    leftMajoranaRotation u v * leftMajoranaMinus w -
      leftMajoranaMinus w * leftMajoranaRotation u v =
        (2 * ZornVec3.dot v w) • leftMajoranaMinus u -
          (2 * ZornVec3.dot u w) • leftMajoranaMinus v := by
  calc
    _ = (leftMajoranaPlus u * leftMajoranaPlus v * leftMajoranaMinus w -
          leftMajoranaMinus w * (leftMajoranaPlus u * leftMajoranaPlus v)) -
        (leftMajoranaMinus u * leftMajoranaMinus v * leftMajoranaMinus w -
          leftMajoranaMinus w * (leftMajoranaMinus u * leftMajoranaMinus v)) := by
      unfold leftMajoranaRotation
      noncomm_ring
    _ = _ := by
      rw [InfoGeometry.Algebra.ChiralCARTransport.quadratic_commutator, InfoGeometry.Algebra.ChiralCARTransport.quadratic_commutator,
        leftMajorana_mixed_anticommutator, leftMajorana_mixed_anticommutator,
        leftMajoranaMinus_anticommutator, leftMajoranaMinus_anticommutator]
      simp [_root_.neg_mul, _root_.neg_smul]
      abel

/-- Evenness is obtained directly from the two tangent equations, without dividing by two. -/
theorem leftMajoranaRotation_commutes_projector (u v : ZornVec3 R) :
    L_map (R := R) (E11 : ZornVectorMatrix R) * leftMajoranaRotation u v =
      leftMajoranaRotation u v * L_map E11 := by
  unfold leftMajoranaRotation leftMajoranaPlus leftMajoranaMinus
  rw [_root_.mul_sub, _root_.sub_mul,
    InfoGeometry.Algebra.ZornColorBilinears.left_E11_commutes_offDiagonal_product,
    InfoGeometry.Algebra.ZornColorBilinears.left_E11_commutes_offDiagonal_product]

/-- A normalized mode parity is an involution in the associative endomorphism ring. -/
theorem leftMajorana_mode_product_square (i : Fin 3) :
    (leftMajoranaMinus (ZornVec3.basis (R := R) i) * leftMajoranaPlus (ZornVec3.basis i)) *
      (leftMajoranaMinus (ZornVec3.basis i) * leftMajoranaPlus (ZornVec3.basis i)) = 1 := by
  rw [← mul_assoc, leftMajorana_mode_flip_minus, leftMajoranaPlus_basis_square]

end
end InfoGeometry.Algebra.ZornVectorMatrix
