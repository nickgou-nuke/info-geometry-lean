/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.IdempotentProjector
import InfoGeometry.OperatorAlgebra.LieJordanEndomorphisms

/-!
# Peirce resolution by native Lie--Jordan endomorphisms

Reuse the existing four corner functions. The new bundled projections are
endomorphisms of the full algebra, not replacements by diagonal coordinates.
The indexed multiplication theorem is the entire sixteen-cell Peirce table.
All doubled extraction identities are characteristic-free; uniqueness is
provided by the actual corner projections, not by division by two.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan

variable {A : Type*} [Ring A]

/-- The two endpoints of the existing complementary Peirce frame. -/
def endpoint (P : A) : Bool → A
  | false => compIdempotent P
  | true => P

theorem endpoint_mul {P : A} (hP : IsIdempotent P) (i j : Bool) :
    endpoint P i * endpoint P j = if i = j then endpoint P i else 0 := by
  have hPP : P * P = P := hP
  have hQQ : compIdempotent P * compIdempotent P = compIdempotent P :=
    compIdempotent_isIdempotent hP
  have hPQ := compIdempotent_orthogonal hP
  have hQP := compIdempotent_orthogonal_rev hP
  cases i <;> cases j <;> simp [endpoint, hPP, hQQ, hPQ, hQP]

variable (R : Type*) [CommRing R] [Algebra R A]

/-- A corner extraction as a native endomorphism of the full algebra. -/
def corner (P : A) (i j : Bool) : Module.End R A :=
  (LinearMap.mulRight R (endpoint P j)).comp (LinearMap.mulLeft R (endpoint P i))

@[simp] theorem corner_apply (P : A) (i j : Bool) (X : A) :
    corner R P i j X = endpoint P i * X * endpoint P j := rfl

@[simp] theorem corner_tt (P X : A) : corner R P true true X = peirce11 P X := rfl
@[simp] theorem corner_tf (P X : A) : corner R P true false X = peirce10 P X := rfl
@[simp] theorem corner_ft (P X : A) : corner R P false true X = peirce01 P X := rfl
@[simp] theorem corner_ff (P X : A) : corner R P false false X = peirce00 P X := rfl

/-- Pairwise orthogonal idempotents in the endomorphism ring. -/
theorem corner_comp {P : A} (hP : IsIdempotent P) (i j k l : Bool) :
    corner R P i j * corner R P k l =
      if i = k ∧ j = l then corner R P i j else 0 := by
  ext X
  have h : (corner R P i j * corner R P k l) X =
      (endpoint P i * endpoint P k) * X * (endpoint P l * endpoint P j) := by
    change endpoint P i * (endpoint P k * X * endpoint P l) * endpoint P j = _
    noncomm_ring
  rw [h, endpoint_mul hP, endpoint_mul hP]
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [hik, hjl, eq_comm, corner_apply]

/-- The four genuine projections resolve the identity endomorphism. -/
theorem corner_sum (P : A) :
    corner R P true true + corner R P true false +
      corner R P false true + corner R P false false = 1 := by
  ext X
  change peirce11 P X + peirce10 P X + peirce01 P X + peirce00 P X = X
  exact peirce_decomposition_sum P X

/-- All sixteen block-product laws, with the middle operator order retained. -/
theorem corner_mul {P : A} (hP : IsIdempotent P) (i j k l : Bool) (X Y : A) :
    corner R P i j X * corner R P k l Y =
      if j = k then corner R P i l (X * endpoint P j * Y) else 0 := by
  by_cases hjk : j = k
  · subst k
    simp only [if_pos rfl, corner_apply]
    calc
      (endpoint P i * X * endpoint P j) * (endpoint P j * Y * endpoint P l) =
          endpoint P i * X * (endpoint P j * endpoint P j) * Y * endpoint P l := by
        noncomm_ring
      _ = endpoint P i * (X * endpoint P j * Y) * endpoint P l := by
        rw [endpoint_mul hP, if_pos rfl]
        noncomm_ring
  · rw [if_neg hjk]
    simp only [corner_apply]
    calc
      (endpoint P i * X * endpoint P j) * (endpoint P k * Y * endpoint P l) =
          endpoint P i * X * (endpoint P j * endpoint P k) * Y * endpoint P l := by
        noncomm_ring
      _ = 0 := by rw [endpoint_mul hP, if_neg hjk]; simp

/-- The double commutator is the off-diagonal extraction. -/
theorem double_lie {P : A} (hP : IsIdempotent P) (X : A) :
    lieOp R P (lieOp R P X) = P * X + X * P - (P * X * P + P * X * P) := by
  simp only [lieOp_apply]
  calc
    P * (P * X - X * P) - (P * X - X * P) * P =
        (P * P) * X + X * (P * P) - (P * X * P + P * X * P) := by
      noncomm_ring
    _ = _ := by rw [show P * P = P from hP]

theorem peirce11_lie_jordan {P : A} (hP : IsIdempotent P) (X : A) :
    peirce11 P X + peirce11 P X =
      jordanOp R P X - lieOp R P (lieOp R P X) := by
  rw [double_lie R hP]
  simp only [jordanOp_apply, peirce11]
  abel

theorem peirce00_lie_jordan {P : A} (hP : IsIdempotent P) (X : A) :
    peirce00 P X + peirce00 P X =
      X + X - jordanOp R P X - lieOp R P (lieOp R P X) := by
  rw [double_lie R hP]
  simp only [jordanOp_apply, peirce00, compIdempotent]
  noncomm_ring

theorem peirce10_lie_jordan {P : A} (hP : IsIdempotent P) (X : A) :
    peirce10 P X + peirce10 P X =
      lieOp R P (lieOp R P X) + lieOp R P X := by
  rw [double_lie R hP]
  simp only [lieOp_apply, peirce10, compIdempotent]
  noncomm_ring

theorem peirce01_lie_jordan {P : A} (hP : IsIdempotent P) (X : A) :
    peirce01 P X + peirce01 P X =
      lieOp R P (lieOp R P X) - lieOp R P X := by
  rw [double_lie R hP]
  simp only [lieOp_apply, peirce01, compIdempotent]
  noncomm_ring

/-- An exact identification with the existing odd Peirce part. -/
theorem double_lie_eq_offDiagonal {P : A} (hP : IsIdempotent P) (X : A) :
    lieOp R P (lieOp R P X) = peirce10 P X + peirce01 P X := by
  rw [double_lie R hP]
  simp only [peirce10, peirce01, compIdempotent]
  noncomm_ring

/-- Corner extraction commutes with every algebra homomorphism. -/
theorem map_corner {B : Type*} [Ring B] [Algebra R B]
    (f : A →ₐ[R] B) (P X : A) (i j : Bool) :
    f (corner R P i j X) = corner R (f P) i j (f X) := by
  cases i <;> cases j <;>
    simp [corner_apply, endpoint, compIdempotent, map_mul, map_sub, map_one]

end InfoGeometry.OperatorAlgebra.LieJordan
