/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Ring.Idempotent

/-!
# Rectangular retracts and their full matrix corners

`K : Matrix n m R` and `Q : Matrix m n R` satisfy `Q * K = 1`.
Their corner embedding is multiplicative but need not preserve the ambient unit.
No diagonal, normal, self-adjoint, or commutation restriction is imposed.
-/

namespace InfoGeometry.Algebra.RectangularRetract

open Matrix

variable {R m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

section Semiring
variable [Semiring R] {K : Matrix n m R} {Q : Matrix m n R}

omit [DecidableEq n] in
theorem support_mul_inclusion (h : Q * K = 1) : (K * Q) * K = K := by
  rw [Matrix.mul_assoc, h, Matrix.mul_one]

omit [DecidableEq n] in
theorem retraction_mul_support (h : Q * K = 1) : Q * (K * Q) = Q := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

theorem support_idempotent (h : Q * K = 1) : IsIdempotentElem (K * Q) := by
  change (K * Q) * (K * Q) = K * Q
  rw [← Matrix.mul_assoc, support_mul_inclusion h]

omit [DecidableEq n] in
theorem sandwich_mul (h : Q * K = 1) (A B : Matrix m m R) :
    (K * A * Q) * (K * B * Q) = K * (A * B) * Q := by
  calc
    _ = K * A * (Q * K) * B * Q := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/-- The genuine nonunital ring homomorphism into the rectangular retract corner. -/
def cornerHom (K : Matrix n m R) (Q : Matrix m n R) (h : Q * K = 1) :
    Matrix m m R →ₙ+* Matrix n n R where
  toFun A := K * A * Q
  map_zero' := by simp
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_mul' A B := (sandwich_mul h A B).symm

@[simp] theorem cornerHom_apply (h : Q * K = 1) (A : Matrix m m R) :
    cornerHom K Q h A = K * A * Q := rfl

theorem compress_corner (h : Q * K = 1) (A : Matrix m m R) :
    Q * cornerHom K Q h A * K = A := by
  calc
    _ = (Q * K) * A * (Q * K) := by simp only [cornerHom_apply, Matrix.mul_assoc]
    _ = A := by rw [h, Matrix.one_mul, Matrix.mul_one]

theorem cornerHom_injective (h : Q * K = 1) : Function.Injective (cornerHom K Q h) := by
  intro A B hAB
  calc
    A = Q * cornerHom K Q h A * K := (compress_corner h A).symm
    _ = Q * cornerHom K Q h B * K := by rw [hAB]
    _ = B := compress_corner h B

@[simp] theorem cornerHom_one (h : Q * K = 1) :
    cornerHom K Q h 1 = K * Q := by simp

/-- Positive powers transport through a nonunital embedding; exponent zero is separate. -/
theorem cornerHom_pow_succ (h : Q * K = 1) (A : Matrix m m R) (r : ℕ) :
    (cornerHom K Q h A) ^ (r + 1) = cornerHom K Q h (A ^ (r + 1)) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, ih, ← map_mul, ← pow_succ]

end Semiring

section Geometry
variable [CommRing R] {K : Matrix n m R} {Q : Matrix m n R}

theorem toLin_support_idempotent (h : Q * K = 1) :
    IsIdempotentElem (Matrix.toLin' (K * Q)) := by
  change (Matrix.toLin' (K * Q)).comp (Matrix.toLin' (K * Q)) = _
  rw [← Matrix.toLin'_mul, (support_idempotent h).eq]

theorem support_range (h : Q * K = 1) :
    LinearMap.range (Matrix.toLin' (K * Q)) = LinearMap.range (Matrix.toLin' K) := by
  rw [Matrix.toLin'_mul]
  apply le_antisymm (LinearMap.range_comp_le_range _ _)
  rintro x ⟨v, rfl⟩
  refine ⟨Matrix.toLin' K v, ?_⟩
  change Matrix.toLin' K (Matrix.toLin' Q (Matrix.toLin' K v)) = Matrix.toLin' K v
  rw [← Matrix.toLin'_mul_apply Q K, h, Matrix.toLin'_one, LinearMap.id_apply]

theorem support_ker (h : Q * K = 1) :
    LinearMap.ker (Matrix.toLin' (K * Q)) = LinearMap.ker (Matrix.toLin' Q) := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.toLin'_mul_apply]
  constructor
  · intro hv
    have hc := congrArg (Matrix.toLin' Q) hv
    rw [← Matrix.toLin'_mul_apply Q K, h, Matrix.toLin'_one, LinearMap.id_apply,
      map_zero] at hc
    exact hc
  · intro hv
    rw [hv, map_zero]

/-- The range of the inclusion and kernel of the retraction are complementary submodules. -/
theorem range_isCompl_ker (h : Q * K = 1) :
    IsCompl (LinearMap.range (Matrix.toLin' K)) (LinearMap.ker (Matrix.toLin' Q)) := by
  rw [← support_range h, ← support_ker h]
  exact LinearMap.IsIdempotentElem.isCompl (toLin_support_idempotent h)

/-- Inclusion in the retract range is detected by the actual projection action. -/
theorem range_le_iff {s : Type*} [Fintype s] [DecidableEq s]
    (h : Q * K = 1) (L : Matrix n s R) :
    LinearMap.range (Matrix.toLin' L) ≤ LinearMap.range (Matrix.toLin' K) ↔
      (K * Q) * L = L := by
  rw [← support_range h, ← LinearMap.IsIdempotentElem.comp_eq_right_iff (toLin_support_idempotent h)]
  rw [← Matrix.toLin'_mul]
  exact Matrix.toLin'.injective.eq_iff

/-- Equal finite square dimensions force the retract support to be the identity. -/
theorem square_retract_support {K Q : Matrix n n R} (h : Q * K = 1) : K * Q = 1 :=
  _root_.mul_eq_one_comm.mp h

/-- A strictly smaller retract dimension rules out collapse to the ambient unit. -/
omit [DecidableEq m] in
theorem support_ne_one_of_card_lt [StrongRankCondition R]
    (K : Matrix n m R) (Q : Matrix m n R) (hdim : Fintype.card m < Fintype.card n) :
    K * Q ≠ 1 := by
  intro heq
  have hr := (Matrix.rank_mul_le_left K Q).trans (Matrix.rank_le_card_width K)
  rw [heq, Matrix.rank_one] at hr
  exact (not_le_of_gt hdim) hr

end Geometry

section Star
variable [Semiring R] [StarRing R]

/-- Adjoint reverses the rectangular retract and transports its entire matrix corner. -/
theorem cornerHom_conjTranspose (K : Matrix n m R) (Q : Matrix m n R)
    (h : Q * K = 1) (A : Matrix m m R) :
    (cornerHom K Q h A)ᴴ =
      cornerHom Qᴴ Kᴴ (by simpa using congrArg Matrix.conjTranspose h) Aᴴ := by
  simp only [cornerHom_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end Star
end InfoGeometry.Algebra.RectangularRetract
