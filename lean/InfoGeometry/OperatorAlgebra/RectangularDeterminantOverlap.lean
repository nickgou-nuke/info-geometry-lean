/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Abel

/-!
# Finite rectangular determinant overlaps

The determinant of a split rectangular lift with its identity complement is
the determinant on the embedded carrier.  For occupied frames, the ordered
compression `Lᴴ * D * R` transforms under the two frame changes separately.
Its Gram determinant retains the target range matrix unless an explicit
image condition removes it.

For isometric right frames, the squared overlap modulus is also the
determinant of an ambient expression depending only on `L * Lᴴ` and
`R * Rᴴ`.  Over `RCLike` coefficients the star-square is the real squared
norm.  Singular overlaps and the empty occupied frame are included.

These are finite matrix identities.  The coefficient ring is commutative;
the rectangular matrix products retain their order.  No determinant line
bundle, choice of global phase, anomaly cancellation, zeta determinant,
continuum limit, or complex exterior inner-product structure is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.RectangularDeterminantOverlap

open scoped Matrix

section Ring

variable {𝕜 m n : Type*} [CommRing 𝕜]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Sylvester's determinant identity removes an identity complement to a
split embedding.  The embedded matrix need not be invertible. -/
theorem det_one_add_split
    (U : Matrix m n 𝕜) (V : Matrix n m 𝕜) (hVU : V * U = 1)
    (A : Matrix n n 𝕜) :
    (1 + U * (A - 1) * V).det = A.det := by
  calc
    (1 + U * (A - 1) * V).det =
        (1 + ((A - 1) * V) * U).det := by
      rw [Matrix.mul_assoc U (A - 1) V]
      exact Matrix.det_one_add_mul_comm U ((A - 1) * V)
    _ = A.det := by
      rw [Matrix.mul_assoc (A - 1) V U, hVU, Matrix.mul_one]
      simp only [← add_sub_assoc, add_sub_cancel_left]

/-- Adding the identity on the complementary range preserves determinant.
No idempotence or invertibility assumption on `A` is required. -/
theorem det_split_complement
    (U : Matrix m n 𝕜) (V : Matrix n m 𝕜) (hVU : V * U = 1)
    (A : Matrix n n 𝕜) :
    (1 - U * V + U * A * V).det = A.det := by
  have h : 1 - U * V + U * A * V = 1 + U * (A - 1) * V := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  rw [h]
  exact det_one_add_split U V hVU A

end Ring

section Star

variable {𝕜 m n k : Type*} [CommRing 𝕜] [StarRing 𝕜]
  [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

/-- The ambient range matrix of a frame.  It is an idempotent when the
frame has orthonormal columns, as expressed by `Fᴴ * F = 1`. -/
def frameRange (F : Matrix m k 𝕜) : Matrix m m 𝕜 := F * Fᴴ

/-- The finite cross-space operator in independently chosen source and
target frames of the same occupied rank. -/
def compression (D : Matrix m n 𝕜) (L : Matrix m k 𝕜)
    (R : Matrix n k 𝕜) : Matrix k k 𝕜 := Lᴴ * D * R

/-- The finite overlap matrix of two frames in a common ambient carrier. -/
def overlap (L R : Matrix m k 𝕜) : Matrix k k 𝕜 := Lᴴ * R

omit [Fintype m] [DecidableEq m] [DecidableEq k] in
theorem frameRange_conjTranspose (F : Matrix m k 𝕜) :
    (frameRange F)ᴴ = frameRange F := by
  simp only [frameRange, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

omit [DecidableEq m] in
theorem frameRange_idempotent (F : Matrix m k 𝕜) (hF : Fᴴ * F = 1) :
    frameRange F * frameRange F = frameRange F := by
  calc
    frameRange F * frameRange F = F * (Fᴴ * F) * Fᴴ := by
      simp only [frameRange, Matrix.mul_assoc]
    _ = frameRange F := by
      simp only [hF, Matrix.mul_one, frameRange]

omit [Fintype k] [DecidableEq k] in
@[simp]
theorem compression_one (L R : Matrix m k 𝕜) :
    compression (1 : Matrix m m 𝕜) L R = overlap L R := by
  simp only [compression, overlap, Matrix.mul_one]

omit [DecidableEq m] [DecidableEq n] [DecidableEq k] in
/-- Independent frame changes act on the two sides in their actual order. -/
theorem compression_frameChange (D : Matrix m n 𝕜)
    (L : Matrix m k 𝕜) (R : Matrix n k 𝕜) (U V : Matrix k k 𝕜) :
    compression D (L * U) (R * V) = Uᴴ * compression D L R * V := by
  simp only [compression, Matrix.conjTranspose_mul, Matrix.mul_assoc]

omit [DecidableEq m] [DecidableEq n] in
/-- The scalar determinant carries the target conjugate character and the
source character.  This is a frame-coordinate law, not an anomaly theorem. -/
theorem det_compression_frameChange (D : Matrix m n 𝕜)
    (L : Matrix m k 𝕜) (R : Matrix n k 𝕜) (U V : Matrix k k 𝕜) :
    (compression D (L * U) (R * V)).det =
      star U.det * (compression D L R).det * V.det := by
  rw [compression_frameChange, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose]

omit [DecidableEq m] [DecidableEq k] in
theorem overlap_frameChange (L R : Matrix m k 𝕜) (U V : Matrix k k 𝕜) :
    overlap (L * U) (R * V) = Uᴴ * overlap L R * V := by
  simp only [overlap, Matrix.conjTranspose_mul, Matrix.mul_assoc]

omit [DecidableEq m] in
theorem det_overlap_frameChange (L R : Matrix m k 𝕜) (U V : Matrix k k 𝕜) :
    (overlap (L * U) (R * V)).det =
      star U.det * (overlap L R).det * V.det := by
  rw [overlap_frameChange, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose]

omit [DecidableEq m] [DecidableEq n] [DecidableEq k] in
/-- The target range matrix is present in the Gram operator of a compression. -/
theorem compression_gram (D : Matrix m n 𝕜)
    (L : Matrix m k 𝕜) (R : Matrix n k 𝕜) :
    (compression D L R)ᴴ * compression D L R =
      Rᴴ * Dᴴ * frameRange L * D * R := by
  simp only [compression, frameRange, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

omit [DecidableEq m] [DecidableEq n] [DecidableEq k] in
/-- The target range matrix can be removed only after its action on the
compressed image is identified with the identity. -/
theorem compression_gram_of_image (D : Matrix m n 𝕜)
    (L : Matrix m k 𝕜) (R : Matrix n k 𝕜)
    (hImage : frameRange L * (D * R) = D * R) :
    (compression D L R)ᴴ * compression D L R = Rᴴ * Dᴴ * D * R := by
  rw [compression_gram]
  simpa only [Matrix.mul_assoc] using
    congrArg (fun X : Matrix m k 𝕜 => Rᴴ * Dᴴ * X) hImage

omit [DecidableEq m] [DecidableEq n] in
/-- An actual intertwining equation and an isometric source frame supply
the image condition used by the compressed Gram identity. -/
theorem compression_gram_of_intertwining (D : Matrix m n 𝕜)
    (L : Matrix m k 𝕜) (R : Matrix n k 𝕜)
    (hR : Rᴴ * R = 1) (hD : frameRange L * D = D * frameRange R) :
    (compression D L R)ᴴ * compression D L R = Rᴴ * Dᴴ * D * R := by
  apply compression_gram_of_image
  calc
    frameRange L * (D * R) = (frameRange L * D) * R :=
      (Matrix.mul_assoc _ _ _).symm
    _ = (D * frameRange R) * R := by rw [hD]
    _ = D * R := by
      simp only [frameRange, Matrix.mul_assoc, hR, Matrix.mul_one]

omit [DecidableEq m] [DecidableEq n] in
theorem det_compression_gram (D : Matrix m n 𝕜)
    (L : Matrix m k 𝕜) (R : Matrix n k 𝕜) :
    (Rᴴ * Dᴴ * frameRange L * D * R).det =
      star (compression D L R).det * (compression D L R).det := by
  rw [← compression_gram D L R, Matrix.det_mul, Matrix.det_conjTranspose]

omit [DecidableEq m] [DecidableEq n] in
theorem det_compression_gram_of_image (D : Matrix m n 𝕜)
    (L : Matrix m k 𝕜) (R : Matrix n k 𝕜)
    (hImage : frameRange L * (D * R) = D * R) :
    (Rᴴ * Dᴴ * D * R).det =
      star (compression D L R).det * (compression D L R).det := by
  rw [← compression_gram_of_image D L R hImage, Matrix.det_mul,
    Matrix.det_conjTranspose]

omit [DecidableEq m] [DecidableEq k] in
theorem overlap_gram (L R : Matrix m k 𝕜) :
    (overlap L R)ᴴ * overlap L R = Rᴴ * frameRange L * R := by
  simp only [overlap, frameRange, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

omit [DecidableEq m] in
theorem det_overlap_gram (L R : Matrix m k 𝕜) :
    (Rᴴ * frameRange L * R).det =
      star (overlap L R).det * (overlap L R).det := by
  rw [← overlap_gram L R, Matrix.det_mul, Matrix.det_conjTranspose]

/-- The ambient determinant depends on the two range matrices, not on the
chosen right frame.  Orthogonality of the left frame is not needed for this
identity; it is needed to interpret its range matrix as a projector. -/
theorem det_projector_overlap (L R : Matrix m k 𝕜) (hR : Rᴴ * R = 1) :
    (1 - frameRange R + frameRange R * frameRange L * frameRange R).det =
      star (overlap L R).det * (overlap L R).det := by
  calc
    (1 - frameRange R + frameRange R * frameRange L * frameRange R).det =
        (1 - R * Rᴴ + R * (Rᴴ * frameRange L * R) * Rᴴ).det := by
      apply congrArg Matrix.det
      simp only [frameRange, Matrix.mul_assoc]
    _ = (Rᴴ * frameRange L * R).det :=
      det_split_complement R Rᴴ hR (Rᴴ * frameRange L * R)
    _ = star (overlap L R).det * (overlap L R).det := det_overlap_gram L R

omit [Fintype k] [DecidableEq k] in
/-- Simultaneously transporting the operator and its frames preserves the
compression itself.  Only the displayed two isometry identities are used. -/
theorem compression_gauge (D : Matrix m n 𝕜)
    (L : Matrix m k 𝕜) (R : Matrix n k 𝕜)
    (G : Matrix m m 𝕜) (H : Matrix n n 𝕜)
    (hG : Gᴴ * G = 1) (hH : Hᴴ * H = 1) :
    compression (G * D * Hᴴ) (G * L) (H * R) = compression D L R := by
  calc
    compression (G * D * Hᴴ) (G * L) (H * R) =
        Lᴴ * (Gᴴ * G) * D * (Hᴴ * H) * R := by
      simp only [compression, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = compression D L R := by
      rw [hG, hH]
      simp only [compression, Matrix.mul_one]

omit [Fintype k] [DecidableEq k] in
theorem overlap_gauge (L R : Matrix m k 𝕜) (G : Matrix m m 𝕜)
    (hG : Gᴴ * G = 1) :
    overlap (G * L) (G * R) = overlap L R := by
  calc
    overlap (G * L) (G * R) = Lᴴ * (Gᴴ * G) * R := by
      simp only [overlap, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = overlap L R := by
      simp only [hG, Matrix.mul_one, overlap]

end Star

section RCLike

variable {𝕜 m n k : Type*} [RCLike 𝕜]
  [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

/-- A square isometric frame has a determinant of norm one. -/
theorem norm_det_eq_one_of_isometry (U : Matrix k k 𝕜) (hU : Uᴴ * U = 1) :
    ‖U.det‖ = 1 := by
  have h : star U.det * U.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] using
      congrArg Matrix.det hU
  apply CStarRing.norm_of_mem_unitary
  exact ⟨h, by simpa only [mul_comm] using h⟩

omit [DecidableEq m] [DecidableEq n] in
/-- Isometric changes of the source and target frames preserve the modulus. -/
theorem norm_det_compression_frameChange (D : Matrix m n 𝕜)
    (L : Matrix m k 𝕜) (R : Matrix n k 𝕜) (U V : Matrix k k 𝕜)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    ‖(compression D (L * U) (R * V)).det‖ = ‖(compression D L R).det‖ := by
  rw [det_compression_frameChange, norm_mul, norm_mul, norm_star,
    norm_det_eq_one_of_isometry U hU, norm_det_eq_one_of_isometry V hV,
    one_mul, mul_one]

omit [DecidableEq m] in
theorem norm_det_overlap_frameChange (L R : Matrix m k 𝕜) (U V : Matrix k k 𝕜)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    ‖(overlap (L * U) (R * V)).det‖ = ‖(overlap L R).det‖ := by
  rw [det_overlap_frameChange, norm_mul, norm_mul, norm_star,
    norm_det_eq_one_of_isometry U hU, norm_det_eq_one_of_isometry V hV,
    one_mul, mul_one]

omit [DecidableEq m] [DecidableEq n] in
/-- The Gram determinant is the real squared modulus, including zero. -/
theorem det_compression_gram_eq_norm_sq (D : Matrix m n 𝕜)
    (L : Matrix m k 𝕜) (R : Matrix n k 𝕜) :
    (Rᴴ * Dᴴ * frameRange L * D * R).det =
      ((‖(compression D L R).det‖ ^ 2 : ℝ) : 𝕜) := by
  rw [det_compression_gram]
  simpa only [RCLike.star_def, RCLike.ofReal_pow] using
    RCLike.conj_mul (compression D L R).det

omit [DecidableEq m] [DecidableEq n] in
theorem det_compression_gram_of_image_eq_norm_sq (D : Matrix m n 𝕜)
    (L : Matrix m k 𝕜) (R : Matrix n k 𝕜)
    (hImage : frameRange L * (D * R) = D * R) :
    (Rᴴ * Dᴴ * D * R).det = ((‖(compression D L R).det‖ ^ 2 : ℝ) : 𝕜) := by
  rw [det_compression_gram_of_image D L R hImage]
  simpa only [RCLike.star_def, RCLike.ofReal_pow] using
    RCLike.conj_mul (compression D L R).det

theorem det_projector_overlap_eq_norm_sq (L R : Matrix m k 𝕜)
    (hR : Rᴴ * R = 1) :
    (1 - frameRange R + frameRange R * frameRange L * frameRange R).det =
      ((‖(overlap L R).det‖ ^ 2 : ℝ) : 𝕜) := by
  rw [det_projector_overlap L R hR]
  simpa only [RCLike.star_def, RCLike.ofReal_pow] using
    RCLike.conj_mul (overlap L R).det

end RCLike

end InfoGeometry.OperatorAlgebra.RectangularDeterminantOverlap
