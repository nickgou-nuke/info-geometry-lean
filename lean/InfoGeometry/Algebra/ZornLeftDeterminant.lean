/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornLeftCAR
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic

/-!
# Determinant of the genuine Zorn left action

The source carrier and product are `ZornVectorMatrix ℝ` and its nonassociative
`mul`. The matrix below represents the already owned associative endomorphism
`ZornLeftCAR.leftMultiplication`; its rows and columns have eight indices,
grouped as `(a,v₀,v₁,v₂)` and `(b,w₀,w₁,w₂)`.

The determinant proof uses exact block Gaussian elimination and a four-swap
permutation for the zero-pivot case. No invertibility or nonzero-coordinate
assumption remains in the result.
-/

namespace InfoGeometry.Algebra.ZornLeftDeterminant

open InfoGeometry.Algebra

noncomputable section

abbrev Z := ZornVectorMatrix ℝ
abbrev CoordinateIndex := Fin 4 ⊕ Fin 4
abbrev Block := Matrix (Fin 4) (Fin 4) ℝ

/-- The two four-coordinate rows are coordinates of the existing carrier. -/
def coordinates : Z ≃ₗ[ℝ] (CoordinateIndex → ℝ) where
  toFun z := Sum.elim ![z.a, z.v 0, z.v 1, z.v 2]
    ![z.b, z.w 0, z.w 1, z.w 2]
  invFun c :=
    ⟨c (.inl 0), ![c (.inl 1), c (.inl 2), c (.inl 3)],
      ![c (.inr 1), c (.inr 2), c (.inr 3)], c (.inr 0)⟩
  left_inv z := by
    ext i <;> (try fin_cases i) <;> rfl
  right_inv c := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  map_add' z w := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  map_smul' r z := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl

theorem coordinateIndex_card : Fintype.card CoordinateIndex = 8 := by decide

/-- Off-diagonal block from the dual coordinates to the primal coordinates. -/
def upperRight (z : Z) : Block :=
  !![0, z.v 0, z.v 1, z.v 2;
     z.v 0, 0, z.w 2, -z.w 1;
     z.v 1, -z.w 2, 0, z.w 0;
     z.v 2, z.w 1, -z.w 0, 0]

/-- Off-diagonal block from the primal coordinates to the dual coordinates. -/
def lowerLeft (z : Z) : Block :=
  !![0, z.w 0, z.w 1, z.w 2;
     z.w 0, 0, -z.v 2, z.v 1;
     z.w 1, z.v 2, 0, -z.v 0;
     z.w 2, -z.v 1, z.v 0, 0]

/-- The actual eight-dimensional left action in the displayed coordinates. -/
def leftMatrix (z : Z) : Matrix CoordinateIndex CoordinateIndex ℝ :=
  Matrix.fromBlocks (z.a • (1 : Block)) (upperRight z)
    (lowerLeft z) (z.b • (1 : Block))

theorem lowerLeft_mul_upperRight (z : Z) :
    lowerLeft z * upperRight z = ZornVec3.dot z.v z.w • (1 : Block) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerLeft, upperRight, Matrix.mul_apply, Fin.sum_univ_four,
      ZornVec3.dot, Fin.sum_univ_three] <;> ring

theorem upperRight_mul_lowerLeft (z : Z) :
    upperRight z * lowerLeft z = ZornVec3.dot z.v z.w • (1 : Block) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerLeft, upperRight, Matrix.mul_apply, Fin.sum_univ_four,
      ZornVec3.dot, Fin.sum_univ_three] <;> ring

/-- This identifies the explicit matrix with the owned Zorn multiplication. -/
theorem leftMatrix_mulVec_coordinates (z w : Z) :
    (leftMatrix z).mulVec (coordinates w) =
      coordinates (ZornLeftCAR.leftMultiplication z w) := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [leftMatrix, upperRight, lowerLeft, coordinates, Matrix.mulVec,
      dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four,
      ZornLeftCAR.leftMultiplication_apply, ZornVectorMatrix.mul,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

theorem leftMatrix_toLin :
    ∀ z : Z, Matrix.toLin' (leftMatrix z) =
      (coordinates : Z →ₗ[ℝ] (CoordinateIndex → ℝ)) ∘ₗ
        ZornLeftCAR.leftMultiplication z ∘ₗ
        (coordinates.symm : (CoordinateIndex → ℝ) →ₗ[ℝ] Z) := by
  intro z
  apply LinearMap.ext
  intro c
  change (leftMatrix z).mulVec c =
    coordinates (ZornLeftCAR.leftMultiplication z (coordinates.symm c))
  simpa only [LinearEquiv.apply_symm_apply] using
    leftMatrix_mulVec_coordinates z (coordinates.symm c)

private theorem sign_sumComm_four :
    Equiv.Perm.sign (Equiv.sumComm (Fin 4) (Fin 4)) = 1 := by
  let s0 : Equiv.Perm CoordinateIndex := Equiv.swap (.inl 0) (.inr 0)
  let s1 : Equiv.Perm CoordinateIndex := Equiv.swap (.inl 1) (.inr 1)
  let s2 : Equiv.Perm CoordinateIndex := Equiv.swap (.inl 2) (.inr 2)
  let s3 : Equiv.Perm CoordinateIndex := Equiv.swap (.inl 3) (.inr 3)
  have h : Equiv.sumComm (Fin 4) (Fin 4) = s0 * s1 * s2 * s3 := by
    ext i
    rcases i with i | i <;> fin_cases i <;> decide
  rw [h]
  simp [s0, s1, s2, s3, Equiv.Perm.sign_swap]

/-- Exact scalar-diagonal block determinant, including a zero first pivot. -/
theorem det_scalar_blocks (a b s : ℝ) (B C : Block)
    (hCB : C * B = s • (1 : Block)) :
    (Matrix.fromBlocks (a • (1 : Block)) B C (b • (1 : Block))).det =
      (a * b - s) ^ 4 := by
  by_cases ha : a = 0
  · subst a
    simp only [zero_smul, zero_mul, zero_sub]
    have hrow :
        (Matrix.fromBlocks (0 : Block) B C (b • (1 : Block))).submatrix
            (Equiv.sumComm (Fin 4) (Fin 4)) id =
          Matrix.fromBlocks C (b • (1 : Block)) (0 : Block) B := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> rfl
    have hdet : (Matrix.fromBlocks C (b • (1 : Block)) (0 : Block) B).det =
        (Matrix.fromBlocks (0 : Block) B C (b • (1 : Block))).det := by
      simpa [hrow, sign_sumComm_four] using
        Matrix.det_permute (Equiv.sumComm (Fin 4) (Fin 4))
          (Matrix.fromBlocks (0 : Block) B C (b • (1 : Block)))
    calc
      (Matrix.fromBlocks (0 : Block) B C (b • (1 : Block))).det =
          (Matrix.fromBlocks C (b • (1 : Block)) (0 : Block) B).det := hdet.symm
      _ = C.det * B.det := Matrix.det_fromBlocks_zero₂₁ _ _ _
      _ = (C * B).det := (Matrix.det_mul C B).symm
      _ = s ^ 4 := by simp [hCB, Matrix.det_smul]
      _ = (-s) ^ 4 := by ring
  · have hAB : (a • (1 : Block)) * (a⁻¹ • B) = B := by
      rw [smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ ha, one_smul]
    have hD : C * (a⁻¹ • B) + (b - a⁻¹ * s) • (1 : Block) =
        b • (1 : Block) := by
      rw [mul_smul_comm, hCB, smul_smul, ← add_smul]
      congr 1
      ring
    have hfactor :
        Matrix.fromBlocks (a • (1 : Block)) B C (b • (1 : Block)) =
          Matrix.fromBlocks (a • (1 : Block)) (0 : Block) C (1 : Block) *
            Matrix.fromBlocks (1 : Block) (a⁻¹ • B) (0 : Block)
              ((b - a⁻¹ * s) • (1 : Block)) := by
      rw [Matrix.fromBlocks_multiply]
      simp only [mul_one, one_mul, zero_mul, mul_zero, add_zero, zero_add]
      rw [hAB, hD]
    rw [hfactor, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_fromBlocks_zero₂₁]
    simp only [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, one_mul]
    rw [← mul_pow]
    congr 1
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

/-- The determinant is the fourth power of the split-octonion quadratic norm. -/
theorem leftMatrix_det (z : Z) :
    (leftMatrix z).det = ZornVectorMatrix.norm z ^ 4 := by
  exact det_scalar_blocks z.a z.b (ZornVec3.dot z.v z.w)
    (upperRight z) (lowerLeft z) (lowerLeft_mul_upperRight z)

/-- The same identity on the already owned associative endomorphism carrier. -/
theorem leftMultiplication_det (z : Z) :
    LinearMap.det (ZornLeftCAR.leftMultiplication z) = ZornVectorMatrix.norm z ^ 4 := by
  calc
    LinearMap.det (ZornLeftCAR.leftMultiplication z) =
        LinearMap.det ((coordinates : Z →ₗ[ℝ] (CoordinateIndex → ℝ)) ∘ₗ
          ZornLeftCAR.leftMultiplication z ∘ₗ
          (coordinates.symm : (CoordinateIndex → ℝ) →ₗ[ℝ] Z)) :=
      (LinearMap.det_conj (ZornLeftCAR.leftMultiplication z) coordinates).symm
    _ = LinearMap.det (Matrix.toLin' (leftMatrix z)) :=
      congrArg LinearMap.det (leftMatrix_toLin z).symm
    _ = (leftMatrix z).det := LinearMap.det_toLin' _
    _ = ZornVectorMatrix.norm z ^ 4 := leftMatrix_det z

theorem leftMatrix_det_eq_zero_iff (z : Z) :
    (leftMatrix z).det = 0 ↔ ZornVectorMatrix.norm z = 0 := by
  rw [leftMatrix_det]
  exact pow_eq_zero_iff (by decide)

end
end InfoGeometry.Algebra.ZornLeftDeterminant
