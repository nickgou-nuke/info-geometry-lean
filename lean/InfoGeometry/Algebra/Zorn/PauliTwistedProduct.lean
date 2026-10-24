/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.PauliBlockCoordinates

/-! # An explicit nonassociative Pauli-block product

The product below is independently specified by block traces and commutators,
not defined by decoding, multiplying octonions, and re-encoding. Its agreement
with the native Zorn product is proved. This is a mathematical convention;
no identification with an uninspected numbered paper formula is claimed.
-/

noncomputable section
namespace InfoGeometry.Algebra.Zorn.PauliBlock

open InfoGeometry.Algebra
open InfoGeometry.Canonical.ZornBdGDerivationBridge.PauliSolderedCrossProductBridge

/-- Explicit trace/commutator product on ambient four-by-four matrices. -/
def twistedProduct (A B : Mat4) : Mat4 :=
  let a := A (.inl 0) (.inl 0)
  let b := A (.inr 0) (.inr 0)
  let c := B (.inl 0) (.inl 0)
  let d := B (.inr 0) (.inr 0)
  let P := A.toBlocks₁₂
  let Q := A.toBlocks₂₁
  let U := B.toBlocks₁₂
  let V := B.toBlocks₂₁
  Matrix.fromBlocks
    ((a * c + Matrix.trace (P * V) / 2) • (1 : Mat2))
    (fun i j => a * U i j + d * P i j - (Q * V - V * Q) i j / 2)
    (fun i j => c * Q i j + b * V i j - (P * U - U * P) i j / 2)
    ((b * d + Matrix.trace (Q * U) / 2) • (1 : Mat2))

set_option maxHeartbeats 1000000 in
/-- Genuine multiplicative compatibility, using the existing Zorn multiplication. -/
theorem twistedProduct_encode (X Y : ZornVectorMatrix ℂ) :
    twistedProduct (encode X) (encode Y) = encode (ZornVectorMatrix.mul X Y) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j
  all_goals simp [twistedProduct, encode, Matrix.fromBlocks, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₁, Matrix.mul_apply, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross,
    Fin.sum_univ_three, sigmaVec]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq, pow_succ]
  all_goals ring

/-- The eight-dimensional matrix image is closed under this product. -/
theorem twistedProduct_mem (A B : Space) :
    twistedProduct A.1 B.1 ∈ LinearMap.range encodeLinear := by
  obtain ⟨X, hX⟩ := A.2
  obtain ⟨Y, hY⟩ := B.2
  refine ⟨ZornVectorMatrix.mul X Y, ?_⟩
  change encode (ZornVectorMatrix.mul X Y) = twistedProduct A.1 B.1
  rw [← hX, ← hY]
  exact (twistedProduct_encode X Y).symm

def spaceMul (A B : Space) : Space := ⟨twistedProduct A.1 B.1, twistedProduct_mem A B⟩

@[simp] theorem spaceMul_coordinateEquiv (X Y : ZornVectorMatrix ℂ) :
    spaceMul (coordinateEquiv X) (coordinateEquiv Y) =
      coordinateEquiv (ZornVectorMatrix.mul X Y) := by
  apply Subtype.ext
  exact twistedProduct_encode X Y

theorem spaceMul_one (A : Space) : spaceMul A (coordinateEquiv ZornVectorMatrix.one) = A := by
  obtain ⟨X, rfl⟩ := coordinateEquiv.surjective A
  rw [spaceMul_coordinateEquiv, ZornVectorMatrix.mul_one]

theorem one_spaceMul (A : Space) : spaceMul (coordinateEquiv ZornVectorMatrix.one) A = A := by
  obtain ⟨X, rfl⟩ := coordinateEquiv.surjective A
  rw [spaceMul_coordinateEquiv, ZornVectorMatrix.one_mul]

/-- Ordinary associative multiplication cannot replace the explicit twisted product. -/
theorem ordinary_product_not_twisted :
    encode (ZornVectorMatrix.U 0) * encode (ZornVectorMatrix.U 1) ≠
      twistedProduct (encode (ZornVectorMatrix.U 0)) (encode (ZornVectorMatrix.U 1)) := by
  rw [twistedProduct_encode]
  intro h
  have hEntry := congrArg (fun M : Mat4 => M (.inr 0) (.inl 0)) h
  norm_num [encode, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, ZornVectorMatrix.U, ZornVectorMatrix.mul,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three, sigmaVec] at hEntry
  exact Complex.I_ne_zero hEntry.symm

/-- The matrix carrier really retains the nonassociativity of the octonions. -/
theorem spaceMul_nonassociative :
    ∃ A B C : Space, spaceMul (spaceMul A B) C ≠ spaceMul A (spaceMul B C) := by
  refine ⟨coordinateEquiv (ZornVectorMatrix.U 0), coordinateEquiv (ZornVectorMatrix.U 1),
    coordinateEquiv (ZornVectorMatrix.U 2), ?_⟩
  simpa only [spaceMul_coordinateEquiv, ne_eq, coordinateEquiv.injective.eq_iff] using
    ZornVectorMatrix.nonassociative_witness (R := ℂ)

end InfoGeometry.Algebra.Zorn.PauliBlock
