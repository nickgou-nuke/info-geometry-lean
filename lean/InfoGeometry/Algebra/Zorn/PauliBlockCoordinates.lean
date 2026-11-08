/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Canonical.ZornBdGDerivationBridge
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Faithful Pauli-block coordinates for complex Zorn matrices

The four-dimensional matrix index is `Fin 2 ⊕ Fin 2`. We reuse the native
Pauli soldering and keep ordinary matrix multiplication separate from Zorn
multiplication. No multiplicativity is asserted in this coordinate file.
-/

noncomputable section
namespace InfoGeometry.Algebra.Zorn.PauliBlock

open InfoGeometry.Algebra
open InfoGeometry.Canonical.ZornBdGDerivationBridge.PauliSolderedCrossProductBridge

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev Mat4 := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ

/-- The off-diagonal phases are part of the convention, not a matrix algebra embedding. -/
def encode (X : ZornVectorMatrix ℂ) : Mat4 :=
  Matrix.fromBlocks (X.a • (1 : Mat2)) (fun i j => -Complex.I * sigmaVec X.v i j)
    (fun i j => Complex.I * sigmaVec X.w i j) (X.b • (1 : Mat2))

def encodeLinear : ZornVectorMatrix ℂ →ₗ[ℂ] Mat4 where
  toFun := encode
  map_add' X Y := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      dsimp [encode, Matrix.fromBlocks, sigmaVec] <;> ring
  map_smul' r X := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      dsimp [encode, Matrix.fromBlocks, sigmaVec] <;> ring

/-- Explicit inverse coordinates, meaningful on all matrices and inverse on the image. -/
def decode (A : Mat4) : ZornVectorMatrix ℂ :=
  ⟨A (.inl 0) (.inl 0),
   ![(Complex.I / 2) * (A (.inl 0) (.inr 1) + A (.inl 1) (.inr 0)),
     (A (.inl 1) (.inr 0) - A (.inl 0) (.inr 1)) / 2,
     Complex.I * A (.inl 0) (.inr 0)],
   ![(-Complex.I / 2) * (A (.inr 0) (.inl 1) + A (.inr 1) (.inl 0)),
     (A (.inr 0) (.inl 1) - A (.inr 1) (.inl 0)) / 2,
     -Complex.I * A (.inr 0) (.inl 0)],
   A (.inr 0) (.inr 0)⟩

@[simp] theorem decode_encode (X : ZornVectorMatrix ℂ) : decode (encode X) = X := by
  ext i
  all_goals try fin_cases i
  all_goals dsimp [decode, encode, Matrix.fromBlocks, sigmaVec]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

theorem encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

/-- An actual submodule of four-by-four matrices, not a second octonion record. -/
abbrev Space := LinearMap.range encodeLinear

/-- The inverse is the displayed decoder, rather than a postulated inverse. -/
def coordinateEquiv : ZornVectorMatrix ℂ ≃ₗ[ℂ] Space :=
  LinearEquiv.ofLeftInverse (f := encodeLinear) (g := decode) decode_encode

@[simp] theorem coordinateEquiv_apply (X : ZornVectorMatrix ℂ) :
    (coordinateEquiv X).1 = encode X := rfl

@[simp] theorem coordinateEquiv_symm_apply (A : Space) :
    coordinateEquiv.symm A = decode A.1 := rfl

/-- Every matrix in the image is reconstructed from its explicit coordinates. -/
theorem encode_decode (A : Space) : encode (decode A.1) = A.1 :=
  congrArg Subtype.val (coordinateEquiv.apply_symm_apply A)

/-- The chosen chirality matrix. Its sign fixes which idempotent is called positive. -/
def gamma5 : Mat4 := Matrix.fromBlocks (-1 : Mat2) 0 0 1

@[simp] theorem encode_one : encode (ZornVectorMatrix.one : ZornVectorMatrix ℂ) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    dsimp [encode, ZornVectorMatrix.one, Matrix.fromBlocks, sigmaVec] <;> norm_num

theorem encode_E11 : encode (ZornVectorMatrix.E11 : ZornVectorMatrix ℂ) =
    (1 / 2 : ℂ) • (1 - gamma5) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    dsimp [encode, gamma5, ZornVectorMatrix.E11, Matrix.fromBlocks, sigmaVec] <;> norm_num

theorem encode_E22 : encode (ZornVectorMatrix.E22 : ZornVectorMatrix ℂ) =
    (1 / 2 : ℂ) • (1 + gamma5) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    dsimp [encode, gamma5, ZornVectorMatrix.E22, Matrix.fromBlocks, sigmaVec] <;> norm_num

end InfoGeometry.Algebra.Zorn.PauliBlock
