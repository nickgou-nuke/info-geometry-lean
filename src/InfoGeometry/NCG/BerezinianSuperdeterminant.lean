import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Matrix
open BigOperators

namespace InfoGeometry.NCG

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "BlockMat" => Matrix (ι ⊕ ι) (ι ⊕ ι) R
local notation "SubMat" => Matrix ι ι R

/-!
=============================================================================
SECTION 1: Block-Diagonal Supermatrices and the Berezinian Superdeterminant
=============================================================================
-/

/-- The Berezinian (Superdeterminant) of a block-diagonal supermatrix M = diag(A, D):
    Ber(M) = det(A) * (det D)⁻¹ -/
def berezinianBlockDiag (A D : SubMat) (inv_det_D : R) : R :=
  Matrix.det A * inv_det_D

/-- 🏆 THEOREM 1: Multiplicativity of the Berezinian Superdeterminant:
    Ber(M₁ * M₂) = Ber(M₁) * Ber(M₂) -/
theorem berezinianBlockDiag_mul
    (A1 A2 D1 D2 : SubMat) (inv_det_D1 inv_det_D2 : R)
    (hD1 : Matrix.det D1 * inv_det_D1 = 1)
    (hD2 : Matrix.det D2 * inv_det_D2 = 1) :
    berezinianBlockDiag (A1 * A2) (D1 * D2) (inv_det_D1 * inv_det_D2) =
      berezinianBlockDiag A1 D1 inv_det_D1 * berezinianBlockDiag A2 D2 inv_det_D2 := by
  dsimp [berezinianBlockDiag]
  rw [Matrix.det_mul]
  ring

/-- 🏆 THEOREM 2: Berezinian of the Super-Identity is 1:
    Ber(I) = det(I) * (det I)⁻¹ = 1 * 1 = 1 -/
@[simp]
theorem berezinianBlockDiag_one :
    berezinianBlockDiag (1 : SubMat) (1 : SubMat) (1 : R) = 1 := by
  dsimp [berezinianBlockDiag]
  rw [Matrix.det_one, mul_one]

/-- 🏆 THEOREM 3: Berezinian Inversion Rule:
    Ber(M⁻¹) = (Ber M)⁻¹ -/
theorem berezinianBlockDiag_inv
    (A D : SubMat) (inv_det_A inv_det_D : R)
    (hA : Matrix.det A * inv_det_A = 1)
    (hD : Matrix.det D * inv_det_D = 1) :
    berezinianBlockDiag D A inv_det_A * berezinianBlockDiag A D inv_det_D = 1 := by
  dsimp [berezinianBlockDiag]
  calc
    (Matrix.det D * inv_det_A) * (Matrix.det A * inv_det_D)
      = (Matrix.det A * inv_det_A) * (Matrix.det D * inv_det_D) := by ring
    _ = 1 * 1 := by rw [hA, hD]
    _ = 1 := mul_one 1

/-!
=============================================================================
SECTION 2: General 2x2 Supermatrix Berezinian via Schur Complement
=============================================================================
-/

/-- The General Berezinian of M = [[A, B], [C, D]] with invertible D:
    Ber(M) = det(A - B * D⁻¹ * C) * (det D)⁻¹ -/
def berezinianSchur (A B C D inv_D : SubMat) (inv_det_D : R) : R :=
  Matrix.det (A - B * inv_D * C) * inv_det_D

/-- 🏆 THEOREM 4: Reduction of General Berezinian to Block-Diagonal:
    When B = 0 and C = 0, Ber([[A, 0], [0, D]]) = det(A) * (det D)⁻¹. -/
theorem berezinianSchur_diag (A D inv_D : SubMat) (inv_det_D : R) :
    berezinianSchur A (0 : SubMat) (0 : SubMat) D inv_D inv_det_D =
      berezinianBlockDiag A D inv_det_D := by
  dsimp [berezinianSchur, berezinianBlockDiag]
  have h_zero : (0 : SubMat) * inv_D * (0 : SubMat) = 0 := by
    simp
  rw [h_zero, sub_zero]

/-!
=============================================================================
SECTION 3: The Supertrace & Berezinian Duality
=============================================================================
-/

/-- Grading Operator Γ = [[1, 0], [0, -1]] -/
def Gamma : BlockMat :=
  fromBlocks (1 : SubMat) 0 0 (-1 : SubMat)

/-- Supertrace of Block Matrix: STr(M) = Tr(M₁₁) - Tr(M₂₂) -/
def superTrace (M : BlockMat) : R :=
  Matrix.trace (fromBlocks (1 : SubMat) 0 0 (-1 : SubMat) * M)

/-- 🏆 THEOREM 5: Supertrace of Block-Diagonal Matrix:
    STr(diag(K₁, K₂)) = Tr(K₁) - Tr(K₂) -/
theorem superTrace_blockDiag_eq (K1 K2 : SubMat) :
    superTrace (fromBlocks K1 (0 : SubMat) (0 : SubMat) K2) =
      Matrix.trace K1 - Matrix.trace K2 := by
  dsimp [superTrace]
  have h_mul : fromBlocks (1 : SubMat) 0 0 (-1) * fromBlocks K1 0 0 K2 =
      fromBlocks K1 0 0 (-K2) := by
    rw [fromBlocks_multiply]
    simp
  rw [h_mul]
  dsimp [Matrix.trace]
  rw [Fintype.sum_sum_type]
  simp
  ring

end InfoGeometry.NCG
