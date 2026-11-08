import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.NCG.BerezinianSuperdeterminant
import InfoGeometry.Canonical.SouriauOnsagerBKMBridge
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

/-!
# Doubled operator / graded block-matrix interoperability

The canonical doubled carrier is a product of two operator algebras, not an
algebra structure in its own right.  Its even (sector-preserving) realization
is therefore the diagonal block embedding.  This file records the native
transport to the existing finite graded block-matrix owner.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace InfoGeometry.Canonical.DoubledOperatorMatrixGradingBridge

open Matrix
open InfoGeometry.Krein
open InfoGeometry.NCG
open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {n : ℕ}

abbrev Op (n : ℕ) := FiniteOperatorAlgebra n
abbrev Block (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ
abbrev Sector (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

variable [InnerProductSpace ℝ (Op n)] [CompleteSpace (Op n)]

/-- Even/block-diagonal realization of a doubled pair of operators. -/
def blockMatrixOfDoubled (u : DoubledSpace (Op n)) : Block n :=
  fromBlocks
    (matrixOfOp (WithLp.fst u))
    0
    0
    (matrixOfOp (WithLp.snd u))

@[simp] theorem blockMatrixOfDoubled_to_doubled (A B : Op n) :
    blockMatrixOfDoubled (to_doubled A B) =
      fromBlocks (matrixOfOp A) 0 0 (matrixOfOp B) := by
  rfl

theorem blockMatrixOfDoubled_add (u v : DoubledSpace (Op n)) :
    blockMatrixOfDoubled (u + v) =
      blockMatrixOfDoubled u + blockMatrixOfDoubled v := by
  ext i j <;> cases i <;> cases j <;> simp [blockMatrixOfDoubled]

/-- Componentwise multiplication is transported to block multiplication. -/
theorem blockMatrixOfDoubled_mul
    (A B C D : Op n) :
    blockMatrixOfDoubled (to_doubled (A.comp B) (C.comp D)) =
      blockMatrixOfDoubled (to_doubled A C) *
        blockMatrixOfDoubled (to_doubled B D) := by
  rw [blockMatrixOfDoubled_to_doubled, blockMatrixOfDoubled_to_doubled,
    blockMatrixOfDoubled_to_doubled]
  rw [matrixOfOp_comp, matrixOfOp_comp]
  simp [Matrix.fromBlocks_multiply]

/-- The block realization preserves the involutive star sectorwise. -/
theorem blockMatrixOfDoubled_star
    (A B : Op n) :
    blockMatrixOfDoubled
        (to_doubled (ContinuousLinearMap.adjoint A)
          (ContinuousLinearMap.adjoint B)) =
      (blockMatrixOfDoubled (to_doubled A B))ᴴ := by
  rw [blockMatrixOfDoubled_to_doubled, blockMatrixOfDoubled_to_doubled]
  simp [Matrix.fromBlocks_conjTranspose]

/-- Existing `spectral_epsilon` becomes the graded sign on the odd block. -/
theorem blockMatrixOfDoubled_spectral_epsilon
    (A B : Op n) :
    blockMatrixOfDoubled (spectral_epsilon (E := Op n) (to_doubled A B)) =
      fromBlocks (matrixOfOp A) 0 0 (-matrixOfOp B) := by
  rfl

/-- Existing graded supertrace reads the difference of sector traces. -/
theorem superTrace_blockMatrixOfDoubled
    (A B : Op n) :
    superTrace (blockMatrixOfDoubled (to_doubled A B)) =
      Matrix.trace (matrixOfOp A) - Matrix.trace (matrixOfOp B) := by
  rw [blockMatrixOfDoubled_to_doubled]
  exact superTrace_blockDiag_eq (matrixOfOp A) (matrixOfOp B)

/-- Existing Berezinian Schur owner applies to the transported even block. -/
theorem berezinianSchur_blockMatrixOfDoubled
    (A B : Op n) (invB : Sector n) (invDetB : ℂ) :
    berezinianSchur
        (matrixOfOp A) 0 0 (matrixOfOp B) invB invDetB =
      berezinianBlockDiag (matrixOfOp A) (matrixOfOp B) invDetB := by
  exact berezinianSchur_diag (matrixOfOp A) (matrixOfOp B) invB invDetB

end InfoGeometry.Canonical.DoubledOperatorMatrixGradingBridge
