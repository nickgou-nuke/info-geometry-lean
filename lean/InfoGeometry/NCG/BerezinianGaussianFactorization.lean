import InfoGeometry.NCG.BerezinianSuperdeterminant
import InfoGeometry.Algebra.FiniteSpinAlgebra

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Matrix

namespace InfoGeometry.NCG

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [Ring R]

local notation "BlockMat" => Matrix (ι ⊕ ι) (ι ⊕ ι) R
local notation "SubMat" => Matrix ι ι R

/-!
This file closes the algebraic block-Gaussian step behind the Schur-complement
Berezinian already defined in `BerezinianSuperdeterminant.lean`.

The block-Gaussian factorization itself (`berezinian_block_gaussian_factorization`)
holds over any associative ring `[Ring R]`. The determinant-based Berezinian
readouts specialize to a commutative ring `[CommRing R_comm]`.
-/

def berezinianUpperShear (B invD : SubMat) : BlockMat :=
  fromBlocks (1 : SubMat) (B * invD) 0 1

def berezinianLowerShear (C invD : SubMat) : BlockMat :=
  fromBlocks (1 : SubMat) 0 (invD * C) 1

def berezinianSchurDiagonal (A B C D invD : SubMat) : BlockMat :=
  fromBlocks (A - B * invD * C) 0 0 D

structure TwoSidedMatrixInverse (D invD : SubMat) : Prop where
  left_inv : invD * D = 1
  right_inv : D * invD = 1

theorem berezinian_block_gaussian_factorization
    (A B C D invD : SubMat)
    (hD : TwoSidedMatrixInverse D invD) :
    fromBlocks A B C D =
      berezinianUpperShear B invD *
        berezinianSchurDiagonal A B C D invD *
          berezinianLowerShear C invD := by
  rcases hD with ⟨hleft, hright⟩
  have hBD : B * invD * D = B := by
    rw [mul_assoc, hleft, mul_one]
  have hDC : D * (invD * C) = C := by
    rw [← mul_assoc, hright, one_mul]
  have hBDC : B * invD * D * invD * C = B * invD * C := by
    rw [hBD]
  have hAssoc : B * (invD * C) = B * invD * C := by
    rw [mul_assoc]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [berezinianUpperShear, berezinianSchurDiagonal,
      berezinianLowerShear, fromBlocks_multiply, hleft, hright,
      hBD, hDC, hBDC, hAssoc]

section CommRing

variable {R_comm : Type*} [CommRing R_comm]

local notation "SubMatC" => Matrix ι ι R_comm

@[simp] theorem berezinianSchur_upperShear (X : SubMatC) :
    berezinianSchur (1 : SubMatC) X 0 1 1 (1 : R_comm) = 1 := by
  simp [berezinianSchur]

@[simp] theorem berezinianSchur_lowerShear (Y : SubMatC) :
    berezinianSchur (1 : SubMatC) 0 Y 1 1 (1 : R_comm) = 1 := by
  simp [berezinianSchur]

theorem berezinianSchur_middle_readout
    (A B C D invD : SubMatC) (invDetD : R_comm) :
    berezinianBlockDiag (A - B * invD * C) D invDetD =
      berezinianSchur A B C D invD invDetD := by
  rfl

theorem berezinianSchur_eq_det_schur_mul_invDet
    (A B C D invD : SubMatC) (invDetD : R_comm) :
    berezinianSchur A B C D invD invDetD =
      Matrix.det (A - B * invD * C) * invDetD := by
  rfl

theorem berezinianSchur_decoupled
    (A D invD : SubMatC) (invDetD : R_comm) :
    berezinianSchur A 0 0 D invD invDetD =
      Matrix.det A * invDetD := by
  simp [berezinianSchur]

theorem berezinianSchur_decoupled_mul_det
    (A D invD : SubMatC) (invDetD : R_comm)
    (hdet : invDetD * Matrix.det D = 1) :
    berezinianSchur A 0 0 D invD invDetD * Matrix.det D = Matrix.det A := by
  simp [berezinianSchur, mul_assoc, hdet]

end CommRing

end InfoGeometry.NCG
