import InfoGeometry.NCG.BerezinianSuperdeterminant

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Matrix

namespace InfoGeometry.NCG

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "BlockMat" => Matrix (ι ⊕ ι) (ι ⊕ ι) R
local notation "SubMat" => Matrix ι ι R

/-!
This file closes the algebraic block-Gaussian step behind the Schur-complement
Berezinian already defined in `BerezinianSuperdeterminant.lean`.

The coefficient ring here is an ordinary commutative ring.  Consequently these
theorems formalize the block factorization and its determinant-ratio readout;
they do not identify the off-diagonal blocks with genuinely odd elements of a
supercommutative algebra.  That parity-sensitive layer requires a separate
graded-algebra owner.
-/

/-- Upper unipotent block shear used in the D-Schur factorization. -/
def berezinianUpperShear (B invD : SubMat) : BlockMat :=
  fromBlocks (1 : SubMat) (B * invD) 0 1

/-- Lower unipotent block shear used in the D-Schur factorization. -/
def berezinianLowerShear (C invD : SubMat) : BlockMat :=
  fromBlocks (1 : SubMat) 0 (invD * C) 1

/-- Block diagonal carrying the D-Schur complement. -/
def berezinianSchurDiagonal (A B C D invD : SubMat) : BlockMat :=
  fromBlocks (A - B * invD * C) 0 0 D

/-- A supplied matrix is a two-sided inverse of `D`. -/
structure TwoSidedMatrixInverse (D invD : SubMat) : Prop where
  left_inv : invD * D = 1
  right_inv : D * invD = 1

/--
Exact block Gaussian elimination:

`[[A,B],[C,D]] = U · diag(A - B D⁻¹ C, D) · L`

provided the supplied `invD` is a genuine two-sided inverse of `D`.
-/
theorem berezinian_block_gaussian_factorization
    (A B C D invD : SubMat)
    (hD : TwoSidedMatrixInverse D invD) :
    fromBlocks A B C D =
      berezinianUpperShear B invD *
        berezinianSchurDiagonal A B C D invD *
          berezinianLowerShear C invD := by
  rcases hD with ⟨hleft, hright⟩
  simp [berezinianUpperShear, berezinianSchurDiagonal,
    berezinianLowerShear, fromBlocks_multiply, hleft, hright, mul_assoc]

/-- The upper unipotent shear has Schur-Berezinian one. -/
@[simp]
theorem berezinianSchur_upperShear (X : SubMat) :
    berezinianSchur (1 : SubMat) X 0 1 1 (1 : R) = 1 := by
  simp [berezinianSchur]

/-- The lower unipotent shear has Schur-Berezinian one. -/
@[simp]
theorem berezinianSchur_lowerShear (Y : SubMat) :
    berezinianSchur (1 : SubMat) 0 Y 1 1 (1 : R) = 1 := by
  simp [berezinianSchur]

/-- The middle factor has exactly the Schur-complement Berezinian readout. -/
theorem berezinianSchur_middle_readout
    (A B C D invD : SubMat) (invDetD : R) :
    berezinianBlockDiag (A - B * invD * C) D invDetD =
      berezinianSchur A B C D invD invDetD := by
  rfl

/--
The existing Schur Berezinian is the bosonic Schur determinant multiplied by
the supplied inverse fermionic determinant.
-/
theorem berezinianSchur_eq_det_schur_mul_invDet
    (A B C D invD : SubMat) (invDetD : R) :
    berezinianSchur A B C D invD invDetD =
      Matrix.det (A - B * invD * C) * invDetD := by
  rfl

/-- Decoupled bosonic/fermionic blocks recover the determinant ratio owner. -/
theorem berezinianSchur_decoupled
    (A D invD : SubMat) (invDetD : R) :
    berezinianSchur A 0 0 D invD invDetD =
      Matrix.det A * invDetD := by
  simp [berezinianSchur]

/--
If `invDetD` is certified as the inverse of `det D`, the decoupled readout is
exactly characterized by multiplication back by `det D`.
-/
theorem berezinianSchur_decoupled_mul_det
    (A D invD : SubMat) (invDetD : R)
    (hdet : invDetD * Matrix.det D = 1) :
    berezinianSchur A 0 0 D invD invDetD * Matrix.det D = Matrix.det A := by
  simp [berezinianSchur, mul_assoc, hdet]

end InfoGeometry.NCG
