import Mathlib.Tactic
import InfoGeometry.Canonical.OperatorWeylChiralCurvatureBlocks

/-!
# InfoGeometry.Canonical.WeylChiralHodgeCurvatureSplit

Lorentzian Hodge eigenspaces in the finite Weyl block representation.

For the Weyl chirality matrix `Γ5 = diag(I₂,-I₂)`, define the finite
bivector Hodge operator by left multiplication with `-i Γ5`.  On block
diagonal even matrices this has the two expected Lorentzian eigenvalues
`-i` and `+i`:

* the upper-left block is the `-i` eigensector;
* the lower-right block is the `+i` eigensector.

This proves the chiral Hodge split itself.  It deliberately does not identify
either sector with the separate Dirac-Pauli quaternionic basis until an
explicit basis-change intertwiner is supplied.
-/

noncomputable section

namespace InfoGeometry.Canonical.WeylChiralHodgeCurvatureSplit

open Matrix
open InfoGeometry.Canonical.OperatorWeylChiralCurvatureBlocks

/-- Lorentzian Hodge star on the finite Weyl matrix carrier. -/
def weylHodgeStar (F : Mat4C) : Mat4C :=
  (-Complex.I) • (weylGamma5 * F)

/-- The Weyl Hodge star squares to minus the identity on all matrices under
this left-action realization. -/
theorem weylHodgeStar_sq (F : Mat4C) :
    weylHodgeStar (weylHodgeStar F) = -F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylHodgeStar, weylGamma5, Matrix.mul_apply,
      Fin.sum_univ_succ, Complex.I_sq]

/-- Embed only the upper chiral `2×2` block. -/
def leftChiralBlock (X : Mat2C) : Mat4C :=
  diagonalBlock X 0

/-- Embed only the lower chiral `2×2` block. -/
def rightChiralBlock (Y : Mat2C) : Mat4C :=
  diagonalBlock 0 Y

/-- The upper Weyl block is the `-i` Lorentzian Hodge eigensector. -/
theorem leftChiralBlock_hodge_eigen (X : Mat2C) :
    weylHodgeStar (leftChiralBlock X) =
      (-Complex.I) • leftChiralBlock X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylHodgeStar, leftChiralBlock, diagonalBlock, weylGamma5,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The lower Weyl block is the `+i` Lorentzian Hodge eigensector. -/
theorem rightChiralBlock_hodge_eigen (Y : Mat2C) :
    weylHodgeStar (rightChiralBlock Y) =
      Complex.I • rightChiralBlock Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylHodgeStar, rightChiralBlock, diagonalBlock, weylGamma5,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- Every block-diagonal even Weyl matrix is the sum of its two chiral Hodge
components. -/
theorem diagonalBlock_eq_left_add_right (X Y : Mat2C) :
    diagonalBlock X Y = leftChiralBlock X + rightChiralBlock Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftChiralBlock, rightChiralBlock, diagonalBlock]

/-- The square of a Weyl slash decomposes into the two Lorentzian Hodge
chiral sectors. -/
theorem weylSlash_sq_hodge_split (A : ComplexFourVector) :
    weylSlash A * weylSlash A =
      leftChiralBlock (sigmaSolder A * coSolder A) +
        rightChiralBlock (coSolder A * sigmaSolder A) := by
  rw [weylSlash_sq_blocks, diagonalBlock_eq_left_add_right]

/-- The two ordered chiral products in the Weyl square carry opposite Hodge
eigenvalues. -/
theorem weylSlash_square_hodge_packet (A : ComplexFourVector) :
    weylHodgeStar
        (leftChiralBlock (sigmaSolder A * coSolder A)) =
      (-Complex.I) •
        leftChiralBlock (sigmaSolder A * coSolder A) ∧
    weylHodgeStar
        (rightChiralBlock (coSolder A * sigmaSolder A)) =
      Complex.I •
        rightChiralBlock (coSolder A * sigmaSolder A) := by
  exact ⟨leftChiralBlock_hodge_eigen _, rightChiralBlock_hodge_eigen _⟩

end InfoGeometry.Canonical.WeylChiralHodgeCurvatureSplit
