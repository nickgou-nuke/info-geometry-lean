import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Quantum.PauliSoldering
import InfoGeometry.Optics.OperatorCausalSoldering
import InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge

/-!
# InfoGeometry.Canonical.OperatorWeylChiralCurvatureBlocks

Canonical finite Weyl-block owner for the Pauli/Clifford operator corridor.

This file does not identify the repository's independent tripotent/TKK
five-grading with exterior Clifford degree.  It isolates the ordinary
Z₂ Clifford parity visible in a Weyl basis:

* odd operators are block-off-diagonal;
* products of odd operators are block-diagonal;
* the two diagonal blocks are the ordered products `σ(A) \barσ(B)` and
  `\barσ(A) σ(B)`.

For operator-valued coefficients the order is retained exactly.  No
noncommutative determinant and no self-duality label is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorWeylChiralCurvatureBlocks

open Matrix
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Optics.OperatorCausalSoldering

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev Mat4C := Matrix (Fin 4) (Fin 4) ℂ
abbrev ComplexFourVector := Fin 4 → ℂ

/-- Sign-reversed Pauli co-soldering `A₀ I - Aᵢ σᵢ`. -/
def coSolder (A : ComplexFourVector) : Mat2C :=
  solder (A 0, -A 1, -A 2, -A 3)

/-- Pauli soldering of a four-vector. -/
def sigmaSolder (A : ComplexFourVector) : Mat2C :=
  solder (A 0, A 1, A 2, A 3)

/-- A `2×2` pair inserted as a block-off-diagonal `4×4` matrix. -/
def offDiagonalBlock (X Y : Mat2C) : Mat4C := fun i j =>
  if hi : i.val < 2 then
    if hj : j.val < 2 then 0 else X ⟨i.val, hi⟩ ⟨j.val - 2, by omega⟩
  else
    if hj : j.val < 2 then Y ⟨i.val - 2, by omega⟩ ⟨j.val, hj⟩ else 0

/-- A `2×2` pair inserted as a block-diagonal `4×4` matrix. -/
def diagonalBlock (X Y : Mat2C) : Mat4C := fun i j =>
  if hi : i.val < 2 then
    if hj : j.val < 2 then X ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else
    if hj : j.val < 2 then 0 else Y ⟨i.val - 2, by omega⟩ ⟨j.val - 2, by omega⟩

/-- Weyl realization of a vector Clifford element. -/
def weylSlash (A : ComplexFourVector) : Mat4C :=
  offDiagonalBlock (sigmaSolder A) (coSolder A)

/-- Weyl chirality grading `diag(I₂,-I₂)`. -/
def weylGamma5 : Mat4C :=
  !![(1 : ℂ), 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- A Weyl vector operator is block-off-diagonal, hence odd for chirality. -/
theorem weylGamma5_anticomm_weylSlash (A : ComplexFourVector) :
    weylGamma5 * weylSlash A + weylSlash A * weylGamma5 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylGamma5, weylSlash, offDiagonalBlock, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- Exact block square of an off-diagonal matrix. -/
theorem offDiagonalBlock_sq (X Y : Mat2C) :
    offDiagonalBlock X Y * offDiagonalBlock X Y =
      diagonalBlock (X * Y) (Y * X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagonalBlock, diagonalBlock, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.sum_univ_two]

/-- The Weyl slash square is block diagonal with the two ordered Pauli
factorizations. -/
theorem weylSlash_sq_blocks (A : ComplexFourVector) :
    weylSlash A * weylSlash A =
      diagonalBlock (sigmaSolder A * coSolder A)
        (coSolder A * sigmaSolder A) := by
  exact offDiagonalBlock_sq _ _

/-- For scalar complex coordinates, both chiral blocks collapse to the same
Minkowski quadratic invariant. -/
theorem sigma_mul_coSolder_eq_scalar (A : ComplexFourVector) :
    sigmaSolder A * coSolder A =
      (InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge.minkowskiQuadratic A) •
        (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaSolder, coSolder, solder_explicit,
      InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge.minkowskiQuadratic,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
    ring

/-- The reversed scalar block gives the same invariant. -/
theorem coSolder_mul_sigma_eq_scalar (A : ComplexFourVector) :
    coSolder A * sigmaSolder A =
      (InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge.minkowskiQuadratic A) •
        (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaSolder, coSolder, solder_explicit,
      InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge.minkowskiQuadratic,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
    ring

/-- Scalar-coordinate Weyl square root of the Minkowski quadratic form. -/
theorem weylSlash_sq_scalar (A : ComplexFourVector) :
    weylSlash A * weylSlash A =
      (InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge.minkowskiQuadratic A) •
        (1 : Mat4C) := by
  rw [weylSlash_sq_blocks, sigma_mul_coSolder_eq_scalar,
    coSolder_mul_sigma_eq_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalBlock]

/-! ## Genuine operator-valued chiral blocks -/

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

abbrev EndW := Module.End ℂ W
abbrev OperatorMat2 := Matrix (Fin 2) (Fin 2) EndW

/-- Operator-valued co-soldering with the same Weyl sign convention. -/
def operatorCoSoldering (v : OperatorFourVector W) : OperatorMat2 :=
  !![v 0 - v 3, -(v 1) + Complex.I • v 2;
     -(v 1) - Complex.I • v 2, v 0 + v 3]

/-- Left chiral even block generated by an operator-valued odd potential. -/
def leftCurvatureBlock (v : OperatorFourVector W) : OperatorMat2 :=
  operatorSoldering v * operatorCoSoldering v

/-- Right chiral even block, retaining the reversed operator ordering. -/
def rightCurvatureBlock (v : OperatorFourVector W) : OperatorMat2 :=
  operatorCoSoldering v * operatorSoldering v

/-- The two operator-valued chiral blocks are exactly the ordered products
appearing in the square of a Weyl off-diagonal operator. -/
theorem operator_chiral_square_packet (v : OperatorFourVector W) :
    leftCurvatureBlock v = operatorSoldering v * operatorCoSoldering v ∧
      rightCurvatureBlock v = operatorCoSoldering v * operatorSoldering v := by
  exact ⟨rfl, rfl⟩

/-- In the commuting limit, the left block has no off-diagonal residue. -/
theorem leftCurvatureBlock_offdiag_zero_of_commute
    (v : OperatorFourVector W)
    (h01 : Commute (v 0) (v 1))
    (h02 : Commute (v 0) (v 2))
    (h13 : Commute (v 1) (v 3))
    (h23 : Commute (v 2) (v 3)) :
    leftCurvatureBlock v 0 1 = 0 ∧ leftCurvatureBlock v 1 0 = 0 := by
  constructor
  · simp [leftCurvatureBlock, operatorSoldering_apply, operatorCoSoldering,
      Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def]
    noncomm_ring [h01.eq, h02.eq, h13.eq, h23.eq]
  · simp [leftCurvatureBlock, operatorSoldering_apply, operatorCoSoldering,
      Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def]
    noncomm_ring [h01.eq, h02.eq, h13.eq, h23.eq]

end InfoGeometry.Canonical.OperatorWeylChiralCurvatureBlocks
