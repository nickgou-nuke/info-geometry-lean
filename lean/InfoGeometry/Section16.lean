import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Section 16: Complex even Clifford coordinates and biquaternion matrices

This file repairs the Section 16 prose into a finite theorem-safe model.

#### BUCKET 1: CLOSED FINITE THEOREMS
The displayed coordinate map
`(z0,z1,z2,z3) ↦ [[z0 - i z2, i z1 - z3], [i z1 + z3, z0 + i z2]]`
has an explicit inverse from `M₂(C)` back to four complex coordinates, hence is
bijective as a finite coordinate map.  The three nontrivial displayed basis
images square to `-I₂` and satisfy their actual cyclic matrix products.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.  The closed results are direct finite matrix calculations.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not construct the full complex Clifford algebra, prove
`Cl(3,0;C) ≃ M₂(C) ⊕ M₂(C)`, identify Spin groups with `SL(2,C)`, prove the
Lorentz double cover, formalize Pauli spin physics, or derive Maxwell's
equations.  Those require algebra, representation theory, Lie groups, and
analysis not present in this finite coordinate section.
-/

noncomputable section

namespace Section16

open Matrix

abbrev EvenCoord := Fin 4 → ℂ
abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

def evenToMatrix (x : EvenCoord) : Mat2C :=
  !![x 0 - Complex.I * x 2, Complex.I * x 1 - x 3;
     Complex.I * x 1 + x 3, x 0 + Complex.I * x 2]

def matrixToEven (M : Mat2C) : EvenCoord
  | 0 => (M 0 0 + M 1 1) / 2
  | 1 => -Complex.I * (M 0 1 + M 1 0) / 2
  | 2 => Complex.I * (M 0 0 - M 1 1) / 2
  | 3 => (M 1 0 - M 0 1) / 2

@[simp] lemma complex_I_sq : Complex.I ^ 2 = (-1 : ℂ) := by
  simp [pow_two, Complex.I_mul_I]

theorem evenToMatrix_matrixToEven (M : Mat2C) :
    evenToMatrix (matrixToEven M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evenToMatrix, matrixToEven] <;> ring_nf <;> rw [complex_I_sq] <;> ring_nf

theorem matrixToEven_evenToMatrix (x : EvenCoord) :
    matrixToEven (evenToMatrix x) = x := by
  funext i
  fin_cases i <;>
    simp [evenToMatrix, matrixToEven] <;> ring_nf <;> rw [complex_I_sq] <;> ring_nf

def I₂ : Mat2C :=
  1

def E12 : Mat2C :=
  !![(0 : ℂ), Complex.I; Complex.I, 0]

def E23 : Mat2C :=
  !![-Complex.I, 0; 0, Complex.I]

def E31 : Mat2C :=
  !![(0 : ℂ), -1; 1, 0]

theorem basis_square_E12 : E12 * E12 = -I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E12, I₂, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem basis_square_E23 : E23 * E23 = -I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E23, I₂, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem basis_square_E31 : E31 * E31 = -I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E31, I₂, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem basis_product_E12_E23 : E12 * E23 = E31 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E12, E23, E31, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem basis_product_E23_E31 : E23 * E31 = E12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E12, E23, E31, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem basis_product_E31_E12 : E31 * E12 = E23 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E12, E23, E31, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem section16_capstone :
    (∀ M : Mat2C, evenToMatrix (matrixToEven M) = M) ∧
    (∀ x : EvenCoord, matrixToEven (evenToMatrix x) = x) ∧
    E12 * E12 = -I₂ ∧ E23 * E23 = -I₂ ∧ E31 * E31 = -I₂ ∧
    E12 * E23 = E31 ∧ E23 * E31 = E12 ∧ E31 * E12 = E23 := by
  exact ⟨evenToMatrix_matrixToEven, matrixToEven_evenToMatrix,
    basis_square_E12, basis_square_E23, basis_square_E31,
    basis_product_E12_E23, basis_product_E23_E31, basis_product_E31_E12⟩

end Section16
