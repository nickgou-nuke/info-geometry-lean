import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import InfoGeometry.Section16

/-!
# Section 17: Biquaternion coordinates and `M₂(C)`

This file repairs the Section 17 prose into a finite theorem-safe model.

#### BUCKET 1: CLOSED FINITE THEOREMS
The displayed biquaternion matrix map
`(c0,c1,c2,c3) ↦ [[c0+i c1, c2+i c3], [-c2+i c3, c0-i c1]]`
has an explicit inverse.  The basis matrices for `i`, `j`, and `k` square to
`-I₂` and satisfy the Hamilton product table.  The map is also identified with
the Section 16 even-Clifford coordinate map by a permutation of the three
imaginary coordinates.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.  These are direct finite matrix calculations.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not construct tensor products over `R`, the full real
8-dimensional biquaternion algebra, the full complex Clifford algebra,
`Cl(3,0;C) ≃ M₂(C) ⊕ M₂(C)`, Spin/SL/Lorentz identifications, Pauli spin
physics, or Maxwell's equations.  Those remain outside this finite coordinate
module.
-/

noncomputable section

namespace Section17

open Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

abbrev BiquatCoord := InfoGeometry.Algebra.FiniteSpin.Vec4C
abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

def biquatToMatrix (q : BiquatCoord) : Mat2C :=
  !![q 0 + Complex.I * q 1, q 2 + Complex.I * q 3;
     -q 2 + Complex.I * q 3, q 0 - Complex.I * q 1]

def matrixToBiquat (M : Mat2C) : BiquatCoord
  | 0 => (M 0 0 + M 1 1) / 2
  | 1 => -Complex.I * (M 0 0 - M 1 1) / 2
  | 2 => (M 0 1 - M 1 0) / 2
  | 3 => -Complex.I * (M 0 1 + M 1 0) / 2

@[simp] lemma complex_I_sq : Complex.I ^ 2 = (-1 : ℂ) := by
  simp [pow_two, Complex.I_mul_I]

theorem biquatToMatrix_matrixToBiquat (M : Mat2C) :
    biquatToMatrix (matrixToBiquat M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [biquatToMatrix, matrixToBiquat] <;> ring_nf <;> try simp [complex_I_sq] <;> try ring

theorem matrixToBiquat_biquatToMatrix (q : BiquatCoord) :
    matrixToBiquat (biquatToMatrix q) = q := by
  funext i
  fin_cases i <;>
    simp [biquatToMatrix, matrixToBiquat] <;> ring_nf <;> try simp [complex_I_sq] <;> try ring

def I₂ : Mat2C :=
  1

def Qi : Mat2C :=
  !![Complex.I, 0; 0, -Complex.I]

def Qj : Mat2C :=
  !![(0 : ℂ), 1; -1, 0]

def Qk : Mat2C :=
  !![(0 : ℂ), Complex.I; Complex.I, 0]

theorem basis_square_Qi : Qi * Qi = -I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Qi, I₂, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem basis_square_Qj : Qj * Qj = -I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Qj, I₂, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem basis_square_Qk : Qk * Qk = -I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Qk, I₂, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem basis_product_Qi_Qj : Qi * Qj = Qk := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Qi, Qj, Qk, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem basis_product_Qj_Qk : Qj * Qk = Qi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Qi, Qj, Qk, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem basis_product_Qk_Qi : Qk * Qi = Qj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Qi, Qj, Qk, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem basis_product_Qj_Qi : Qj * Qi = -Qk := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Qi, Qj, Qk, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem basis_product_Qk_Qj : Qk * Qj = -Qi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Qi, Qj, Qk, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem basis_product_Qi_Qk : Qi * Qk = -Qj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Qi, Qj, Qk, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Section 17's biquaternion matrix map is Section 16's map with permuted imaginary slots. -/
theorem biquatToMatrix_eq_section16_evenToMatrix (q : BiquatCoord) :
    biquatToMatrix q =
      Section16.evenToMatrix (fun
        | 0 => q 0
        | 1 => q 3
        | 2 => -q 1
        | 3 => -q 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [biquatToMatrix, Section16.evenToMatrix] <;> ring

theorem section17_capstone :
    (∀ M : Mat2C, biquatToMatrix (matrixToBiquat M) = M) ∧
    (∀ q : BiquatCoord, matrixToBiquat (biquatToMatrix q) = q) ∧
    Qi * Qi = -I₂ ∧ Qj * Qj = -I₂ ∧ Qk * Qk = -I₂ ∧
    Qi * Qj = Qk ∧ Qj * Qk = Qi ∧ Qk * Qi = Qj ∧
    Qj * Qi = -Qk ∧ Qk * Qj = -Qi ∧ Qi * Qk = -Qj ∧
    (∀ q : BiquatCoord,
      biquatToMatrix q =
        Section16.evenToMatrix (fun
          | 0 => q 0
          | 1 => q 3
          | 2 => -q 1
          | 3 => -q 2)) := by
  exact ⟨biquatToMatrix_matrixToBiquat, matrixToBiquat_biquatToMatrix,
    basis_square_Qi, basis_square_Qj, basis_square_Qk,
    basis_product_Qi_Qj, basis_product_Qj_Qk, basis_product_Qk_Qi,
    basis_product_Qj_Qi, basis_product_Qk_Qj, basis_product_Qi_Qk,
    biquatToMatrix_eq_section16_evenToMatrix⟩

end Section17
