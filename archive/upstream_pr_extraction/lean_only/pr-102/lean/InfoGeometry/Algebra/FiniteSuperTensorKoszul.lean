import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-!
# Finite super tensor Koszul signs

This file records only finite algebraic facts from the supergraded tensor-product
story.

It does not define a general Berezinian, a Clifford-algebra equivalence, Bott
periodicity, ABS map, Dirac index, or tenfold-way classification theorem.  The
proved content is the concrete `1|1` odd-operator Koszul sign calculation and
the resulting equality of the two `2 × 2` determinant blocks.
-/

namespace InfoGeometry.Algebra.FiniteSuperTensorKoszul

open Matrix
open scoped Kronecker

/--
The ordinary Kronecker determinant law: tensoring square matrices introduces the
opposite dimension as an exponent on each determinant factor.
-/
theorem det_kronecker_dimensional_exponents
    {R : Type*} [CommRing R]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m R) (B : Matrix n n R) :
    Matrix.det (A ⊗ₖ B) =
      Matrix.det A ^ Fintype.card n * Matrix.det B ^ Fintype.card m := by
  exact Matrix.det_kronecker A B

/--
The `4 × 4` matrix of the graded tensor product of two pure odd `1|1` maps,
with basis ordered as `(00,11,01,10)`.  The negative entries are exactly the
Koszul signs from moving an odd operator past an odd basis vector.
-/
noncomputable def oddOddKoszulTensorMatrix
    {R : Type*} [Zero R] [Mul R] [Neg R] (a b c d : R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![(0 : R), -a * c, 0, 0;
     b * d, 0, 0, 0;
     0, 0, 0, -a * d;
     0, 0, b * c, 0]

/--
The concrete parity operator for the ordered tensor basis `(00,11,01,10)`:
the first two basis vectors have even total parity and the last two have odd
total parity.
-/
noncomputable def tensorParityMatrix
    {R : Type*} [Zero R] [One R] [Neg R] : Matrix (Fin 4) (Fin 4) R :=
  !![(1 : R), 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/--
The odd-odd Koszul tensor is even: conjugation by the total-parity operator
fixes the concrete `1|1 ⊗ 1|1` matrix.
-/
theorem tensorParity_conj_oddOddKoszulTensorMatrix
    {R : Type*} [CommRing R] (a b c d : R) :
    tensorParityMatrix * oddOddKoszulTensorMatrix a b c d * tensorParityMatrix =
      oddOddKoszulTensorMatrix a b c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorParityMatrix, oddOddKoszulTensorMatrix, Matrix.mul_apply, Fin.sum_univ_four]

/-- The even-parity block of the odd-odd Koszul tensor matrix has determinant `abcd`. -/
theorem oddOddKoszul_evenBlock_det
    {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![(0 : R), -a * c; b * d, 0] = a * b * c * d := by
  simp [Matrix.det_fin_two]
  ring

/-- The odd-parity block of the odd-odd Koszul tensor matrix has the same determinant. -/
theorem oddOddKoszul_oddBlock_det
    {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![(0 : R), -a * d; b * c, 0] = a * b * c * d := by
  simp [Matrix.det_fin_two]
  ring

/--
For nonzero block determinant, the finite block determinant ratio of the
odd-odd Koszul tensor matrix is `1`.

This is only the explicit block-diagonal `1|1 ⊗ 1|1` calculation; it is not a
general Berezinian theorem.
-/
theorem oddOddKoszul_blockDet_ratio_eq_one
    {R : Type*} [Field R] {a b c d : R}
    (h : a * b * c * d ≠ 0) :
    Matrix.det !![(0 : R), -a * c; b * d, 0] /
      Matrix.det !![(0 : R), -a * d; b * c, 0] = 1 := by
  rw [oddOddKoszul_evenBlock_det, oddOddKoszul_oddBlock_det]
  exact div_self h

end InfoGeometry.Algebra.FiniteSuperTensorKoszul
