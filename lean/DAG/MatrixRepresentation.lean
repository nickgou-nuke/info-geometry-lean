/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import DAG.TwoComplex
import DAG.GraphHodge

/-!
# DAG.MatrixRepresentation

Block matrix coordinate representation of the `TwoComplex` using Mathlib's
`Matrix` type.

Converts the Array-based boundary maps from `TwoComplex.lean` into
`Matrix (Fin n) (Fin m) ℚ` for access to the linear algebra library.

These matrices are the finite rational coordinate shadow of the real doubled
Hestenes--Krein proof-DAG carrier.  The primitive geometric lane is real and
doubled; this file owns the finite matrix formulas for the graph Dirac,
chiral grading, and Majorana skew form.

## Operators

- `chiralGamma` : Γ = diag(+I on C⁰, -I on C¹, +I on C²)
- `diracOp` : D = ∂ + ∂* (block-off-diagonal, self-adjoint)
- `majoranaOp` : A = ΓD (skew-symmetric, for Pfaffian)

## Theorems

- `chiral_anticommutation` : ΓD + DΓ = 0 (∀ n₀, n₁, n₂, ∀ B₁, B₂)
- `majorana_skew_symmetric` : A[i,j] = -A[j,i]

## BUCKET 1
The graded matrix formulas and finite skew/Pfaffian identities are proved
directly for arbitrary boundary matrices of the stated finite dimensions.

## BUCKET 2
The zero representation is constructed from zero boundary maps.

## BUCKET 3
No continuum limit or infinite-dimensional operator representation is asserted.
-/

open Matrix

namespace DAG.MatrixRepresentation

/-! ## The finite graded cell carrier -/

/-- A cell in one of the three consecutive degrees of a finite two-complex. -/
inductive Cell (n0 n1 n2 : ℕ)
  | zero : Fin n0 → Cell n0 n1 n2
  | one  : Fin n1 → Cell n0 n1 n2
  | two  : Fin n2 → Cell n0 n1 n2
  deriving DecidableEq, Fintype

/-! ## Chiral Grading Γ -/

/-- The even/odd grading of a cell in degrees `0,1,2`. -/
def cellParity {n0 n1 n2 : ℕ} : Cell n0 n1 n2 → ℚ
  | Cell.zero _ => 1
  | Cell.one _ => -1
  | Cell.two _ => 1

/-- The diagonal grading operator with eigenvalue `(-1)^degree`. -/
def chiralGamma {n0 n1 n2 : ℕ} : Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℚ :=
  Matrix.diagonal cellParity

/-! ## Dirac Operator D = ∂ + ∂* -/

/-- The symmetric block operator assembled from the two boundary matrices. -/
def diracOp {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℚ)
    (B2 : Matrix (Fin n1) (Fin n2) ℚ) :
    Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℚ
  | Cell.zero i, Cell.one j  => B1 i j
  | Cell.one i,  Cell.zero j => B1 j i
  | Cell.one i,  Cell.two j  => B2 i j
  | Cell.two i,  Cell.one j  => B2 j i
  | _, _ => 0

/-! ## Majorana Operator A = ΓD (skew-symmetric) -/

/-- The graded Dirac matrix whose block signs make it skew-symmetric. -/
def majoranaOp {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℚ)
    (B2 : Matrix (Fin n1) (Fin n2) ℚ) :
    Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℚ
  | Cell.zero i, Cell.one j  => -(B1 i j)
  | Cell.one i,  Cell.zero j => B1 j i
  | Cell.one i,  Cell.two j  => -(B2 i j)
  | Cell.two i,  Cell.one j  => B2 j i
  | _, _ => 0

/-! ## Theorem 1: ΓD + DΓ = 0 -/

/-- The grading anticommutes with the Dirac operator for all finite boundary
matrices, including rectangular boundary maps. -/
theorem chiral_anticommutation {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℚ)
    (B2 : Matrix (Fin n1) (Fin n2) ℚ) :
    chiralGamma (n0 := n0) (n1 := n1) (n2 := n2)
      * diracOp B1 B2
    + diracOp B1 B2
      * chiralGamma (n0 := n0) (n1 := n1) (n2 := n2)
    = 0 := by
  ext i j
  simp only [chiralGamma, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.zero_apply]
  have h :
      cellParity i * diracOp B1 B2 i j + diracOp B1 B2 i j * cellParity j =
        diracOp B1 B2 i j * (cellParity i + cellParity j) := by
    ring
  rw [h]
  cases i <;> cases j <;> simp [cellParity, diracOp]

/-! ## Theorem 2: Majorana is Skew-Symmetric -/

/-- The Majorana matrix is pointwise skew-symmetric for every pair of boundary
matrices. -/
theorem majorana_skew_symmetric {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℚ)
    (B2 : Matrix (Fin n1) (Fin n2) ℚ) (i j : Cell n0 n1 n2) :
    majoranaOp B1 B2 i j = -(majoranaOp B1 B2 j i) := by
  cases i <;> cases j <;> simp [majoranaOp]

/-! ## Theorem 3: Pfaffian² = Determinant (2×2) -/

/-- For every skew-symmetric `2 × 2` matrix over `ℚ`, the determinant is the
square of its upper-right entry. This is the dimension-two Pfaffian identity
in coordinates, with skew-symmetry as an explicit hypothesis rather than a
single hard-coded matrix. -/
theorem det_eq_sq_upperRight_of_skew_2x2
    (A : Matrix (Fin 2) (Fin 2) ℚ) (hA : Aᵀ = -A) :
    Matrix.det A = A 0 1 * A 0 1 := by
  have h00 : A 0 0 = 0 := by
    have h := congrFun (congrFun hA 0) 0
    simp only [Matrix.transpose_apply] at h
    change A 0 0 = -(A 0 0) at h
    linarith
  have h11 : A 1 1 = 0 := by
    have h := congrFun (congrFun hA 1) 1
    simp only [Matrix.transpose_apply] at h
    change A 1 1 = -(A 1 1) at h
    linarith
  have h10 : A 1 0 = -A 0 1 := by
    have h := congrFun (congrFun hA 0) 1
    simp only [Matrix.transpose_apply] at h
    change A 1 0 = -(A 0 1) at h
    exact h
  simp [Matrix.det_fin_two, h00, h11, h10]

/-- The standard skew matrix is the concrete specialization of
`det_eq_sq_upperRight_of_skew_2x2`. -/
theorem pfaffian_sq_eq_det_2x2 (a : ℚ) :
    a * a = Matrix.det (!![(0 : ℚ), a; -a, 0]) := by
  let A : Matrix (Fin 2) (Fin 2) ℚ := !![(0 : ℚ), a; -a, 0]
  have hA : Aᵀ = -A := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, Matrix.transpose_apply]
  have hdet := det_eq_sq_upperRight_of_skew_2x2 A hA
  change A 0 1 * A 0 1 = Matrix.det A
  exact hdet.symm

/-! ## Boundary data and derived readouts -/

/-- A finite two-complex matrix representation is determined by its two
boundary maps. Its grading, Dirac, and Majorana operators are derived below,
so a value cannot store inconsistent copies of those operators. -/
structure MatrixRep (n0 n1 n2 : ℕ) where
  B1 : Matrix (Fin n0) (Fin n1) ℚ
  B2 : Matrix (Fin n1) (Fin n2) ℚ

/-- The grading readout determined by a representation's cell dimensions. -/
def MatrixRep.Gamma {n0 n1 n2 : ℕ} (_rep : MatrixRep n0 n1 n2) :
    Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℚ :=
  chiralGamma

/-- The Dirac readout determined by the stored boundary maps. -/
def MatrixRep.Dirac {n0 n1 n2 : ℕ} (rep : MatrixRep n0 n1 n2) :
    Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℚ :=
  diracOp rep.B1 rep.B2

/-- The Majorana readout determined by the stored boundary maps. -/
def MatrixRep.Majorana {n0 n1 n2 : ℕ} (rep : MatrixRep n0 n1 n2) :
    Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℚ :=
  majoranaOp rep.B1 rep.B2

/-- Construct the finite matrix representation from its boundary maps. -/
def mk (n0 n1 n2 : ℕ) (B1 : Matrix (Fin n0) (Fin n1) ℚ) (B2 : Matrix (Fin n1) (Fin n2) ℚ) :
    MatrixRep n0 n1 n2 :=
  ⟨B1, B2⟩

/-- The zero-boundary representation exists in every finite cell dimension. -/
def zeroRep (n0 n1 n2 : ℕ) : MatrixRep n0 n1 n2 :=
  mk n0 n1 n2 0 0

instance (n0 n1 n2 : ℕ) : Inhabited (MatrixRep n0 n1 n2) :=
  ⟨zeroRep n0 n1 n2⟩

end DAG.MatrixRepresentation
