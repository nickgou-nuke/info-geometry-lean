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
-/

open Matrix

namespace DAG.MatrixRepresentation

/-! ## The finite graded cell carrier -/

inductive Cell (n0 n1 n2 : ℕ)
  | zero : Fin n0 → Cell n0 n1 n2
  | one  : Fin n1 → Cell n0 n1 n2
  | two  : Fin n2 → Cell n0 n1 n2
  deriving DecidableEq, Fintype

/-! ## Chiral Grading Γ -/

def cellParity {n0 n1 n2 : ℕ} : Cell n0 n1 n2 → ℚ
  | Cell.zero _ => 1
  | Cell.one _ => -1
  | Cell.two _ => 1

def chiralGamma {n0 n1 n2 : ℕ} : Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℚ :=
  Matrix.diagonal cellParity

/-! ## Dirac Operator D = ∂ + ∂* -/

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

theorem majorana_skew_symmetric {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℚ)
    (B2 : Matrix (Fin n1) (Fin n2) ℚ) (i j : Cell n0 n1 n2) :
    majoranaOp B1 B2 i j = -(majoranaOp B1 B2 j i) := by
  cases i <;> cases j <;> simp [majoranaOp]

/-! ## Theorem 3: Pfaffian² = Determinant (2×2) -/

theorem pfaffian_sq_eq_det_2x2 (a : ℚ) :
    a * a = Matrix.det (!![(0 : ℚ), a; -a, 0]) := by
  rw [Matrix.det_fin_two]
  norm_num

/-! ## MatrixRep structure -/

structure MatrixRep (n0 n1 n2 : ℕ) where
  B1 : Matrix (Fin n0) (Fin n1) ℚ
  B2 : Matrix (Fin n1) (Fin n2) ℚ
  Gamma : Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℚ
  Dirac : Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℚ
  Majorana : Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℚ

def mk (n0 n1 n2 : ℕ) (B1 : Matrix (Fin n0) (Fin n1) ℚ) (B2 : Matrix (Fin n1) (Fin n2) ℚ) :
    MatrixRep n0 n1 n2 :=
  { B1 := B1
    B2 := B2
    Gamma := chiralGamma (n0 := n0) (n1 := n1) (n2 := n2)
    Dirac := diracOp B1 B2
    Majorana := majoranaOp B1 B2
  }

end DAG.MatrixRepresentation
