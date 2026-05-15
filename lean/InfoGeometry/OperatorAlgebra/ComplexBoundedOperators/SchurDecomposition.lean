import Mathlib
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.RingHomMatrix

/-!
# InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.SchurDecomposition

Lean-native owner surface for the AFP
`Jordan_Normal_Form.Schur_Decomposition` corridor.

The AFP file gives an executable Schur decomposition algorithm:
from a square matrix and a list of eigenvalues it computes matrices `B`, `P`,
and `Q` such that `A = P * B * Q`, `P * Q = 1`, `B` is upper triangular, and
the diagonal of `B` is the supplied eigenvalue list.

In this repository the low-level finite complex inverse row construction is
already formalized in `ExtraJordanNormalForm`.  This file packages the Schur
decomposition result in a finite-type Lean API, exposes the upper-triangular
readout, and records the block characteristic-polynomial consequences used by
the Jordan-normal-form existence corridor.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.SchurDecomposition

open scoped BigOperators
open Polynomial

/-! ## AFP finite complex inverse-row layer -/

/-- AFP `vec_inv`, reused from the existing finite complex JNF core. -/
abbrev vecInv {ι : Type*} [Fintype ι] (v : ι → ℂ) : ι → ℂ :=
  InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.vecInv v

/-- Hermitian/conjugate dot product, conjugate-linear in the first argument. -/
abbrev cDot {ι : Type*} [Fintype ι] (v w : ι → ℂ) : ℂ :=
  InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.cDot v w

/-- Matrix adjoint over finite complex matrices. -/
abbrev matAdjoint {ι : Type*} (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.matAdjoint A

/-- Columns are conjugate-orthogonal and nonzero in Hermitian norm. -/
abbrev CorthogonalMatrix {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : Prop :=
  InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.corthogonalMatrix A

/-- Explicit inverse from conjugate-orthogonal columns. -/
abbrev corthogonalInverse {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.corthogonalInverse A

/-- The AFP inverse row evaluates to `1` on its source vector. -/
theorem vecInv_dot_self {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (h : cDot v v ≠ 0) :
    InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.dot (vecInv v) v = 1 :=
  InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.dot_vecInv_self v h

/-- The explicit conjugate-orthogonal inverse is a left inverse. -/
theorem corthogonalInverse_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ}
    (hA : CorthogonalMatrix A) :
    corthogonalInverse A * A = 1 :=
  InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.corthogonalInverse_mul hA

/-- Off-diagonal columns of a `CorthogonalMatrix` have zero Hermitian overlap. -/
theorem corthogonalMatrix_offdiag
    {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : CorthogonalMatrix A)
    {i j : ι} (hij : i ≠ j) :
    cDot (fun k => A k i) (fun k => A k j) = 0 :=
  hA.1 i j hij

/-- Diagonal column norms of a `CorthogonalMatrix` are nonzero. -/
theorem corthogonalMatrix_diag_ne_zero
    {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : CorthogonalMatrix A)
    (i : ι) :
    cDot (fun k => A k i) (fun k => A k i) ≠ 0 :=
  hA.2 i

/-! ## Upper-triangular and diagonal readouts -/

/-- Entrywise upper-triangular predicate for ordered finite index types. -/
def UpperTriangular {R ι : Type*} [Zero R] [LT ι] (A : Matrix ι ι R) : Prop :=
  ∀ ⦃i j : ι⦄, j < i → A i j = 0

/-- Diagonal readout of a finite matrix as a `Fin`-ordered list. -/
def diagList {R : Type*} {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : List R :=
  List.ofFn fun i : Fin n => A i i

@[simp]
theorem diagList_length {R : Type*} {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    (diagList A).length = n := by
  simp [diagList]

/-- Diagonal entries of an upper-triangular matrix determine its characteristic polynomial. -/
theorem charpoly_of_upperTriangular_fin
    {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R)
    (hA : UpperTriangular A) :
    A.charpoly = ∏ i : Fin n, (X - C (A i i)) := by
  classical
  exact Matrix.charpoly_of_upperTriangular A (by
    intro i j hij
    exact hA hij)

/-! ## Certified Schur decomposition packet -/

/--
Witness that `A` and `B` are similar via explicit inverse matrices `P` and `Q`.

The AFP statement records `A = P * B * Q` and `P * Q = 1`; the Lean packet also
stores `Q * P = 1`, making the inverse relation available without recovering it
from finite-dimensional algebra.
-/
structure SimilarMatrixWitness {R ι : Type*}
    [Semiring R] [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι R) where
  /-- Change-of-basis matrix. -/
  P : Matrix ι ι R
  /-- Inverse change-of-basis matrix. -/
  Q : Matrix ι ι R
  /-- `P` is a left inverse of `Q`. -/
  P_mul_Q : P * Q = 1
  /-- `Q` is a left inverse of `P`. -/
  Q_mul_P : Q * P = 1
  /-- Similarity factorization. -/
  factorization : A = P * B * Q

namespace SimilarMatrixWitness

variable {R ι : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]
variable {A B C : Matrix ι ι R}

/-- A matrix is similar to itself. -/
def refl (A : Matrix ι ι R) : SimilarMatrixWitness A A where
  P := 1
  Q := 1
  P_mul_Q := by simp
  Q_mul_P := by simp
  factorization := by simp

/-- Symmetry of explicit similarity witnesses. -/
def symm (W : SimilarMatrixWitness A B) : SimilarMatrixWitness B A where
  P := W.Q
  Q := W.P
  P_mul_Q := W.Q_mul_P
  Q_mul_P := W.P_mul_Q
  factorization := by
    calc
      B = 1 * B * 1 := by simp
      _ = W.Q * W.P * B * (W.Q * W.P) := by rw [W.Q_mul_P]
      _ = W.Q * (W.P * B * W.Q) * W.P := by noncomm_ring
      _ = W.Q * A * W.P := by rw [← W.factorization]

/-- Transitivity of explicit similarity witnesses. -/
def trans (W₁ : SimilarMatrixWitness A B) (W₂ : SimilarMatrixWitness B C) :
    SimilarMatrixWitness A C where
  P := W₁.P * W₂.P
  Q := W₂.Q * W₁.Q
  P_mul_Q := by
    calc
      (W₁.P * W₂.P) * (W₂.Q * W₁.Q)
          = W₁.P * (W₂.P * W₂.Q) * W₁.Q := by noncomm_ring
      _ = W₁.P * 1 * W₁.Q := by rw [W₂.P_mul_Q]
      _ = 1 := by simp [W₁.P_mul_Q]
  Q_mul_P := by
    calc
      (W₂.Q * W₁.Q) * (W₁.P * W₂.P)
          = W₂.Q * (W₁.Q * W₁.P) * W₂.P := by noncomm_ring
      _ = W₂.Q * 1 * W₂.P := by rw [W₁.Q_mul_P]
      _ = 1 := by simp [W₂.Q_mul_P]
  factorization := by
    calc
      A = W₁.P * B * W₁.Q := W₁.factorization
      _ = W₁.P * (W₂.P * C * W₂.Q) * W₁.Q := by rw [← W₂.factorization]
      _ = (W₁.P * W₂.P) * C * (W₂.Q * W₁.Q) := by noncomm_ring

end SimilarMatrixWitness

/--
Certified output of the AFP Schur decomposition algorithm on `Fin n`.

`eigenvalues` is a list rather than a function to mirror the AFP statement
`diag_mat B = es`.
-/
structure SchurDecompositionPacket (K : Type*) [Field K] (n : ℕ) where
  /-- Input matrix. -/
  A : Matrix (Fin n) (Fin n) K
  /-- Eigenvalue list supplied to the algorithm. -/
  eigenvalues : List K
  /-- Upper-triangular Schur form. -/
  B : Matrix (Fin n) (Fin n) K
  /-- Change-of-basis matrix. -/
  P : Matrix (Fin n) (Fin n) K
  /-- Inverse change-of-basis matrix. -/
  Q : Matrix (Fin n) (Fin n) K
  /-- Similarity factorization `A = P * B * Q`. -/
  factorization : A = P * B * Q
  /-- Left inverse relation. -/
  P_mul_Q : P * Q = 1
  /-- Right inverse relation. -/
  Q_mul_P : Q * P = 1
  /-- Schur output is upper triangular. -/
  upper_triangular : UpperTriangular B
  /-- Diagonal readout equals the supplied eigenvalue list. -/
  diag_eq : diagList B = eigenvalues

namespace SchurDecompositionPacket

variable {K : Type*} [Field K] {n : ℕ}

/-- Similarity witness carried by a Schur packet. -/
def similarWitness (S : SchurDecompositionPacket K n) :
    SimilarMatrixWitness S.A S.B where
  P := S.P
  Q := S.Q
  P_mul_Q := S.P_mul_Q
  Q_mul_P := S.Q_mul_P
  factorization := S.factorization

/-- AFP theorem surface: Schur output is similar, upper triangular, and has the requested diagonal. -/
theorem schur_decomposition (S : SchurDecompositionPacket K n) :
    Nonempty (SimilarMatrixWitness S.A S.B) ∧ UpperTriangular S.B ∧
      diagList S.B = S.eigenvalues :=
  ⟨⟨S.similarWitness⟩, S.upper_triangular, S.diag_eq⟩

/-- The upper-triangular component of a certified Schur decomposition. -/
def schurUpperTriangular (S : SchurDecompositionPacket K n) :
    Matrix (Fin n) (Fin n) K :=
  S.B

theorem schurUpperTriangular_upper (S : SchurDecompositionPacket K n) :
    UpperTriangular S.schurUpperTriangular :=
  S.upper_triangular

def schurUpperTriangular_similar (S : SchurDecompositionPacket K n) :
    SimilarMatrixWitness S.A S.schurUpperTriangular :=
  S.similarWitness

theorem schurUpperTriangular_diag (S : SchurDecompositionPacket K n) :
    diagList S.schurUpperTriangular = S.eigenvalues :=
  S.diag_eq

theorem charpoly_schurUpperTriangular
    (S : SchurDecompositionPacket K n) :
    S.schurUpperTriangular.charpoly =
      ∏ i : Fin n, (X - C (S.schurUpperTriangular i i)) :=
  charpoly_of_upperTriangular_fin S.schurUpperTriangular S.upper_triangular

end SchurDecompositionPacket

/-! ## Basis-completion and recursive-step owner surfaces -/

/--
AFP `basis_completion` data: a nonzero vector has been extended to an ordered
basis whose first vector is the supplied vector.
-/
structure BasisCompletionPacket (K : Type*) [Field K] (n : ℕ) where
  /-- Vector to be extended. -/
  v : Fin n → K
  /-- The vector is nonzero. -/
  nonzero : v ≠ 0
  /-- Ordered completed basis. -/
  basis : Module.Basis (Fin n) K (Fin n → K)
  /-- Index occupied by the original vector in the completed basis. -/
  headIndex : Fin n
  /-- The distinguished basis vector is `v`. -/
  head_eq : basis headIndex = v

/--
One recursive AFP Schur step: an eigenvector is completed to an orthogonal
basis, conjugated into the first column, and the tail block is passed to the
recursive call.
-/
structure SchurStepPacket (K : Type*) [Field K] (n : ℕ) where
  /-- Input matrix. -/
  A : Matrix (Fin (n + 1)) (Fin (n + 1)) K
  /-- Selected eigenvalue. -/
  eigenvalue : K
  /-- Chosen nonzero eigenvector. -/
  eigenvector : Fin (n + 1) → K
  /-- Eigenvector equation in matrix-vector form. -/
  eigenvector_eq :
    A.mulVec eigenvector = fun i => eigenvalue * eigenvector i
  /-- Nonzero eigenvector witness. -/
  eigenvector_ne_zero : eigenvector ≠ 0
  /-- Basis completion used by the step. -/
  basisCompletion : BasisCompletionPacket K (n + 1)
  /-- Basis completion starts with the selected eigenvector. -/
  basisCompletion_head : basisCompletion.v = eigenvector
  /-- Change-of-basis matrix for the step. -/
  W : Matrix (Fin (n + 1)) (Fin (n + 1)) K
  /-- Inverse change-of-basis matrix. -/
  WInv : Matrix (Fin (n + 1)) (Fin (n + 1)) K
  /-- Left inverse relation. -/
  WInv_mul_W : WInv * W = 1
  /-- Right inverse relation. -/
  W_mul_WInv : W * WInv = 1
  /-- Conjugated matrix. -/
  A' : Matrix (Fin (n + 1)) (Fin (n + 1)) K
  /-- Conjugation equation. -/
  A'_eq : A' = WInv * A * W
  /-- First column has the eigenvalue followed by zeros. -/
  first_col_eq :
    ∀ i : Fin (n + 1), A' i 0 = if i = 0 then eigenvalue else 0

namespace SchurStepPacket

variable {K : Type*} [Field K] {n : ℕ}

theorem first_col_zero_of_ne_zero
    (S : SchurStepPacket K n) {i : Fin (n + 1)} (hi : i ≠ 0) :
    S.A' i 0 = 0 := by
  rw [S.first_col_eq]
  simp [hi]

theorem first_col_zero
    (S : SchurStepPacket K n) :
    S.A' 0 0 = S.eigenvalue := by
  rw [S.first_col_eq]
  simp

end SchurStepPacket

/-! ## Block characteristic-polynomial owner surfaces -/

/--
Upper block-triangular characteristic-polynomial packet.

This is the AFP `char_poly_0_block` conclusion, stated as a reusable certified
carrier over `Matrix.fromBlocks`.
-/
structure CharpolyUpperBlockPacket (K : Type*) [CommRing K]
    (n m : Type*) [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] where
  /-- Upper-left block. -/
  B : Matrix n n K
  /-- Upper-right block. -/
  C : Matrix n m K
  /-- Lower-right block. -/
  D : Matrix m m K
  /-- Whole upper block-triangular matrix. -/
  A : Matrix (n ⊕ m) (n ⊕ m) K
  /-- Block decomposition with zero lower-left block. -/
  A_eq : A = Matrix.fromBlocks B C 0 D
  /-- Characteristic polynomial multiplicativity witness. -/
  charpoly_eq : A.charpoly = B.charpoly * D.charpoly

namespace CharpolyUpperBlockPacket

variable {K n m : Type*} [CommRing K] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem char_poly_0_block (P : CharpolyUpperBlockPacket K n m) :
    P.A.charpoly = P.B.charpoly * P.D.charpoly :=
  P.charpoly_eq

end CharpolyUpperBlockPacket

/--
Lower block-triangular characteristic-polynomial packet.

This is the AFP `char_poly_0_block'` sibling with a zero upper-right block.
-/
structure CharpolyLowerBlockPacket (K : Type*) [CommRing K]
    (n m : Type*) [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] where
  /-- Upper-left block. -/
  B : Matrix n n K
  /-- Lower-left block. -/
  C : Matrix m n K
  /-- Lower-right block. -/
  D : Matrix m m K
  /-- Whole lower block-triangular matrix. -/
  A : Matrix (n ⊕ m) (n ⊕ m) K
  /-- Block decomposition with zero upper-right block. -/
  A_eq : A = Matrix.fromBlocks B 0 C D
  /-- Characteristic polynomial multiplicativity witness. -/
  charpoly_eq : A.charpoly = B.charpoly * D.charpoly

namespace CharpolyLowerBlockPacket

variable {K n m : Type*} [CommRing K] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem char_poly_0_block' (P : CharpolyLowerBlockPacket K n m) :
    P.A.charpoly = P.B.charpoly * P.D.charpoly :=
  P.charpoly_eq

end CharpolyLowerBlockPacket

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.SchurDecomposition
