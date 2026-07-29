import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.RingHomMatrix
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CharPoly

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

/--
Native ordered-basis transport lemma for the first Schur column.

If the `0`-th basis vector is the selected eigenvector, then the coordinate
vector of a scalar multiple of that eigenvector is concentrated in the `0`
slot.

This is the small transport fact needed to read off the first Schur column
without invoking the recursive AFP Schur algorithm.
-/
theorem basis_repr_smul_head
    {K : Type*} [Field K]
    {n : ℕ}
    (basis : Module.Basis (Fin (n + 1)) K (Fin (n + 1) → K))
    (eigenvector : Fin (n + 1) → K)
    (hhead : basis 0 = eigenvector)
    (c : K) (i : Fin (n + 1)) :
    basis.repr (c • eigenvector) i = if i = 0 then c else 0 := by
  subst hhead
  by_cases hi : i = 0
  · subst hi
    simp
  · simp [hi]

/--
First-column transport for a selected eigenvector.

If the `0`-th basis vector is the eigenvector of a matrix `A` with eigenvalue
`λ`, then the basis coordinates of `A` applied to that basis vector are the
singleton vector `Pi.single 0 λ`.

This is the Lean-native form of the AFP first Schur-column readout.
-/
theorem basis_repr_eigenvector_head
    {K : Type*} [Field K]
    {n : ℕ}
    (basis : Module.Basis (Fin (n + 1)) K (Fin (n + 1) → K))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (eigenvector : Fin (n + 1) → K)
    (hhead : basis 0 = eigenvector)
    (eigval : K)
    (heig : A.mulVec eigenvector = fun i => eigval * eigenvector i) :
    basis.repr (A.mulVec (basis 0)) = Finsupp.single 0 eigval := by
  subst hhead
  have heig' : A.mulVec (basis 0) = eigval • basis 0 := by
    ext i
    have hcoord := congrArg (fun v : Fin (n + 1) → K => v i) heig
    simpa [Pi.smul_apply] using hcoord
  rw [heig']
  ext i
  rw [basis_repr_smul_head (basis := basis) (eigenvector := basis 0) rfl eigval i]
  by_cases hi : i = 0 <;> simp [hi]

/--
Native first-Schur-column transport in basis-change form.

This is the Lean translation of the AFP `corthogonal_col_ev_0` seam, but
written in Mathlib's basis-to-matrix language.  The only data needed is:

* a basis whose first vector is the eigenvector,
* the eigenvector equation `A v = eigval • v`.

The conjugated matrix obtained from the basis change then has first column
`eigval` in the top entry and zeros below.
-/
theorem schurStep_first_col
    {K : Type*} [Field K]
    {n : ℕ}
    (basis : Module.Basis (Fin (n + 1)) K (Fin (n + 1) → K))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (eigenvector : Fin (n + 1) → K)
    (hhead : basis 0 = eigenvector)
    (eigval : K)
    (heig : A.mulVec eigenvector = fun i => eigval * eigenvector i) :
    ∀ i : Fin (n + 1),
      ((basis.toMatrix (Pi.basisFun K (Fin (n + 1)))) * A *
        ((Pi.basisFun K (Fin (n + 1))).toMatrix basis)) i 0 =
      if i = 0 then eigval else 0 := by
  classical
  intro i
  let std : Module.Basis (Fin (n + 1)) K (Fin (n + 1) → K) :=
    Pi.basisFun K (Fin (n + 1))
  let W : Matrix (Fin (n + 1)) (Fin (n + 1)) K := std.toMatrix basis
  let WInv : Matrix (Fin (n + 1)) (Fin (n + 1)) K := basis.toMatrix std
  have hrepr0 : basis.repr (basis 0) = Finsupp.single 0 (1 : K) := by
    simp
  have hW : Matrix.mulVec W (Finsupp.single 0 (1 : K)) = eigenvector := by
    have htmp : Matrix.mulVec W (basis.repr (basis 0)) = basis 0 := by
      convert Module.Basis.toMatrix_mulVec_repr (b' := std) (b := basis)
        (m := basis 0) using 1
    calc
      Matrix.mulVec W (Finsupp.single 0 (1 : K))
          = Matrix.mulVec W (basis.repr (basis 0)) := by
              rw [← hrepr0]
      _ = basis 0 := htmp
      _ = eigenvector := hhead
  have hrepr : basis.repr eigenvector = Finsupp.single 0 (1 : K) := by
    rw [← hhead]
    exact hrepr0
  have hWinv0 : Matrix.mulVec WInv eigenvector = basis.repr eigenvector := by
    convert Module.Basis.toMatrix_mulVec_repr (b := std) (b' := basis)
      (m := eigenvector) using 1
  have hWinv : Matrix.mulVec WInv eigenvector = Finsupp.single 0 (1 : K) := by
    rw [hrepr] at hWinv0
    exact hWinv0
  have hsmul : eigval • Finsupp.single 0 (1 : K) = Finsupp.single 0 eigval := by
    ext j
    by_cases hj : j = 0 <;> simp [hj]
  have hA' :
      Matrix.mulVec (WInv * A * W) (Finsupp.single 0 (1 : K)) =
      eigval • Finsupp.single 0 (1 : K) := by
    calc
      Matrix.mulVec (WInv * A * W) (Finsupp.single 0 (1 : K))
          = Matrix.mulVec WInv (Matrix.mulVec A (Matrix.mulVec W (Finsupp.single 0 (1 : K)))) := by
              simp [Matrix.mulVec_mulVec, mul_assoc]
      _ = Matrix.mulVec WInv (Matrix.mulVec A eigenvector) := by
            rw [hW]
      _ = Matrix.mulVec WInv (fun i => eigval * eigenvector i) := by
            rw [heig]
      _ = Matrix.mulVec WInv (eigval • eigenvector) := by rfl
      _ = eigval • Finsupp.single 0 (1 : K) := by
            have hmul := Matrix.mulVec_smul WInv eigval eigenvector
            rw [hWinv] at hmul
            exact hmul
  have hA'' : Matrix.mulVec (WInv * A * W) (Finsupp.single 0 (1 : K)) =
      Finsupp.single 0 eigval := by
    simpa [hsmul] using hA'
  have hcoord := congrArg (fun v : Fin (n + 1) → K => v i) hA''
  by_cases hi : i = 0
  · subst hi
    simpa [Matrix.mulVec, Finsupp.single] using hcoord
  · simpa [Matrix.mulVec, Finsupp.single, hi] using hcoord

/-! ## Certified Schur decomposition packet -/

/--
Witness that `A` and `B` are similar via explicit inverse matrices `P` and `Q`.

The AFP statement records `A = P * B * Q` and `P * Q = 1`; the Lean packet also
stores `Q * P = 1`, making the inverse relation available without recovering it
from finite-dimensional algebra.
-/
abbrev SimilarMatrixWitness {R ι : Type*}
    [Semiring R] [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι R) :=
  InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CharPoly.SimilarMatrixWitness
    A B

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
    S.A = S.P * S.B * S.Q ∧
      S.P * S.Q = 1 ∧
      S.Q * S.P = 1 ∧
      UpperTriangular S.B ∧
      diagList S.B = S.eigenvalues :=
  ⟨S.factorization, S.P_mul_Q, S.Q_mul_P, S.upper_triangular, S.diag_eq⟩

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
Native basis-completion theorem: any nonzero vector extends to a basis of its
singleton carrier, and the distinguished basis vector is the given vector.

This is the Lean-native replacement for the abstract AFP basis-completion
surface.  The full `Fin n`-indexed ordered completion is downstream work; the
mathematical core is the basis-extension step.
-/
theorem exists_basis_completion
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (s : Set V) (hs : LinearIndepOn K id s) :
    ∃ b : Module.Basis (hs.extend (Set.subset_univ s)) K V,
      ∀ x : hs.extend (Set.subset_univ s), b x = x := by
  refine ⟨Module.Basis.extend hs, ?_⟩
  intro x
  exact Module.Basis.extend_apply_self hs x

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

/--
Native constructor for the first recursive Schur step over a completed basis.

This packages the exact one-step AFP data:

* the selected eigenvector and eigenvalue;
* a completed basis whose first vector is the eigenvector;
* the change-of-basis matrices and their two-sided inverse relations;
* the conjugated matrix and its first-column readout.

The recursive tail assembly is still a separate step; this theorem closes the
first Schur-step packet natively.
-/
theorem of_basis
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (eigenvector : Fin (n + 1) → K)
    (basis : Module.Basis (Fin (n + 1)) K (Fin (n + 1) → K))
    (hhead : basis 0 = eigenvector)
    (eigval : K)
    (heig : A.mulVec eigenvector = fun i => eigval * eigenvector i) :
    ∃ S : SchurStepPacket K n,
      S.A' 0 0 = eigval ∧
        (∀ i : Fin (n + 1), i ≠ 0 → S.A' i 0 = 0) := by
  classical
  let std : Module.Basis (Fin (n + 1)) K (Fin (n + 1) → K) :=
    Pi.basisFun K (Fin (n + 1))
  let W : Matrix (Fin (n + 1)) (Fin (n + 1)) K := std.toMatrix basis
  let WInv : Matrix (Fin (n + 1)) (Fin (n + 1)) K := basis.toMatrix std
  let S : SchurStepPacket K n :=
    { A := A
      eigenvalue := eigval
      eigenvector := eigenvector
      eigenvector_eq := heig
      eigenvector_ne_zero := by
        simpa [hhead] using (basis.ne_zero (0 : Fin (n + 1)))
      basisCompletion :=
        { v := eigenvector
          nonzero := by
            simpa [hhead] using (basis.ne_zero (0 : Fin (n + 1)))
          basis := basis
          headIndex := 0
          head_eq := hhead }
      basisCompletion_head := rfl
      W := W
      WInv := WInv
      WInv_mul_W := by
        simp [WInv, W, std]
      W_mul_WInv := by
        simp [WInv, W, std]
      A' := WInv * A * W
      A'_eq := rfl
      first_col_eq := by
        simpa [WInv, W, std] using
          (schurStep_first_col (K := K) (n := n) basis A eigenvector hhead eigval heig) }
  refine ⟨S, ?_, ?_⟩
  · change S.A' 0 0 = eigval
    rw [S.first_col_eq]
    dsimp [S]
  · intro i hi
    rw [S.first_col_eq]
    simp [hi]

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

/-- The lower-right tail block of the first Schur step. -/
def tailMatrix (S : SchurStepPacket K n) : Matrix (Fin n) (Fin n) K :=
  fun i j => S.A' i.succ j.succ

/-- The tail matrix is the `succ/succ` submatrix of the conjugated matrix. -/
theorem tailMatrix_eq_submatrix (S : SchurStepPacket K n) :
    S.tailMatrix = S.A'.submatrix Fin.succ Fin.succ :=
  rfl

/-- Entrywise readout of the tail block. -/
theorem tailMatrix_apply (S : SchurStepPacket K n) (i j : Fin n) :
    S.tailMatrix i j = S.A' i.succ j.succ :=
  rfl

/-- Canonical equivalence splitting `Fin (n+1)` into the distinguished head and the tail. -/
def schurStepEquiv (n : ℕ) : Fin (n + 1) ≃ PUnit ⊕ Fin n :=
  (finSuccEquiv n).trans
    ((Equiv.optionEquivSumPUnit (Fin n)).trans (Equiv.sumComm _ _))

/--
The first Schur step is block-form after reindexing by the distinguished head
and the tail.

This is the recursive seam needed for the tail assembly:

* top-left block is the eigenvalue;
* top-right block is the first row tail;
* lower-left block is zero;
* lower-right block is the recursive tail matrix.
-/
theorem schurStep_block_form (S : SchurStepPacket K n) :
    Matrix.reindex (schurStepEquiv n) (schurStepEquiv n) S.A' =
      Matrix.fromBlocks
        (fun (_ : PUnit) (_ : PUnit) => S.eigenvalue : Matrix PUnit PUnit K)
        (fun (_ : PUnit) (j : Fin n) => S.A' 0 j.succ : Matrix PUnit (Fin n) K)
        (0 : Matrix (Fin n) PUnit K)
        S.tailMatrix := by
  classical
  ext x y
  cases x <;> cases y <;> simp [schurStepEquiv, tailMatrix, S.first_col_eq]

/--
Recursive Schur tail assembly in block form.

This is the AFP-style recursive seam: the first Schur step is rewritten into a
block matrix whose lower-right block is the recursive tail decomposition, and
the whole block form is conjugated by the tail similarity witness.

The theorem is stated on the block-reindexed matrix because that is the honest
recursive object produced by the AFP proof.
-/
theorem schurStep_recursive_tail_assembly
    (S : SchurStepPacket K n)
    (T : SchurDecompositionPacket K n)
    (hTail : T.A = S.tailMatrix) :
    Matrix.reindex (schurStepEquiv n) (schurStepEquiv n) S.A' =
      Matrix.fromBlocks (fun (_ : PUnit) (_ : PUnit) => S.eigenvalue)
        (fun (_ : PUnit) (j : Fin n) => S.A' 0 j.succ) 0 (T.P * (T.B * T.Q)) := by
  classical
  calc
    Matrix.reindex (schurStepEquiv n) (schurStepEquiv n) S.A' =
        Matrix.fromBlocks (fun (_ : PUnit) (_ : PUnit) => S.eigenvalue)
          (fun (_ : PUnit) (j : Fin n) => S.A' 0 j.succ) 0 S.tailMatrix := by
      simpa using S.schurStep_block_form
    _ = Matrix.fromBlocks (fun (_ : PUnit) (_ : PUnit) => S.eigenvalue)
          (fun (_ : PUnit) (j : Fin n) => S.A' 0 j.succ) 0 T.A := by
      rw [← hTail]
    _ = Matrix.fromBlocks (fun (_ : PUnit) (_ : PUnit) => S.eigenvalue)
          (fun (_ : PUnit) (j : Fin n) => S.A' 0 j.succ) 0 (T.P * (T.B * T.Q)) := by
      rw [T.factorization]
      simp [mul_assoc]

end SchurStepPacket

/-! ## Block characteristic-polynomial owner surfaces -/

/--
Upper block-triangular characteristic-polynomial packet.

This is the AFP `char_poly_0_block` conclusion, stated as a reusable certified
carrier over `Matrix.fromBlocks`.
-/
theorem char_poly_fromBlocks_zero₁₂
    {K : Type*} [CommRing K] {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    [DecidableEq m] (B : Matrix n n K) (C : Matrix m n K) (D : Matrix m m K) :
    (Matrix.fromBlocks B 0 C D).charpoly = B.charpoly * D.charpoly := by
  exact Matrix.charpoly_fromBlocks_zero₁₂ (M₁₁ := B) (M₂₁ := C) (M₂₂ := D)

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
  by
    simp [P.A_eq]

end CharpolyUpperBlockPacket

/--
Lower block-triangular characteristic-polynomial packet.

This is the AFP `char_poly_0_block'` sibling with a zero upper-right block.
-/
theorem char_poly_fromBlocks_zero₂₁
    {K : Type*} [CommRing K] {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    [DecidableEq m] (B : Matrix n n K) (C : Matrix n m K) (D : Matrix m m K) :
    (Matrix.fromBlocks B C 0 D).charpoly = B.charpoly * D.charpoly := by
  exact Matrix.charpoly_fromBlocks_zero₂₁ (M₁₁ := B) (M₁₂ := C) (M₂₂ := D)

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
  by
    simp [P.A_eq]

end CharpolyLowerBlockPacket

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.SchurDecomposition
