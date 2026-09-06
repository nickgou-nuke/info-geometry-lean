import Mathlib.Tactic

/-!
# InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.VSConnect

Lean-native finite-dimensional analogue of AFP `Jordan_Normal_Form.VS_Connect`.

The Isabelle theory connects its custom matrix/vector carriers to a separate
vector-space library.  In Lean, finite vectors `Fin n → K` and finite matrices
`Matrix (Fin m) (Fin n) K` already inherit their module and algebra structures
from typeclasses.  This file records the bridge explicitly with list spans,
row/column lists, and row/column spaces.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.VSConnect

open scoped BigOperators

/-- Finite vector carrier corresponding to AFP `carrier_vec n`. -/
abbrev FiniteVector (K : Type*) (n : Nat) :=
  Fin n → K

/-- Finite matrix carrier corresponding to AFP `carrier_mat m n`. -/
abbrev FiniteMatrix (K : Type*) (m n : Nat) :=
  Matrix (Fin m) (Fin n) K

/-- The list-span bridge from concrete finite vectors to Lean submodules. -/
def listSpan (K : Type*) [Semiring K] {n : Nat}
    (vs : List (FiniteVector K n)) : Submodule K (FiniteVector K n) :=
  Submodule.span K {v | v ∈ vs}

/-- Every list member belongs to its span. -/
theorem mem_listSpan_of_mem {K : Type*} [Semiring K] {n : Nat}
    {v : FiniteVector K n} {vs : List (FiniteVector K n)} (hv : v ∈ vs) :
    v ∈ listSpan K vs :=
  Submodule.subset_span hv

/-- Monotonicity of list spans under list-membership inclusion. -/
theorem listSpan_mono {K : Type*} [Semiring K] {n : Nat}
    {vs ws : List (FiniteVector K n)}
    (h : ∀ v : FiniteVector K n, v ∈ vs → v ∈ ws) :
    listSpan K vs ≤ listSpan K ws :=
  Submodule.span_mono (by
    intro v hv
    exact h v hv)

@[simp]
theorem listSpan_nil {K : Type*} [Semiring K] {n : Nat} :
    listSpan K ([] : List (FiniteVector K n)) = ⊥ := by
  ext v
  simp [listSpan]

/-- Extension principle for spans of lists with the same members. -/
theorem listSpan_ext {K : Type*} [Semiring K] {n : Nat}
    {vs ws : List (FiniteVector K n)}
    (h : ∀ v : FiniteVector K n, v ∈ vs ↔ v ∈ ws) :
    listSpan K vs = listSpan K ws := by
  exact le_antisymm
    (listSpan_mono (K := K) (fun v hv => (h v).1 hv))
    (listSpan_mono (K := K) (fun v hv => (h v).2 hv))

/-- Span of a cons list is the span of the inserted vector set. -/
theorem listSpan_cons {K : Type*} [Semiring K] {n : Nat}
    (v : FiniteVector K n) (vs : List (FiniteVector K n)) :
    listSpan K (v :: vs) = Submodule.span K (insert v {w | w ∈ vs}) := by
  apply congrArg (Submodule.span K)
  ext w
  simp

/-- Finite matrix rows as a list of finite vectors. -/
def rows {K : Type*} {m n : Nat}
    (A : FiniteMatrix K m n) : List (FiniteVector K n) :=
  List.ofFn fun i : Fin m => fun j : Fin n => A i j

/-- Finite matrix columns as a list of finite vectors. -/
def cols {K : Type*} {m n : Nat}
    (A : FiniteMatrix K m n) : List (FiniteVector K m) :=
  List.ofFn fun j : Fin n => fun i : Fin m => A i j

@[simp]
theorem rows_length {K : Type*} {m n : Nat} (A : FiniteMatrix K m n) :
    (rows A).length = m := by
  simp [rows]

@[simp]
theorem cols_length {K : Type*} {m n : Nat} (A : FiniteMatrix K m n) :
    (cols A).length = n := by
  simp [cols]

/-- Row space of a finite matrix. -/
def rowSpace (K : Type*) [Semiring K] {m n : Nat}
    (A : FiniteMatrix K m n) : Submodule K (FiniteVector K n) :=
  listSpan K (rows A)

/-- The row space of the identity matrix is the whole finite vector space. -/
theorem rowSpace_identity_eq_top {K : Type*} [Semiring K] (n : Nat) :
    rowSpace K (1 : FiniteMatrix K n n) = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro x
    let b : Module.Basis (Fin n) K (FiniteVector K n) := Pi.basisFun K (Fin n)
    have hrows : ∀ i : Fin n, b i ∈ rows (1 : FiniteMatrix K n n) := by
      intro i
      rw [rows]
      refine (List.mem_ofFn).2 ?_
      refine ⟨i, ?_⟩
      ext j
      by_cases h : i = j <;> simp [b, Pi.basisFun, Matrix.one_apply, h]
    rw [← b.sum_repr x]
    classical
    have hsum :
        ∑ i, (b.repr x) i • b i ∈ rowSpace K (1 : FiniteMatrix K n n) := by
      simpa using
        (Submodule.sum_mem (rowSpace K (1 : FiniteMatrix K n n))
          (t := Finset.univ) (f := fun i : Fin n => (b.repr x) i • b i) (by
            intro i hi
            exact Submodule.smul_mem _ _ (mem_listSpan_of_mem (K := K) (n := n)
              (v := b i)
              (vs := rows (1 : FiniteMatrix K n n))
              (hrows i))))
    simpa [b] using hsum

/-- Column space of a finite matrix. -/
def colSpace (K : Type*) [Semiring K] {m n : Nat}
    (A : FiniteMatrix K m n) : Submodule K (FiniteVector K m) :=
  listSpan K (cols A)

/-- Row membership introduction from the concrete row list. -/
theorem row_mem_rowSpace {K : Type*} [Semiring K] {m n : Nat}
    (A : FiniteMatrix K m n) {v : FiniteVector K n}
    (hv : v ∈ rows A) :
    v ∈ rowSpace K A :=
  mem_listSpan_of_mem hv

/-- Column membership introduction from the concrete column list. -/
theorem col_mem_colSpace {K : Type*} [Semiring K] {m n : Nat}
    (A : FiniteMatrix K m n) {v : FiniteVector K m}
    (hv : v ∈ cols A) :
    v ∈ colSpace K A :=
  mem_listSpan_of_mem hv

/--
Carrier bridge packet for finite vectors.

This records the Lean replacements for AFP carrier facts: a chosen list of
vectors spans a submodule, with optional basis/independence witnesses supplied
when a downstream theorem needs them.
-/
structure VectorCarrierPacket (K : Type*) [Semiring K] (n : Nat) where
  /-- Concrete finite-vector list. -/
  vectors : List (FiniteVector K n)
  /-- The associated Lean submodule. -/
  carrier : Submodule K (FiniteVector K n)
  /-- The carrier is exactly the span of the concrete list. -/
  carrier_eq_span : carrier = listSpan K vectors

/-- A basis-level finite-vector packet, property-gated (Native Closure Mandated: Closure Debt) for downstream basis APIs. -/
structure VectorBasisPacket (K : Type*) [Field K] (n : Nat) where
  /-- Index type for the basis. -/
  basisIndex : Type
  /-- Finite basis index. -/
  finiteIndex : Fintype basisIndex
  /-- Decidable equality for the basis index. -/
  decidableIndex : DecidableEq basisIndex
  /-- Basis vectors indexed by `basisIndex`. -/
  basisVector : basisIndex → FiniteVector K n
  /-- Predicate-level property that the indexed vectors are linearly independent. -/
  independent : LinearIndependent K basisVector
  /-- Predicate-level property that the indexed vectors span the full space. -/
  spans_top : Submodule.span K (Set.range basisVector) = ⊤

attribute [instance] VectorBasisPacket.finiteIndex
attribute [instance] VectorBasisPacket.decidableIndex

/-- Matrix-space bridge packet for row and column spaces. -/
structure MatrixCarrierPacket (K : Type*) [Semiring K] (m n : Nat) where
  /-- Concrete matrix. -/
  matrix : FiniteMatrix K m n
  /-- Row-space carrier. -/
  rowCarrier : Submodule K (FiniteVector K n)
  /-- Column-space carrier. -/
  colCarrier : Submodule K (FiniteVector K m)
  /-- Row-space carrier agrees with the concrete row span. -/
  rowCarrier_eq : rowCarrier = rowSpace K matrix
  /-- Column-space carrier agrees with the concrete column span. -/
  colCarrier_eq : colCarrier = colSpace K matrix

namespace MatrixCarrierPacket

variable {K : Type*} [Semiring K] {m n : Nat}

theorem rowSpace_eq (P : MatrixCarrierPacket K m n) :
    P.rowCarrier = rowSpace K P.matrix :=
  P.rowCarrier_eq

theorem colSpace_eq (P : MatrixCarrierPacket K m n) :
    P.colCarrier = colSpace K P.matrix :=
  P.colCarrier_eq

end MatrixCarrierPacket

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.VSConnect
