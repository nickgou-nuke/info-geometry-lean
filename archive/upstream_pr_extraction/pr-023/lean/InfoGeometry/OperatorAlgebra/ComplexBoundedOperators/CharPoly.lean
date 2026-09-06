import Mathlib

/-!
# InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CharPoly

Lean-native owner surface for AFP `Jordan_Normal_Form.Char_Poly`.

Mathlib already provides `Matrix.charpoly`, Cayley-Hamilton, roots of the
characteristic polynomial, and the matrix spectrum bridge.  This module packages
those facts in the AFP vocabulary used by the surrounding Jordan-normal-form
ports: eigenvectors, eigenvalues, characteristic matrices, factorized
characteristic polynomials, and block/triangular readouts.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CharPoly

open scoped BigOperators
open Polynomial

/-- Entrywise upper-triangular predicate for ordered finite index types. -/
def UpperTriangular {R ι : Type*} [Zero R] [LT ι] (A : Matrix ι ι R) : Prop :=
  ∀ ⦃i j : ι⦄, j < i → A i j = 0

/-- Explicit similarity witness `A = P * B * Q`, with inverse equations. -/
structure SimilarMatrixWitness {R ι : Type*}
    [Semiring R] [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι R) where
  /-- Change-of-basis matrix. -/
  P : Matrix ι ι R
  /-- Inverse change-of-basis matrix. -/
  Q : Matrix ι ι R
  /-- Left inverse relation. -/
  P_mul_Q : P * Q = 1
  /-- Right inverse relation. -/
  Q_mul_P : Q * P = 1
  /-- Similarity factorization. -/
  factorization : A = P * B * Q

namespace SimilarMatrixWitness

/-- Reflexive similarity witness. -/
def refl {R ι : Type*}
    [Semiring R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) : SimilarMatrixWitness A A where
  P := 1
  Q := 1
  P_mul_Q := by simp
  Q_mul_P := by simp
  factorization := by simp

end SimilarMatrixWitness

/-- AFP `eigenvector`: a nonzero vector satisfying `A v = k v`. -/
def Eigenvector {K ι : Type*} [Semiring K] [Fintype ι]
    (A : Matrix ι ι K) (v : ι → K) (k : K) : Prop :=
  v ≠ 0 ∧ A.mulVec v = k • v

/-- AFP `eigenvalue`, expressed through the characteristic polynomial root set.

For finite matrices over fields this is equivalent to mathlib's matrix spectrum
predicate; see `eigenvalue_iff_mem_spectrum`.
-/
def Eigenvalue {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (k : K) : Prop :=
  (Matrix.charpoly A).IsRoot k

/-- Characteristic matrix `A - k I`, matching the AFP sign convention. -/
def charMatrix {K ι : Type*} [Ring K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (k : K) : Matrix ι ι K :=
  A - Matrix.scalar ι k

/-- Characteristic polynomial abbreviation in AFP style. -/
abbrev charPoly {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) : K[X] :=
  Matrix.charpoly A

@[simp]
theorem charPoly_eq {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) :
    charPoly A = Matrix.charpoly A :=
  rfl

/-- Eigenvectors are preserved by matrix powers. -/
theorem eigenvector_pow {K ι : Type*} [CommSemiring K] [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K} {v : ι → K} {k : K}
    (hv : Eigenvector A v k) (i : Nat) :
    (A ^ i).mulVec v = (k ^ i) • v := by
  rcases hv with ⟨_, hAv⟩
  induction i with
  | zero =>
      simp
  | succ i ih =>
      calc
        (A ^ (i + 1)).mulVec v = A.mulVec ((A ^ i).mulVec v) := by
          rw [pow_succ']
          simp [Matrix.mulVec_mulVec]
        _ = A.mulVec ((k ^ i) • v) := by rw [ih]
        _ = (k ^ i) • (A.mulVec v) := by
          ext j
          simp [Matrix.mulVec]
        _ = (k ^ i) • (k • v) := by rw [hAv]
        _ = (k ^ (i + 1)) • v := by
          ext j
          simp [pow_succ, mul_assoc]

/-- Mathlib spectrum bridge for the AFP eigenvalue predicate. -/
theorem eigenvalue_iff_mem_spectrum {K ι : Type*}
    [Field K] [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K} {k : K} :
    Eigenvalue A k ↔ k ∈ spectrum K A := by
  rw [Eigenvalue]
  exact (Matrix.mem_spectrum_iff_isRoot_charpoly (A := A) (r := k)).symm

/-- AFP `spectrum_root_char_poly`, in characteristic-polynomial form. -/
theorem eigenvalue_root_charPoly {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (k : K) :
    Eigenvalue A k ↔ (charPoly A).eval k = 0 := by
  simp [Eigenvalue, Polynomial.IsRoot]

/-- The characteristic polynomial of a finite matrix is monic. -/
theorem charPoly_monic {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) :
    (charPoly A).Monic :=
  Matrix.charpoly_monic A

/-- Upper-triangular characteristic polynomial readout. -/
theorem charPoly_upperTriangular
    {K : Type*} [CommRing K] {n : Nat}
    (A : Matrix (Fin n) (Fin n) K)
    (hA : UpperTriangular A) :
    charPoly A = ∏ i : Fin n, (X - C (A i i)) :=
  Matrix.charpoly_of_upperTriangular A (by
    intro i j hij
    exact hA hij)

/-- witness-gated (Native Closure Mandated: Closure Debt) characteristic-polynomial invariance under similarity. -/
structure SimilarCharPolyPacket {K ι : Type*}
    [CommRing K] [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι K) where
  /-- Explicit similarity witness. -/
  witness : SimilarMatrixWitness A B
  /-- Characteristic-polynomial invariance carried by the packet. -/
  charpoly_eq : charPoly A = charPoly B

/-- Projection for characteristic-polynomial invariance under similarity. -/
theorem charPoly_similar {K ι : Type*}
    [CommRing K] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι K}
    (P : SimilarCharPolyPacket A B) :
    charPoly A = charPoly B :=
  P.charpoly_eq

/-- Native characteristic-polynomial invariance under explicit similarity data. -/
theorem charPoly_similar_of_witness {K ι : Type*}
    [CommRing K] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι K}
    (W : SimilarMatrixWitness A B) :
    charPoly A = charPoly B := by
  rw [charPoly, W.factorization, charPoly]
  calc
    (W.P * B * W.Q).charpoly = (W.P * (B * W.Q)).charpoly := by
      rw [Matrix.mul_assoc]
    _ = ((B * W.Q) * W.P).charpoly := by
      rw [Matrix.charpoly_mul_comm]
    _ = (B * (W.Q * W.P)).charpoly := by
      rw [Matrix.mul_assoc]
    _ = B.charpoly := by
      rw [W.Q_mul_P, Matrix.mul_one]

/--
Factorized characteristic polynomial packet.

This is the Lean owner surface for AFP `char_poly_factorized`; mathlib supplies
the algebraically closed splitting infrastructure, while the packet records the
linear-factor list used by downstream JNF code.
-/
structure CharPolyFactorizationPacket (n : Nat) where
  /-- Input complex matrix. -/
  A : Matrix (Fin n) (Fin n) ℂ
  /-- Linear-factor roots. -/
  roots : List ℂ
  /-- Product of linear factors equals the characteristic polynomial. -/
  factorization : charPoly A = roots.foldr (fun a p => (X - C a) * p) 1
  /-- The root list has matrix dimension length. -/
  length_eq : roots.length = n

namespace CharPolyFactorizationPacket

/-- Native factorization of the characteristic polynomial over `ℂ`. -/
theorem charPoly_factorized_native (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ roots : List ℂ,
      charPoly A = roots.foldr (fun a p => (X - C a) * p) 1 ∧ roots.length = n := by
  classical
  let r : Multiset ℂ := (charPoly A).roots
  have hsplits : (charPoly A).Splits := IsAlgClosed.splits (charPoly A)
  refine ⟨r.toList, ?_, ?_⟩
  · have hsplits : (charPoly A).Splits := IsAlgClosed.splits (charPoly A)
    have hprod : charPoly A = (r.map fun a => X - C a).prod := by
      simpa [r] using hsplits.eq_prod_roots_of_monic (Matrix.charpoly_monic A)
    rw [hprod, ← Multiset.prod_map_toList, List.prod_eq_foldr, List.foldr_map]
  · have hcard : r.card = n := by
      have h1 : (charPoly A).natDegree = r.card := by
        simpa [r] using hsplits.natDegree_eq_card_roots
      rw [← h1, Matrix.charpoly_natDegree_eq_dim]
      simp
    simpa [r, hcard] using (Multiset.length_toList r)

/-- Native constructor for the factorization packet. -/
noncomputable def ofMatrix (A : Matrix (Fin n) (Fin n) ℂ) : CharPolyFactorizationPacket n := by
  classical
  let h := charPoly_factorized_native (n := n) A
  refine
    { A := A
      roots := Classical.choose h
      factorization := (Classical.choose_spec h).1
      length_eq := (Classical.choose_spec h).2 }

/-- Projection corresponding to AFP `char_poly_factorized`. -/
theorem charPoly_factorized {n : Nat} (P : CharPolyFactorizationPacket n) :
    ∃ roots : List ℂ,
      charPoly P.A = roots.foldr (fun a p => (X - C a) * p) 1 ∧ roots.length = n :=
  ⟨P.roots, P.factorization, P.length_eq⟩

end CharPolyFactorizationPacket

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CharPoly
