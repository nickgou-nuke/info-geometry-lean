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

namespace CharPoly

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

/-- Explicit 2×2 determinant readout. -/
def det_2x2 (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

/-- Explicit 2×2 characteristic polynomial readout. -/
def char_poly_2x2 (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℂ :=
  det_2x2 (x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - M)

/-- The explicit 2×2 readout agrees with the matrix characteristic polynomial evaluation. -/
theorem char_poly_2x2_eq_eval_charpoly
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) :
    char_poly_2x2 M x = (Matrix.charpoly M).eval x := by
  simpa [char_poly_2x2, det_2x2, Matrix.smul_eq_mul_diagonal, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.det_fin_two] using (Matrix.eval_charpoly M x).symm

/-- The explicit `2×2` complex characteristic polynomial evaluates to the Zhukovsky form. -/
theorem char_poly_eq_zhukovsky
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : Matrix.det M = 1) :
    char_poly_2x2 M x = x^2 - Tr * x + 1 := by
  rw [char_poly_2x2_eq_eval_charpoly, Matrix.charpoly_fin_two, h_tr, h_det]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]

/-- Nonzero roots of the explicit determinant-one characteristic polynomial satisfy the Zhukovsky relation. -/
theorem eigenvalue_zhukovsky_relation_2x2
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : Matrix.det M = 1)
    (h_eigen : char_poly_2x2 M x = 0) (hx : x ≠ 0) :
    x + x⁻¹ = Tr := by
  have hchar := char_poly_eq_zhukovsky M x Tr h_tr h_det
  rw [h_eigen] at hchar
  have hquad : x^2 - Tr * x + 1 = 0 := hchar.symm
  have hmul : x * (x + x⁻¹ - Tr) = 0 := by
    field_simp [hx]
    ring_nf at hquad ⊢
    exact hquad
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hx)

/-- For nonzero `x`, the explicit determinant-one root condition is equivalent to the Zhukovsky relation. -/
theorem char_poly_2x2_root_iff_zhukovsky_relation
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : Matrix.det M = 1) (hx : x ≠ 0) :
    char_poly_2x2 M x = 0 ↔ x + x⁻¹ = Tr := by
  constructor
  · intro h_eigen
    exact eigenvalue_zhukovsky_relation_2x2 M x Tr h_tr h_det h_eigen hx
  · intro hrel
    rw [char_poly_eq_zhukovsky M x Tr h_tr h_det]
    have hmul : x * (x + x⁻¹ - Tr) = 0 := by
      rw [hrel]
      ring
    field_simp [hx] at hmul
    ring_nf at hmul ⊢
    exact hmul

/-- Nonzero roots of the explicit determinant-one characteristic polynomial are closed under spectral inversion. -/
theorem inverse_root_of_root_2x2
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : Matrix.det M = 1)
    (h_eigen : char_poly_2x2 M x = 0) (hx : x ≠ 0) :
    char_poly_2x2 M x⁻¹ = 0 := by
  have hrel : x + x⁻¹ = Tr :=
    eigenvalue_zhukovsky_relation_2x2 M x Tr h_tr h_det h_eigen hx
  exact (char_poly_2x2_root_iff_zhukovsky_relation M x⁻¹ Tr h_tr h_det (inv_ne_zero hx)).mpr
    (by simpa [inv_inv, add_comm] using hrel)

/-- A trace-free determinant-one `2×2` complex matrix has eigenvalues satisfying `x^2 = -1`. -/
theorem trace_free_eigenvalue_compact_C_2x2
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ)
    (h_tr : Matrix.trace M = 0) (h_det : Matrix.det M = 1)
    (h_eigen : char_poly_2x2 M x = 0) :
    x^2 = -1 := by
  have hchar : x^2 + 1 = 0 := by
    have h := char_poly_eq_zhukovsky (M := M) (x := x) (Tr := 0) h_tr h_det
    rw [h_eigen] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h.symm
  exact eq_neg_of_add_eq_zero_left hchar

/-- A complex number whose square is `-1` lies on the squared-norm unit circle. -/
theorem normSq_eq_one_of_sq_eq_neg_one (x : ℂ) (h : x^2 = -1) :
    Complex.normSq x = 1 := by
  have hnorm : Complex.normSq (x^2) = Complex.normSq (-1 : ℂ) := by
    rw [h]
  have hs : Complex.normSq x * Complex.normSq x = 1 := by
    simpa [pow_two] using hnorm
  have hn : 0 ≤ Complex.normSq x := Complex.normSq_nonneg x
  nlinarith

/-- The only complex roots of `x^2 = -1` are `I` and `-I`. -/
theorem sq_eq_neg_one_iff_eq_I_or_neg_I (x : ℂ) :
    x^2 = -1 ↔ x = Complex.I ∨ x = -Complex.I := by
  constructor
  · intro h
    have hf : (x - Complex.I) * (x + Complex.I) = 0 := by
      calc
        (x - Complex.I) * (x + Complex.I) = x^2 - Complex.I^2 := by ring
        _ = x^2 + 1 := by simp [Complex.I_mul_I, pow_two]
        _ = 0 := by rw [h]; norm_num
    rcases mul_eq_zero.mp hf with hx | hx
    · left
      exact sub_eq_zero.mp hx
    · right
      exact eq_neg_of_add_eq_zero_left hx
  · intro h
    rcases h with rfl | rfl <;> norm_num

/-- Explicit `2×2` trace-free determinant-one roots lie on the squared-norm unit circle. -/
theorem trace_free_eigenvalue_normSq_eq_one_2x2
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ)
    (h_tr : Matrix.trace M = 0) (h_det : Matrix.det M = 1)
    (h_eigen : char_poly_2x2 M x = 0) :
    Complex.normSq x = 1 :=
  normSq_eq_one_of_sq_eq_neg_one x
    (trace_free_eigenvalue_compact_C_2x2 M x h_tr h_det h_eigen)

/-- Explicit `2×2` trace-free determinant-one roots are exactly the two complex points `±I`. -/
theorem trace_free_eigenvalue_eq_I_or_neg_I_2x2
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ)
    (h_tr : Matrix.trace M = 0) (h_det : Matrix.det M = 1)
    (h_eigen : char_poly_2x2 M x = 0) :
    x = Complex.I ∨ x = -Complex.I :=
  (sq_eq_neg_one_iff_eq_I_or_neg_I x).mp
    (trace_free_eigenvalue_compact_C_2x2 M x h_tr h_det h_eigen)

/-- Explicit `2×2` trace-free determinant-one roots have inverse equal to their negative. -/
theorem trace_free_eigenvalue_inv_eq_neg_2x2
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ)
    (h_tr : Matrix.trace M = 0) (h_det : Matrix.det M = 1)
    (h_eigen : char_poly_2x2 M x = 0) :
    x⁻¹ = -x := by
  have hsq : x^2 = -1 := trace_free_eigenvalue_compact_C_2x2 M x h_tr h_det h_eigen
  apply inv_eq_of_mul_eq_one_right
  calc
    x * (-x) = -(x^2) := by ring
    _ = 1 := by rw [hsq]; norm_num

/-- The `2×2` complex characteristic polynomial evaluates to the Zhukovsky quadratic form. -/
theorem charPoly_eval_fin_two_zhukovsky
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : Matrix.det M = 1) :
    (Matrix.charpoly M).eval x = x^2 - Tr * x + 1 := by
  rw [Matrix.charpoly_fin_two, h_tr, h_det]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]

/-- Nonzero roots of the Mathlib determinant-one characteristic polynomial satisfy the Zhukovsky relation. -/
theorem charPoly_eigenvalue_zhukovsky_relation
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : Matrix.det M = 1)
    (h_eigen : (Matrix.charpoly M).eval x = 0) (hx : x ≠ 0) :
    x + x⁻¹ = Tr := by
  have hchar := charPoly_eval_fin_two_zhukovsky M x Tr h_tr h_det
  rw [h_eigen] at hchar
  have hquad : x^2 - Tr * x + 1 = 0 := hchar.symm
  have hmul : x * (x + x⁻¹ - Tr) = 0 := by
    field_simp [hx]
    ring_nf at hquad ⊢
    exact hquad
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hx)

/-- For nonzero `x`, the Mathlib determinant-one root condition is equivalent to the Zhukovsky relation. -/
theorem charPoly_root_iff_zhukovsky_relation
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : Matrix.det M = 1) (hx : x ≠ 0) :
    (Matrix.charpoly M).eval x = 0 ↔ x + x⁻¹ = Tr := by
  constructor
  · intro h_eigen
    exact charPoly_eigenvalue_zhukovsky_relation M x Tr h_tr h_det h_eigen hx
  · intro hrel
    rw [charPoly_eval_fin_two_zhukovsky M x Tr h_tr h_det]
    have hmul : x * (x + x⁻¹ - Tr) = 0 := by
      rw [hrel]
      ring
    field_simp [hx] at hmul
    ring_nf at hmul ⊢
    exact hmul

/-- Nonzero roots of the Mathlib determinant-one characteristic polynomial are closed under spectral inversion. -/
theorem charPoly_inverse_root_of_root
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : Matrix.det M = 1)
    (h_eigen : (Matrix.charpoly M).eval x = 0) (hx : x ≠ 0) :
    (Matrix.charpoly M).eval x⁻¹ = 0 := by
  have hrel : x + x⁻¹ = Tr :=
    charPoly_eigenvalue_zhukovsky_relation M x Tr h_tr h_det h_eigen hx
  exact (charPoly_root_iff_zhukovsky_relation M x⁻¹ Tr h_tr h_det (inv_ne_zero hx)).mpr
    (by simpa [inv_inv, add_comm] using hrel)

/-- A trace-free determinant-one `2×2` complex matrix has eigenvalues satisfying `x^2 = -1`. -/
theorem trace_free_eigenvalue_compact_C
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ)
    (h_tr : Matrix.trace M = 0) (h_det : Matrix.det M = 1)
    (h_eigen : (Matrix.charpoly M).eval x = 0) :
    x^2 = -1 := by
  have hchar : x^2 + 1 = 0 := by
    have h := charPoly_eval_fin_two_zhukovsky (M := M) (x := x) (Tr := 0) h_tr h_det
    rw [h_eigen] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h.symm
  exact eq_neg_of_add_eq_zero_left hchar

/-- Matrix-characteristic-polynomial trace-free determinant-one roots lie on the squared-norm unit circle. -/
theorem trace_free_eigenvalue_normSq_eq_one
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ)
    (h_tr : Matrix.trace M = 0) (h_det : Matrix.det M = 1)
    (h_eigen : (Matrix.charpoly M).eval x = 0) :
    Complex.normSq x = 1 :=
  normSq_eq_one_of_sq_eq_neg_one x
    (trace_free_eigenvalue_compact_C M x h_tr h_det h_eigen)

/-- Matrix-characteristic-polynomial trace-free determinant-one roots are exactly `±I`. -/
theorem trace_free_eigenvalue_eq_I_or_neg_I
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ)
    (h_tr : Matrix.trace M = 0) (h_det : Matrix.det M = 1)
    (h_eigen : (Matrix.charpoly M).eval x = 0) :
    x = Complex.I ∨ x = -Complex.I :=
  (sq_eq_neg_one_iff_eq_I_or_neg_I x).mp
    (trace_free_eigenvalue_compact_C M x h_tr h_det h_eigen)

/-- Matrix-characteristic-polynomial trace-free determinant-one roots have inverse equal to their negative. -/
theorem trace_free_eigenvalue_inv_eq_neg
    (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ)
    (h_tr : Matrix.trace M = 0) (h_det : Matrix.det M = 1)
    (h_eigen : (Matrix.charpoly M).eval x = 0) :
    x⁻¹ = -x := by
  have hsq : x^2 = -1 := trace_free_eigenvalue_compact_C M x h_tr h_det h_eigen
  apply inv_eq_of_mul_eq_one_right
  calc
    x * (-x) = -(x^2) := by ring
    _ = 1 := by rw [hsq]; norm_num

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

/-- Lemma 1: rewrite the left characteristic polynomial using the explicit factorization. -/
theorem charPoly_eq_charPoly_factorization {K ι : Type*}
    [CommRing K] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι K}
    (W : SimilarMatrixWitness A B) :
    charPoly A = charPoly (W.P * B * W.Q) := by
  exact congrArg charPoly W.factorization

/-- Lemma 2: associate the product before applying Sylvester commutation. -/
theorem charPoly_factorization_assoc_left {K ι : Type*}
    [CommRing K] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι K}
    (W : SimilarMatrixWitness A B) :
    charPoly (W.P * B * W.Q) = charPoly (W.P * (B * W.Q)) := by
  rw [Matrix.mul_assoc]

/-- Lemma 3: Sylvester characteristic-polynomial identity `χ_{XY}=χ_{YX}`. -/
theorem charPoly_factorization_swap {K ι : Type*}
    [CommRing K] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι K}
    (W : SimilarMatrixWitness A B) :
    charPoly (W.P * (B * W.Q)) = charPoly ((B * W.Q) * W.P) := by
  exact Matrix.charpoly_mul_comm W.P (B * W.Q)

/-- Lemma 4: reassociate to expose the inverse product `Q * P`. -/
theorem charPoly_factorization_assoc_right {K ι : Type*}
    [CommRing K] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι K}
    (W : SimilarMatrixWitness A B) :
    charPoly ((B * W.Q) * W.P) = charPoly (B * (W.Q * W.P)) := by
  rw [Matrix.mul_assoc]

/-- Lemma 5: use the right-inverse equation to collapse `B * (Q * P)` to `B`. -/
theorem charPoly_factorization_collapse_inverse {K ι : Type*}
    [CommRing K] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι K}
    (W : SimilarMatrixWitness A B) :
    charPoly (B * (W.Q * W.P)) = charPoly B := by
  rw [W.Q_mul_P, Matrix.mul_one]

/-- Theorem: explicit similarity preserves characteristic polynomial. -/
theorem charPoly_eq_of_similarWitness {K ι : Type*}
    [CommRing K] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι K}
    (W : SimilarMatrixWitness A B) :
    charPoly A = charPoly B := by
  calc
    charPoly A = charPoly (W.P * B * W.Q) := charPoly_eq_charPoly_factorization W
    _ = charPoly (W.P * (B * W.Q)) := charPoly_factorization_assoc_left W
    _ = charPoly ((B * W.Q) * W.P) := charPoly_factorization_swap W
    _ = charPoly (B * (W.Q * W.P)) := charPoly_factorization_assoc_right W
    _ = charPoly B := charPoly_factorization_collapse_inverse W

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

/-- Native existence theorem for the factorization packet. -/
theorem exists_factorizationPacket_ofMatrix (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ P : CharPolyFactorizationPacket n,
      P.A = A ∧
      charPoly P.A = P.roots.foldr (fun a p => (X - C a) * p) 1 ∧
      P.roots.length = n := by
  rcases charPoly_factorized_native (n := n) A with ⟨roots, hfactor, hlen⟩
  exact
    ⟨{ A := A
       roots := roots
       factorization := hfactor
       length_eq := hlen },
      rfl, hfactor, hlen⟩

/-- Projection corresponding to AFP `char_poly_factorized`. -/
theorem charPoly_factorized {n : Nat} (P : CharPolyFactorizationPacket n) :
    ∃ roots : List ℂ,
      charPoly P.A = roots.foldr (fun a p => (X - C a) * p) 1 ∧ roots.length = n :=
  ⟨P.roots, P.factorization, P.length_eq⟩

end CharPolyFactorizationPacket

end CharPoly
