import Mathlib
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CharPoly
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanBlock
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.SchurDecomposition

/-!
# InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanNormalForm

Lean-native AFP `Jordan_Normal_Form` block layer.

This file packages the block-diagonal Jordan matrix itself, its characteristic
polynomial, and the similarity-based Jordan normal-form predicate used by the
downstream spectral-radius corridor.

The full Jordan-existence theorem is still the higher-level target; this module
closes the native block-matrix and factorization layer first.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanNormalForm

open scoped BigOperators
open Polynomial
open Module.End
open scoped DirectSum
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanBlock

/-- Total size of a Jordan block list. -/
def matrixSize : List (Nat × ℂ) → Nat
  | [] => 0
  | (n, _) :: as => n + matrixSize as

/-- Recursive block-diagonal Jordan matrix built from a list of `(block size, eigenvalue)` pairs. -/
def jordanMatrix : ∀ l : List (Nat × ℂ), Matrix (Fin (matrixSize l)) (Fin (matrixSize l)) ℂ
  | [] => 0
  | (n, a) :: as => by
      exact Matrix.reindex
        (by
          simpa [matrixSize] using (finSumFinEquiv (m := n) (n := matrixSize as)))
        (by
          simpa [matrixSize] using (finSumFinEquiv (m := n) (n := matrixSize as)))
          (Matrix.fromBlocks (InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanBlock.jordanBlock n a)
          0 0 (jordanMatrix as))

/-- AFP-style recursive block decomposition for a Jordan matrix. -/
theorem jordanMatrix_cons (n : Nat) (a : ℂ) (as : List (Nat × ℂ)) :
    jordanMatrix ((n, a) :: as) =
      Matrix.reindex
        (by
          simpa [matrixSize] using (finSumFinEquiv (m := n) (n := matrixSize as)))
        (by
          simpa [matrixSize] using (finSumFinEquiv (m := n) (n := matrixSize as)))
        (Matrix.fromBlocks
          (InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanBlock.jordanBlock n a)
          0 0
          (jordanMatrix as)) := by
  rfl

/-- Transport a Jordan matrix along a proof that the block-list size matches `n`. -/
def jordanMatrixTransport {n : Nat} (blocks : List (Nat × ℂ))
    (h : matrixSize blocks = n) :
    Matrix (Fin n) (Fin n) ℂ := by
  subst h
  exact jordanMatrix blocks

/-- AFP-style Jordan normal-form predicate on a concrete block list. -/
def jordanNF {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ) (blocks : List (Nat × ℂ)) : Prop :=
  ∃ h : matrixSize blocks = n,
    Nonempty (InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CharPoly.SimilarMatrixWitness A
      (jordanMatrixTransport blocks h))

/-- Recursive factorization polynomial for a block-list Jordan matrix. -/
def jordanMatrixPoly : List (Nat × ℂ) → ℂ[X]
  | [] => 1
  | (n, a) :: as => (X - C a) ^ n * jordanMatrixPoly as

/-- Characteristic polynomial of a block-list Jordan matrix. -/
theorem jordanMatrix_charpoly : ∀ blocks : List (Nat × ℂ),
    (jordanMatrix blocks).charpoly = jordanMatrixPoly blocks
  | [] => by
      simp [jordanMatrix, jordanMatrixPoly, matrixSize]
  | (n, a) :: as => by
      calc
        (jordanMatrix ((n, a) :: as)).charpoly =
            (X - C a) ^ n * (jordanMatrix as).charpoly := by
              rw [jordanMatrix]
              rw [Matrix.charpoly_reindex]
              rw [InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.SchurDecomposition.char_poly_fromBlocks_zero₁₂]
              rw [InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanBlock.jordanBlock_charpoly]
        _ = (X - C a) ^ n * jordanMatrixPoly as := by
              rw [jordanMatrix_charpoly as]
        _ = jordanMatrixPoly ((n, a) :: as) := by
              rfl

/-- Characteristic polynomial readout for a transported Jordan matrix. -/
theorem jordanMatrixTransport_charpoly {n : Nat} (blocks : List (Nat × ℂ))
    (h : matrixSize blocks = n) :
    (jordanMatrixTransport blocks h).charpoly = jordanMatrixPoly blocks := by
  subst h
  simpa using jordanMatrix_charpoly (blocks := blocks)

/-- Recursive constructor: the transported Jordan matrix is in Jordan normal form
with respect to its own block list. -/
theorem jordanNF_transport {n : Nat} (blocks : List (Nat × ℂ))
    (h : matrixSize blocks = n) :
    jordanNF (jordanMatrixTransport blocks h) blocks := by
  refine ⟨h, ?_⟩
  exact ⟨InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CharPoly.SimilarMatrixWitness.refl
    (jordanMatrixTransport blocks h)⟩

/-- Native Jordan normal-form predicate implies the transported Jordan matrix similarity readout. -/
theorem jordanNF_charpoly {n : Nat} {A : Matrix (Fin n) (Fin n) ℂ}
    {blocks : List (Nat × ℂ)} (hNF : jordanNF A blocks) :
    ∃ _ : matrixSize blocks = n,
      Matrix.charpoly A = jordanMatrixPoly blocks := by
  rcases hNF with ⟨h, hW⟩
  refine ⟨h, ?_⟩
  rcases hW with ⟨W⟩
  calc
    Matrix.charpoly A = Matrix.charpoly (jordanMatrixTransport blocks h) := by
      simpa using
        InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CharPoly.charPoly_similar_of_sorry W
    _ = jordanMatrixPoly blocks := jordanMatrixTransport_charpoly (blocks := blocks) h

/-- The matrix-endomorphism associated to a square complex matrix on the standard basis. -/
def matrixEnd {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (Fin n → ℂ) :=
  Matrix.toLin (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) A

/-- Native evaluation of `matrixEnd` as matrix multiplication. -/
theorem matrixEnd_apply {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    matrixEnd A v = A.mulVec v := by
  simp [matrixEnd, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

/-- Native matrix-facing generalized-eigenspace span theorem. -/
theorem matrix_iSup_maxGenEigenspace_eq_top {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ) :
    ⨆ μ : ℂ, (matrixEnd A).maxGenEigenspace μ = ⊤ := by
  simpa [matrixEnd] using
    (Module.End.iSup_maxGenEigenspace_eq_top (f := matrixEnd A))

/-- Native matrix-facing formula for the dimension of the maximal generalized eigenspace. -/
theorem matrix_finrank_maxGenEigenspace_eq {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ)
    (μ : ℂ) :
    Module.finrank ℂ ((matrixEnd A).maxGenEigenspace μ) =
      (matrixEnd A).charpoly.rootMultiplicity μ := by
  simpa [matrixEnd] using
    (LinearMap.finrank_maxGenEigenspace_eq (φ := matrixEnd A) μ)

/-- Native matrix-facing identification of the maximal generalized eigenspace with the
finite-step generalized eigenspace at exponent `finrank`. -/
theorem matrix_maxGenEigenspace_eq_genEigenspace_finrank {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    (matrixEnd A).maxGenEigenspace μ = (matrixEnd A).genEigenspace μ
        (Module.finrank ℂ (Fin n → ℂ)) := by
  simpa [matrixEnd] using
    (Module.End.maxGenEigenspace_eq_genEigenspace_finrank (f := matrixEnd A) μ)

/-- Native matrix-facing stabilization of generalized eigenspaces at `finrank`. -/
theorem matrix_genEigenspace_eq_genEigenspace_finrank_of_le {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) {k : ℕ}
    (hk : Module.finrank ℂ (Fin n → ℂ) ≤ k) :
    (matrixEnd A).genEigenspace μ k = (matrixEnd A).genEigenspace μ
        (Module.finrank ℂ (Fin n → ℂ)) := by
  simpa [matrixEnd] using
    (Module.End.genEigenspace_eq_genEigenspace_finrank_of_le (f := matrixEnd A) μ hk)

/-- Native matrix-facing collapse of generalized eigenspaces for finitely semisimple maps. -/
theorem matrix_maxGenEigenspace_eq_eigenspace_of_isFinitelySemisimple {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hss : IsFinitelySemisimple (matrixEnd A)) (μ : ℂ) :
    (matrixEnd A).maxGenEigenspace μ = (matrixEnd A).eigenspace μ := by
  simpa [matrixEnd] using
    (Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (f := matrixEnd A) hss μ)

/-- Native matrix-facing collapse of finite-step generalized eigenspaces to eigenspaces. -/
theorem matrix_genEigenspace_eq_eigenspace_of_isFinitelySemisimple {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hss : IsFinitelySemisimple (matrixEnd A)) (μ : ℂ) {k : ℕ}
    (hk : 0 < k) :
    (matrixEnd A).genEigenspace μ k = (matrixEnd A).eigenspace μ := by
  simpa [matrixEnd] using
    (Module.End.IsFinitelySemisimple.genEigenspace_eq_eigenspace
      (f := matrixEnd A) hss μ (show (0 : ℕ∞) < (k : ℕ∞) from by exact_mod_cast hk))

/-- Native matrix-facing eigenspace spanning theorem for finitely semisimple maps. -/
theorem matrix_iSup_eigenspace_eq_top_of_isFinitelySemisimple {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hss : IsFinitelySemisimple (matrixEnd A)) :
    ⨆ μ : ℂ, (matrixEnd A).eigenspace μ = ⊤ := by
  have hcollapse : ∀ μ : ℂ, (matrixEnd A).maxGenEigenspace μ = (matrixEnd A).eigenspace μ := by
    intro μ
    simpa [matrixEnd] using
      (Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
        (f := matrixEnd A) hss μ)
  simpa [hcollapse] using (matrix_iSup_maxGenEigenspace_eq_top (A := A))

/-- Native matrix-facing upper bound for generalized eigenspace dimension. -/
theorem matrix_finrank_genEigenspace_le {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ)
    (μ : ℂ) (k : ℕ) :
    Module.finrank ℂ ((matrixEnd A).genEigenspace μ k) ≤
      (matrixEnd A).charpoly.rootMultiplicity μ := by
  simpa [matrixEnd] using
    (LinearMap.finrank_genEigenspace_le (φ := matrixEnd A) μ k)

/-- Native matrix-facing upper bound for the eigenspace dimension. -/
theorem matrix_finrank_eigenspace_le {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    Module.finrank ℂ ((matrixEnd A).eigenspace μ) ≤ (matrixEnd A).charpoly.rootMultiplicity μ := by
  simpa [matrixEnd] using
    (LinearMap.finrank_eigenspace_le (φ := matrixEnd A) μ)

/-- Native eigenvalue existence theorem for a nontrivial square complex matrix. -/
theorem matrix_exists_eigenvalue_succ {n : Nat} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ μ : ℂ, (matrixEnd A).HasEigenvalue μ := by
  simpa [matrixEnd] using (Module.End.exists_eigenvalue (f := matrixEnd A))

/-- Native matrix-facing eigenvector extraction from an eigenvalue witness. -/
theorem matrix_exists_eigenvector_of_hasEigenvalue {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : (matrixEnd A).HasEigenvalue μ) :
    ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.mulVec v = μ • v := by
  rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
  have hv' : matrixEnd A v = μ • v ∧ v ≠ 0 := by
    simpa [Module.End.HasEigenvector, Module.End.HasUnifEigenvector] using hv
  exact ⟨v, hv'.2, by simpa [matrixEnd] using hv'.1⟩

/-- Native complex eigenvector existence on a nontrivial square matrix. -/
theorem matrix_exists_eigenvector_succ {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ μ : ℂ, ∃ v : Fin (n + 1) → ℂ, v ≠ 0 ∧ A.mulVec v = μ • v := by
  rcases matrix_exists_eigenvalue_succ (A := A) with ⟨μ, hμ⟩
  rcases matrix_exists_eigenvector_of_hasEigenvalue (A := A) (μ := μ) hμ with ⟨v, hv₀, hv⟩
  exact ⟨μ, v, hv₀, hv⟩

/-- Native matrix-facing nilpotence of `(A - μI)` on the generalized `μ`-eigenspace. -/
theorem matrix_isNilpotent_restrict_genEigenspace_top {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (h :
      Set.MapsTo ⇑(matrixEnd A - μ • 1)
        ↑(((matrixEnd A).genEigenspace μ) ⊤)
        ↑(((matrixEnd A).genEigenspace μ) ⊤)) :
    IsNilpotent (LinearMap.restrict (matrixEnd A - μ • 1) h) := by
  simpa [matrixEnd] using
    (Module.End.isNilpotent_restrict_genEigenspace_top (f := matrixEnd A) μ
      (Module.End.mapsTo_genEigenspace_of_comm
        (Algebra.mul_sub_algebraMap_commutes (matrixEnd A) μ) μ ⊤))

/-- Native matrix-facing generalized-eigenspace restriction theorem. -/
theorem matrix_genEigenspace_restrict_eq_top {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (p : Submodule ℂ (Fin n → ℂ))
    (hp : ∀ x ∈ p, matrixEnd A x ∈ p)
    (h :
      ⨆ μ : ℂ, (matrixEnd A).genEigenspace μ ⊤ = ⊤) :
    ⨆ μ : ℂ, (Module.End.genEigenspace (LinearMap.restrict (matrixEnd A) hp) μ) ⊤ = ⊤ := by
  simpa [matrixEnd] using
    (Module.End.genEigenspace_restrict_eq_top (f := matrixEnd A) (p := p) (k := ⊤) hp h)

/-- Matrix-side generalized-eigenspace restriction theorem using `mulVec` notation. -/
theorem matrix_genEigenspace_restrict_eq_top_mulVec {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (p : Submodule ℂ (Fin n → ℂ))
    (hp : ∀ x ∈ p, A.mulVec x ∈ p)
    (h :
      ⨆ μ : ℂ, (matrixEnd A).genEigenspace μ ⊤ = ⊤) :
    ⨆ μ : ℂ, (Module.End.genEigenspace
        (LinearMap.restrict (matrixEnd A) (by simpa [matrixEnd] using hp)) μ) ⊤ = ⊤ := by
  simpa [matrixEnd] using
    (matrix_genEigenspace_restrict_eq_top (A := A) (p := p)
      (hp := by simpa [matrixEnd] using hp) h)

/-- Native Jordan-Chevalley-Dunford decomposition for a square complex matrix. -/
theorem matrix_exists_isNilpotent_isSemisimple {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ᵉ (N ∈ Algebra.adjoin ℂ {matrixEnd A}) (S ∈ Algebra.adjoin ℂ {matrixEnd A}),
      IsNilpotent N ∧ IsSemisimple S ∧ matrixEnd A = N + S := by
  simpa [matrixEnd] using
    (Module.End.exists_isNilpotent_isSemisimple (f := matrixEnd A))

/-- Native matrix-facing nilpotence on the maximal generalized eigenspace. -/
theorem matrix_isNilpotent_restrict_maxGenEigenspace_sub_algebraMap {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (h :
      Set.MapsTo ⇑(matrixEnd A - (algebraMap ℂ (Module.End ℂ (Fin n → ℂ))) μ)
        ↑((matrixEnd A).maxGenEigenspace μ)
        ↑((matrixEnd A).maxGenEigenspace μ)) :
    IsNilpotent
      (LinearMap.restrict (matrixEnd A - (algebraMap ℂ (Module.End ℂ (Fin n → ℂ))) μ) h) := by
  simpa [matrixEnd] using
    (Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (f := matrixEnd A) μ
      (Module.End.mapsTo_maxGenEigenspace_of_comm
        (Algebra.mul_sub_algebraMap_commutes (matrixEnd A) μ) μ))

/-- PID-route torsion bridge: the matrix action on `AEval'` is torsion over `ℂ[X]`. -/
theorem matrixAEval_isTorsion {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ) :
    Module.IsTorsion ℂ[X] (Module.AEval' (matrixEnd A)) := by
  intro m
  obtain ⟨p, hpmonic, hzero⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℂ (matrixEnd A)
  refine ⟨⟨p, mem_nonZeroDivisors_of_ne_zero hpmonic.ne_zero⟩, ?_⟩
  simpa using congrArg (fun q : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) => q m) hzero

/-- Native PID decomposition object for the `AEval'` matrix module. -/
noncomputable def matrixAEval_pidStructure {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ) :=
  Module.equiv_directSum_of_isTorsion (R := ℂ[X]) (M := Module.AEval' (matrixEnd A))
    (matrixAEval_isTorsion (A := A))

/-- Over `ℂ`, every irreducible polynomial has degree one. -/
theorem complex_irreducible_degree_eq_one {p : ℂ[X]} (hp : Irreducible p) :
    p.degree = 1 := by
  simpa using (IsAlgClosed.degree_eq_one_of_irreducible ℂ hp)

/-- A degree-one complex polynomial is a unit multiple of a linear factor. -/
theorem complex_degree_one_associated_X_sub_C (p : ℂ[X]) (hdeg : p.degree = 1) :
    ∃ a : ℂ, Associated p (X - C a) := by
  have hp0 : p ≠ 0 := by
    intro hp0
    rw [hp0] at hdeg
    simp at hdeg
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  let a : ℂ := -(p.coeff 0) / p.leadingCoeff
  have hEq : p = C p.leadingCoeff * (X - C a) := by
    dsimp [a]
    calc
      p = C p.leadingCoeff * X + C (p.coeff 0) := by
        simpa using (Polynomial.eq_X_add_C_of_degree_eq_one hdeg)
      _ = C p.leadingCoeff * (X + C (p.coeff 0 / p.leadingCoeff)) := by
        calc
          C p.leadingCoeff * X + C (p.coeff 0)
              = C p.leadingCoeff * X + C (p.leadingCoeff * (p.coeff 0 / p.leadingCoeff)) := by
                congr 2
                exact (mul_div_cancel₀ _ hlc).symm
          _ = C p.leadingCoeff * X + C p.leadingCoeff * C (p.coeff 0 / p.leadingCoeff) := by
                simp
          _ = C p.leadingCoeff * (X + C (p.coeff 0 / p.leadingCoeff)) := by
                rw [mul_add]
      _ = C p.leadingCoeff * (X - C a) := by
        congr 1
        ext i
        cases i with
        | zero =>
            simpa [a] using (show p.coeff 0 / p.leadingCoeff = -(-p.coeff 0 / p.leadingCoeff) by
              ring_nf)
        | succ i =>
            simp [a]
  refine ⟨a, ?_⟩
  rw [hEq]
  exact associated_unit_mul_left (X - C a) (C p.leadingCoeff)
    (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hlc))

/-- Over `ℂ`, every irreducible polynomial is associated to a linear factor. -/
theorem complex_irreducible_associated_X_sub_C {p : ℂ[X]} (hp : Irreducible p) :
    ∃ a : ℂ, Associated p (X - C a) := by
  exact complex_degree_one_associated_X_sub_C p (complex_irreducible_degree_eq_one hp)

/-- Powers of complex irreducibles are associated to powers of linear factors. -/
theorem complex_irreducible_pow_associated_X_sub_C {p : ℂ[X]} (hp : Irreducible p) (e : ℕ) :
    ∃ a : ℂ, Associated (p ^ e) ((X - C a) ^ e) := by
  rcases complex_irreducible_associated_X_sub_C (p := p) hp with ⟨a, ha⟩
  exact ⟨a, ha.pow_pow⟩

/-- Over `ℂ`, every irreducible principal ideal is the ideal of a linear factor. -/
theorem complex_irreducible_span_eq_span_X_sub_C {p : ℂ[X]} (hp : Irreducible p) :
    ∃ a : ℂ, Ideal.span ({p} : Set ℂ[X]) = Ideal.span ({X - C a} : Set ℂ[X]) := by
  rcases complex_irreducible_associated_X_sub_C (p := p) hp with ⟨a, hassoc⟩
  exact ⟨a, Ideal.span_singleton_eq_span_singleton.mpr hassoc⟩

/-- Normalize the PID decomposition of `AEval'` to linear factors over `ℂ`. -/
theorem matrixAEval_pidStructure_linearFactors {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℂ) (e : ι → ℕ) (I : ι → Submodule ℂ[X] ℂ[X]),
      ((∀ i, I i = Ideal.span ({(X - C (a i)) ^ e i} : Set ℂ[X])) ∧
        (Nonempty <|
          Module.AEval' (matrixEnd A) ≃ₗ[ℂ[X]]
            ⨁ i : ι, (ℂ[X] ⧸ I i))) := by
  classical
  obtain ⟨ι, fι, p, hp, e, ⟨e0⟩⟩ :=
    Module.equiv_directSum_of_isTorsion (R := ℂ[X]) (M := Module.AEval' (matrixEnd A))
      (matrixAEval_isTorsion (A := A))
  let a : ι → ℂ := fun i => Classical.choose (complex_irreducible_pow_associated_X_sub_C (p := p i)
    (hp i) (e i))
  let I0 : ι → Submodule ℂ[X] ℂ[X] := fun i =>
    Ideal.span ({p i ^ e i} : Set ℂ[X])
  let J0 : ι → Submodule ℂ[X] ℂ[X] := fun i =>
    Ideal.span ({(X - C (a i)) ^ e i} : Set ℂ[X])
  have ha : ∀ i, Associated (p i ^ e i) ((X - C (a i)) ^ e i) := by
    intro i
    dsimp [a]
    exact Classical.choose_spec (complex_irreducible_pow_associated_X_sub_C (p := p i)
      (hp i) (e i))
  have hIJ : ∀ i, I0 i = J0 i := by
    intro i
    dsimp [I0, J0]
    exact Ideal.span_singleton_eq_span_singleton.mpr (ha i)
  let I : ι → Submodule ℂ[X] ℂ[X] := I0
  refine ⟨ι, fι, a, e, I, ?_, ?_⟩
  · intro i
    dsimp [I, I0, J0]
    exact hIJ i
  · refine ⟨?_⟩
    simpa [I, I0, J0, hIJ] using e0

/-- The quotient by an ideal is cyclic, generated by the class of `1`. -/
theorem quotient_span_top {I : Ideal ℂ[X]} :
    Submodule.span ℂ[X] {Ideal.Quotient.mk I (1 : ℂ[X])} = ⊤ := by
  simpa using (Ideal.Quotient.span_singleton_one (I := I))

/--
Native module-cyclic reconstruction of the normalized PID decomposition.

The torsion decomposition of `AEval'` is a direct sum of cyclic quotients,
each generated by the class of `1`; the ideals are then normalized to linear
factors over `ℂ`.
-/
theorem matrixAEval_pidStructure_cyclicLinearFactors {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℂ) (e : ι → ℕ) (I : ι → Submodule ℂ[X] ℂ[X]),
      ((∀ i, I i = Ideal.span ({(X - C (a i)) ^ e i} : Set ℂ[X])) ∧
        (∀ i, Submodule.span ℂ[X] {Ideal.Quotient.mk (I i) (1 : ℂ[X])} = ⊤) ∧
        (Nonempty <|
          Module.AEval' (matrixEnd A) ≃ₗ[ℂ[X]]
            ⨁ i : ι, (ℂ[X] ⧸ I i))) := by
  rcases matrixAEval_pidStructure_linearFactors (A := A) with
    ⟨ι, fι, a, e, I, hI, hEquiv⟩
  refine ⟨ι, fι, a, e, I, ?_⟩
  refine ⟨hI, ?_, hEquiv⟩
  intro i
  simpa using (quotient_span_top (I := I i))

/-- A cyclic factor `AdjoinRoot (X^(n+1))` has a Jordan block basis after shifting
 the generator by `a`. -/
theorem adjoinRoot_shifted_powerBasis_exists_jordanBlock {n : Nat} (a : ℂ) :
    ∃ (pb : PowerBasis ℂ (AdjoinRoot ((X ^ (n + 1) : ℂ[X])))),
      Matrix.reindex Fin.revPerm Fin.revPerm
        (Algebra.leftMulMatrix pb.basis (pb.gen + algebraMap ℂ _ a)) =
        InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanBlock.jordanBlock
          (R := ℂ) pb.dim a := by
  refine ⟨AdjoinRoot.powerBasis' (Polynomial.monic_X_pow (R := ℂ) (n + 1)), ?_⟩
  simpa using
    (adjoinRoot_powerBasis_rev_leftMulMatrix_add_scalar_eq_jordanBlock
      (K := ℂ) (n := n) (a := a))


end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanNormalForm
