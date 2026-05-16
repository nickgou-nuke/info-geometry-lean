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

/-- Native Jordan normal-form predicate implies the transported Jordan matrix similarity readout. -/
theorem jordanNF_charpoly {n : Nat} {A : Matrix (Fin n) (Fin n) ℂ}
    {blocks : List (Nat × ℂ)} (hNF : jordanNF A blocks) :
    ∃ h : matrixSize blocks = n,
      Matrix.charpoly A = jordanMatrixPoly blocks := by
  rcases hNF with ⟨h, hW⟩
  refine ⟨h, ?_⟩
  rcases hW with ⟨W⟩
  calc
    Matrix.charpoly A = Matrix.charpoly (jordanMatrixTransport blocks h) := by
      simpa using
        InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CharPoly.charPoly_similar_of_witness W
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

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanNormalForm
