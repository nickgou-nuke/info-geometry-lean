import InfoGeometry.Categorical.FibonacciGlobalChannelBasis
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.FibonacciGlobalAssociator

noncomputable section

namespace InfoGeometry.Categorical.FibonacciOrdinaryChannelBasis

open InfoGeometry.Categorical.FibonacciGlobalChannelBasis
open InfoGeometry.Categorical.FibonacciGlobalAssociator
open InfoGeometry.Categorical.FibonacciHomSpace

theorem leftTauSemanticPathEquivRight_symm_f_output_one
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (i : Fin (TauTripleMultiplicity X Y Z)) :
    (leftTauSemanticPathEquivRight X Y Z).symm
        (rightTauFOutputOne X Y Z i) =
      leftTauFInputOne X Y Z i := by
  exact rightTauSemanticPathMap_f_output_one X Y Z i

theorem leftTauSemanticPathEquivRight_symm_f_output_two
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (i : Fin (TauTripleMultiplicity X Y Z)) :
    (leftTauSemanticPathEquivRight X Y Z).symm
        (rightTauFOutputTwo X Y Z i) =
      leftTauFInputTwo X Y Z i := by
  exact rightTauSemanticPathMap_f_output_two X Y Z i

theorem semanticReindex_f_output_one_one
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (M : Matrix
      (LeftTauFusionPathIndex X Y Z)
      (LeftTauFusionPathIndex X Y Z) ℂ)
    (i j : Fin (TauTripleMultiplicity X Y Z)) :
    Matrix.reindex (leftTauSemanticPathEquivRight X Y Z)
        (leftTauSemanticPathEquivRight X Y Z) M
        (rightTauFOutputOne X Y Z i) (rightTauFOutputOne X Y Z j) =
      M (leftTauFInputOne X Y Z i) (leftTauFInputOne X Y Z j) := by
  simp [Matrix.reindex,
    leftTauSemanticPathEquivRight_symm_f_output_one]

theorem semanticReindex_f_output_one_two
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (M : Matrix
      (LeftTauFusionPathIndex X Y Z)
      (LeftTauFusionPathIndex X Y Z) ℂ)
    (i j : Fin (TauTripleMultiplicity X Y Z)) :
    Matrix.reindex (leftTauSemanticPathEquivRight X Y Z)
        (leftTauSemanticPathEquivRight X Y Z) M
        (rightTauFOutputOne X Y Z i) (rightTauFOutputTwo X Y Z j) =
      M (leftTauFInputOne X Y Z i) (leftTauFInputTwo X Y Z j) := by
  simp [Matrix.reindex,
    leftTauSemanticPathEquivRight_symm_f_output_one,
    leftTauSemanticPathEquivRight_symm_f_output_two]

theorem semanticReindex_f_output_two_one
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (M : Matrix
      (LeftTauFusionPathIndex X Y Z)
      (LeftTauFusionPathIndex X Y Z) ℂ)
    (i j : Fin (TauTripleMultiplicity X Y Z)) :
    Matrix.reindex (leftTauSemanticPathEquivRight X Y Z)
        (leftTauSemanticPathEquivRight X Y Z) M
        (rightTauFOutputTwo X Y Z i) (rightTauFOutputOne X Y Z j) =
      M (leftTauFInputTwo X Y Z i) (leftTauFInputOne X Y Z j) := by
  simp [Matrix.reindex,
    leftTauSemanticPathEquivRight_symm_f_output_one,
    leftTauSemanticPathEquivRight_symm_f_output_two]

theorem semanticReindex_f_output_two_two
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (M : Matrix
      (LeftTauFusionPathIndex X Y Z)
      (LeftTauFusionPathIndex X Y Z) ℂ)
    (i j : Fin (TauTripleMultiplicity X Y Z)) :
    Matrix.reindex (leftTauSemanticPathEquivRight X Y Z)
        (leftTauSemanticPathEquivRight X Y Z) M
        (rightTauFOutputTwo X Y Z i) (rightTauFOutputTwo X Y Z j) =
      M (leftTauFInputTwo X Y Z i) (leftTauFInputTwo X Y Z j) := by
  simp [Matrix.reindex,
    leftTauSemanticPathEquivRight_symm_f_output_two]

noncomputable def semanticSquareTransport
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    (M : Matrix (LeftTauFusionPathIndex X Y Z)
      (RightTauFusionPathIndex X Y Z) ℂ) :
    Matrix (RightTauFusionPathIndex X Y Z)
      (RightTauFusionPathIndex X Y Z) ℂ :=
  Matrix.reindex (leftTauSemanticPathEquivRight X Y Z)
    (leftTauSemanticPathEquivRight X Y Z)
    (Matrix.submatrix M id (leftTauSemanticPathEquivRight X Y Z))

theorem semanticSquareTransport_apply
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    (M : Matrix (LeftTauFusionPathIndex X Y Z)
      (RightTauFusionPathIndex X Y Z) ℂ)
    (a b : RightTauFusionPathIndex X Y Z) :
    semanticSquareTransport X Y Z M a b =
      M ((leftTauSemanticPathEquivRight X Y Z).symm a) b := by
  simp [semanticSquareTransport, Matrix.reindex, Matrix.submatrix]

theorem semanticSquareTransport_f_block
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    Matrix.submatrix (semanticSquareTransport X Y Z
      (tauFusionPathMatrix X Y Z τ s))
        (rightTauFBlockOutput X Y Z)
        (rightTauFBlockOutput X Y Z) =
      Matrix.submatrix (tauFusionPathMatrix X Y Z τ s)
        (leftTauFBlockInput X Y Z)
        (rightTauFBlockOutput X Y Z) := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp [Matrix.submatrix, semanticSquareTransport_apply,
            semanticSquareTransport,
            leftTauFBlockInput, rightTauFBlockOutput,
            leftTauSemanticPathEquivRight_symm_f_output_one]
      | inr j =>
          simp [Matrix.submatrix, semanticSquareTransport_apply,
            semanticSquareTransport,
            leftTauFBlockInput, rightTauFBlockOutput,
            leftTauSemanticPathEquivRight_symm_f_output_one,
            leftTauSemanticPathEquivRight_symm_f_output_two]
  | inr i =>
      cases j with
      | inl j =>
          simp [Matrix.submatrix, semanticSquareTransport_apply,
            semanticSquareTransport,
            leftTauFBlockInput, rightTauFBlockOutput,
            leftTauSemanticPathEquivRight_symm_f_output_one,
            leftTauSemanticPathEquivRight_symm_f_output_two]
      | inr j =>
          simp [Matrix.submatrix, semanticSquareTransport_apply,
            semanticSquareTransport,
            leftTauFBlockInput, rightTauFBlockOutput,
            leftTauSemanticPathEquivRight_symm_f_output_two]

theorem semanticSquareTransport_f_block_transpose_mul
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    Matrix.transpose (Matrix.submatrix
      (semanticSquareTransport X Y Z
        (tauFusionPathMatrix X Y Z τ s))
      (rightTauFBlockOutput X Y Z)
      (rightTauFBlockOutput X Y Z)) *
      Matrix.submatrix
        (semanticSquareTransport X Y Z
          (tauFusionPathMatrix X Y Z τ s))
        (rightTauFBlockOutput X Y Z)
        (rightTauFBlockOutput X Y Z) =
      (1 : Matrix
        (Sum (Fin (TauTripleMultiplicity X Y Z))
          (Fin (TauTripleMultiplicity X Y Z)))
        (Sum (Fin (TauTripleMultiplicity X Y Z))
          (Fin (TauTripleMultiplicity X Y Z))) ℂ) := by
  rw [semanticSquareTransport_f_block]
  exact tauFusionPathMatrix_f_block_transpose_mul X Y Z τ s hs hτ

theorem semanticSquareTransport_f_block_mul_transpose
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    Matrix.submatrix
        (semanticSquareTransport X Y Z
          (tauFusionPathMatrix X Y Z τ s))
        (rightTauFBlockOutput X Y Z)
        (rightTauFBlockOutput X Y Z) *
      Matrix.transpose (Matrix.submatrix
        (semanticSquareTransport X Y Z
          (tauFusionPathMatrix X Y Z τ s))
        (rightTauFBlockOutput X Y Z)
        (rightTauFBlockOutput X Y Z)) =
      (1 : Matrix
        (Sum (Fin (TauTripleMultiplicity X Y Z))
          (Fin (TauTripleMultiplicity X Y Z)))
        (Sum (Fin (TauTripleMultiplicity X Y Z))
          (Fin (TauTripleMultiplicity X Y Z))) ℂ) := by
  rw [semanticSquareTransport_f_block]
  rw [tauFusionPathMatrix_f_block_eq]
  rw [FibonacciGlobalAssociator.tauTripleFMatrix_transpose]
  exact FibonacciGlobalChannelBasis.tauTripleFMatrix_sq
    (TauTripleMultiplicity X Y Z) τ s hs hτ

def leftTauOrdinaryPath (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
  {i : LeftTauFusionPathIndex X Y Z //
    (∀ k, i ≠ leftTauFInputOne X Y Z k) ∧
    (∀ k, i ≠ leftTauFInputTwo X Y Z k)}

def rightTauOrdinaryPath (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) : Type :=
  {j : RightTauFusionPathIndex X Y Z //
    (∀ k, j ≠ rightTauFOutputOne X Y Z k) ∧
    (∀ k, j ≠ rightTauFOutputTwo X Y Z k)}

instance leftTauOrdinaryPathFinite (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Finite (leftTauOrdinaryPath X Y Z) :=
  Finite.of_injective Subtype.val Subtype.val_injective

instance rightTauOrdinaryPathFinite (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Finite (rightTauOrdinaryPath X Y Z) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance leftTauOrdinaryPathFintype (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Fintype (leftTauOrdinaryPath X Y Z) := Fintype.ofFinite _

noncomputable instance rightTauOrdinaryPathFintype (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    Fintype (rightTauOrdinaryPath X Y Z) := Fintype.ofFinite _

noncomputable def leftTauOrdinaryPathEquivRight
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) :
    leftTauOrdinaryPath X Y Z ≃ rightTauOrdinaryPath X Y Z :=
  { toFun := fun i =>
      ⟨leftTauSemanticPathMap X Y Z i.1, by
        constructor
        · intro k h
          exact i.2.1 k ((leftTauSemanticPathMap_eq_f_output_one_iff
            X Y Z i.1 k).1 h)
        · intro k h
          exact i.2.2 k ((leftTauSemanticPathMap_eq_f_output_two_iff
            X Y Z i.1 k).1 h)⟩
    invFun := fun j =>
      ⟨rightTauSemanticPathMap X Y Z j.1, by
        constructor
        · intro k h
          apply j.2.1 k
          calc
            j.1 = leftTauSemanticPathMap X Y Z
                (rightTauSemanticPathMap X Y Z j.1) := by
              exact (leftTauSemanticPathEquivRight X Y Z).right_inv j.1 |>.symm
            _ = leftTauSemanticPathMap X Y Z
                (leftTauFInputOne X Y Z k) := congrArg
              (leftTauSemanticPathMap X Y Z) h
            _ = rightTauFOutputOne X Y Z k := by rfl
        · intro k h
          apply j.2.2 k
          calc
            j.1 = leftTauSemanticPathMap X Y Z
                (rightTauSemanticPathMap X Y Z j.1) := by
              exact (leftTauSemanticPathEquivRight X Y Z).right_inv j.1 |>.symm
            _ = leftTauSemanticPathMap X Y Z
                (leftTauFInputTwo X Y Z k) := congrArg
              (leftTauSemanticPathMap X Y Z) h
            _ = rightTauFOutputTwo X Y Z k := by rfl⟩
    left_inv := by
      intro i
      apply Subtype.ext
      exact (leftTauSemanticPathEquivRight X Y Z).left_inv i.1
    right_inv := by
      intro j
      apply Subtype.ext
      exact (leftTauSemanticPathEquivRight X Y Z).right_inv j.1 }

theorem tauFusionPathEntry_ordinary_eq_one
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (i : leftTauOrdinaryPath X Y Z)
    (j : rightTauOrdinaryPath X Y Z)
    (h : leftTauSemanticPathMap X Y Z i.1 = j.1) :
    tauFusionPathEntry X Y Z τ s i.1 j.1 = 1 := by
  classical
  rw [← h]
  rcases i with ⟨i, hi⟩
  rcases i with i | i
  · simp [tauFusionPathEntry, leftTauSemanticPathMap]
  · rcases i with i | i
    · exact (hi.1 i rfl).elim
    · rcases i with i | i
      · simp [tauFusionPathEntry, leftTauSemanticPathMap]
      · rcases i with i | i
        · simp [tauFusionPathEntry, leftTauSemanticPathMap]
        · rcases i with i | i
          · simp [tauFusionPathEntry, leftTauSemanticPathMap]
          · rcases i with i | i
            · simp [tauFusionPathEntry, leftTauSemanticPathMap]
            · rcases i with i | i
              · simp only [tauFusionPathEntry]
                simp [leftTauSemanticPathMap]
              · exact (hi.2 i rfl).elim

theorem tauFusionPathEntry_ordinary_eq_zero
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ)
    (i : leftTauOrdinaryPath X Y Z)
    (j : rightTauOrdinaryPath X Y Z)
    (h : leftTauSemanticPathMap X Y Z i.1 ≠ j.1) :
    tauFusionPathEntry X Y Z τ s i.1 j.1 = 0 := by
  classical
  rcases i with ⟨i, hi⟩
  rcases i with i | i
  · have hj : j.1 ≠ Sum.inl i := by
      intro e
      apply h
      simpa [leftTauSemanticPathMap] using e.symm
    simp [tauFusionPathEntry, leftTauSemanticPathMap, hj]
  · rcases i with i | i
    · simp [tauFusionPathEntry, j.2.1 i, j.2.2 i,
        Ne.symm (j.2.1 i), Ne.symm (j.2.2 i)]
    · rcases i with i | i
      · have hj : j.1 ≠ Sum.inr (Sum.inl i) := by
          intro e
          apply h
          simpa [leftTauSemanticPathMap] using e.symm
        simp [tauFusionPathEntry, leftTauSemanticPathMap, hj]
      · rcases i with i | i
        · have hj : j.1 ≠ Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) := by
            intro e
            apply h
            simpa [leftTauSemanticPathMap] using e.symm
          simp [tauFusionPathEntry, leftTauSemanticPathMap, hj]
        · rcases i with i | i
          · have hj : j.1 ≠ Sum.inr (Sum.inr (Sum.inr (Sum.inr
                (Sum.inr (Sum.inr (Sum.inl i)))))) := by
              intro e
              apply h
              simpa [leftTauSemanticPathMap] using e.symm
            simp [tauFusionPathEntry, leftTauSemanticPathMap, hj]
          · rcases i with i | i
            · have hj : j.1 ≠ Sum.inr (Sum.inr (Sum.inl i)) := by
                intro e
                apply h
                simpa [leftTauSemanticPathMap] using e.symm
              simp [tauFusionPathEntry, leftTauSemanticPathMap, hj]
            · rcases i with i | i
              · have hj : j.1 ≠ Sum.inr (Sum.inr (Sum.inr (Sum.inr
                    (Sum.inr (Sum.inl i))))) := by
                  intro e
                  apply h
                  simpa [leftTauSemanticPathMap] using e.symm
                simp only [tauFusionPathEntry]
                simp [leftTauSemanticPathMap, hj]
              · simp [tauFusionPathEntry, j.2.1 i, j.2.2 i,
                  Ne.symm (j.2.1 i), Ne.symm (j.2.2 i)]

noncomputable def tauFusionPathOrdinaryMatrix
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    Matrix (leftTauOrdinaryPath X Y Z)
      (rightTauOrdinaryPath X Y Z) ℂ :=
  Matrix.submatrix (tauFusionPathMatrix X Y Z τ s)
    Subtype.val Subtype.val

noncomputable def tauFusionPathOrdinaryPermutation
    {α β : Type*} (e : α ≃ β) : Matrix α β ℂ := by
  classical
  exact fun i j => if e i = j then 1 else 0

theorem tauFusionPathOrdinaryMatrix_eq_permutation
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat) (τ s : ℂ) :
    tauFusionPathOrdinaryMatrix X Y Z τ s =
      tauFusionPathOrdinaryPermutation
        (leftTauOrdinaryPathEquivRight X Y Z) := by
  classical
  ext i j
  change tauFusionPathEntry X Y Z τ s i.1 j.1 = _
  by_cases h : leftTauSemanticPathMap X Y Z i.1 = j.1
  · rw [tauFusionPathEntry_ordinary_eq_one X Y Z τ s i j h]
    simp [tauFusionPathOrdinaryPermutation,
      leftTauOrdinaryPathEquivRight, h]
  · rw [tauFusionPathEntry_ordinary_eq_zero X Y Z τ s i j h]
    have he : leftTauOrdinaryPathEquivRight X Y Z i = j ↔
        leftTauSemanticPathMap X Y Z i.1 = j.1 := by
      constructor
      · intro e
        exact congrArg Subtype.val e
      · intro e
        apply Subtype.ext
        exact e
    simp [tauFusionPathOrdinaryPermutation, he, h]

theorem tauFusionPathOrdinaryMatrix_mul_transpose
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    [DecidableEq (leftTauOrdinaryPath X Y Z)]
    [DecidableEq (rightTauOrdinaryPath X Y Z)]
    (τ s : ℂ) :
    tauFusionPathOrdinaryMatrix X Y Z τ s *
        Matrix.transpose (tauFusionPathOrdinaryMatrix X Y Z τ s) =
      (1 : Matrix (leftTauOrdinaryPath X Y Z)
        (leftTauOrdinaryPath X Y Z) ℂ) := by
  rw [tauFusionPathOrdinaryMatrix_eq_permutation]
  exact FibonacciGlobalAssociator.equivPermutationMatrix_mul_transpose
    (leftTauOrdinaryPathEquivRight X Y Z)

theorem tauFusionPathOrdinaryMatrix_transpose_mul
    (X Y Z : InfoGeometry.Categorical.FibonacciHomSpace.FibCat)
    [DecidableEq (leftTauOrdinaryPath X Y Z)]
    [DecidableEq (rightTauOrdinaryPath X Y Z)]
    (τ s : ℂ) :
    Matrix.transpose (tauFusionPathOrdinaryMatrix X Y Z τ s) *
        tauFusionPathOrdinaryMatrix X Y Z τ s =
      (1 : Matrix (rightTauOrdinaryPath X Y Z)
        (rightTauOrdinaryPath X Y Z) ℂ) := by
  rw [tauFusionPathOrdinaryMatrix_eq_permutation]
  exact FibonacciGlobalAssociator.equivPermutationMatrix_transpose_mul
    (leftTauOrdinaryPathEquivRight X Y Z)

end InfoGeometry.Categorical.FibonacciOrdinaryChannelBasis
