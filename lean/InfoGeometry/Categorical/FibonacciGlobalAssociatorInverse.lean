import InfoGeometry.Categorical.FibonacciGlobalAssociator
import Mathlib.Data.Matrix.Diagonal

set_option maxHeartbeats 32000000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Categorical.FibonacciGlobalAssociator

open CategoryTheory
open InfoGeometry.Categorical.FibonacciGlobalChannelBasis
open InfoGeometry.Categorical.FibonacciBraidedCategory
open InfoGeometry.Categorical.FibonacciHomSpace
open scoped Classical

lemma ite_ite_of_ne {α R : Type*} [AddZeroClass R] [DecidableEq α]
    {j A B : α} (hAB : A ≠ B) (x y : R) :
    (if j = A then x else if j = B then y else 0) =
      (if j = A then x else 0) + (if j = B then y else 0) := by
  by_cases hA : j = A
  · subst hA
    have : ¬ (j = B) := hAB
    simp [this]
  · by_cases hB : j = B
    · subst hB
      simp [hA]
    · simp [hA, hB]

theorem tauFusionPathMatrix_mul_transpose (first second third : FibCat)
    (tau scale : ℂ) (scale_sq : scale ^ 2 = tau) (tau_sq : tau ^ 2 + tau = 1) :
    tauFusionPathMatrix first second third tau scale *
        (tauFusionPathMatrix first second third tau scale).transpose = 1 := by
  ext row col
  rcases row with r | ⟨r | ⟨r | ⟨r | ⟨r | ⟨r | ⟨r | r⟩⟩⟩⟩⟩⟩
  -- Case 1 (ordinary)
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (leftTauSemanticPathMap first second third (Sum.inl r))]
    · rw [Matrix.transpose_apply]
      dsimp only [tauFusionPathMatrix, tauFusionPathEntry]
      rcases col with col | col | col | col | col | col | col | col <;>
        simp [leftTauSemanticPathMap, Matrix.one_apply, rightTauFOutputOne, rightTauFOutputTwo]
    · intro j _ hj
      rw [Matrix.transpose_apply]
      dsimp only [tauFusionPathMatrix, tauFusionPathEntry]
      simp [hj]
    · simp
  -- Case 2 (F-input-one)
  · rw [Matrix.mul_apply]
    have hne := rightTauFOutputOne_ne_two first second third r r
    have hsplit : ∀ j, tauFusionPathMatrix first second third tau scale (Sum.inr (Sum.inl r)) j =
        (if j = rightTauFOutputOne first second third r then tau else 0) +
        (if j = rightTauFOutputTwo first second third r then scale else 0) := fun j => by
      dsimp [tauFusionPathMatrix, tauFusionPathEntry]
      exact ite_ite_of_ne hne tau scale
    simp_rw [hsplit, add_mul, Finset.sum_add_distrib]
    simp_rw [Matrix.transpose_apply, ite_mul, zero_mul]
    simp_rw [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have diagonal : tau * tau + scale * scale = 1 := by
      calc
        tau * tau + scale * scale = tau ^ 2 + scale ^ 2 := by ring
        _ = 1 := by rw [scale_sq]; exact tau_sq
    dsimp [tauFusionPathMatrix, tauFusionPathEntry]
    rcases col with col | col | col | col | col | col | col | col
    · simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply]
    · by_cases h : col = r
      · subst h
        simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply, diagonal]
      · have h1 : rightTauFOutputOne first second third r ≠ rightTauFOutputOne first second third col := by
          intro e; exact h (rightTauFOutputOne_injective first second third e).symm
        have h2 : rightTauFOutputTwo first second third r ≠ rightTauFOutputTwo first second third col := by
          intro e; exact h (rightTauFOutputTwo_injective first second third e).symm
        have h12 : rightTauFOutputOne first second third r ≠ rightTauFOutputTwo first second third col :=
          rightTauFOutputOne_ne_two first second third r col
        have h21 : rightTauFOutputTwo first second third r ≠ rightTauFOutputOne first second third col :=
          Ne.symm (rightTauFOutputOne_ne_two first second third col r)
        simp [rightTauFOutputOne, rightTauFOutputTwo, Matrix.one_apply, h, Ne.symm h,
          h1, Ne.symm h1, h2, Ne.symm h2, h12, Ne.symm h12, h21, Ne.symm h21]
    · simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply]
    · simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply]
    · simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply]
    · simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply]
    · simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply]
    · by_cases h : col = r
      · subst h
        have h12 : rightTauFOutputOne first second third col ≠ rightTauFOutputTwo first second third col :=
          rightTauFOutputOne_ne_two first second third col col
        simp [rightTauFOutputOne, rightTauFOutputTwo, Matrix.one_apply, h12, Ne.symm h12]
        ring
      · have h1 : rightTauFOutputOne first second third r ≠ rightTauFOutputOne first second third col := by
          intro e; exact h (rightTauFOutputOne_injective first second third e).symm
        have h2 : rightTauFOutputTwo first second third r ≠ rightTauFOutputTwo first second third col := by
          intro e; exact h (rightTauFOutputTwo_injective first second third e).symm
        have h12 : rightTauFOutputOne first second third r ≠ rightTauFOutputTwo first second third col :=
          rightTauFOutputOne_ne_two first second third r col
        have h21 : rightTauFOutputTwo first second third r ≠ rightTauFOutputOne first second third col :=
          Ne.symm (rightTauFOutputOne_ne_two first second third col r)
        simp [rightTauFOutputOne, rightTauFOutputTwo, Matrix.one_apply, h, Ne.symm h,
          h1, Ne.symm h1, h2, Ne.symm h2, h12, Ne.symm h12, h21, Ne.symm h21]
  -- Case 3 (ordinary)
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (leftTauSemanticPathMap first second third (Sum.inr (Sum.inr (Sum.inl r))))]
    · rw [Matrix.transpose_apply]
      dsimp only [tauFusionPathMatrix, tauFusionPathEntry]
      rcases col with col | col | col | col | col | col | col | col <;>
        simp [leftTauSemanticPathMap, Matrix.one_apply, rightTauFOutputOne, rightTauFOutputTwo]
    · intro j _ hj
      rw [Matrix.transpose_apply]
      dsimp only [tauFusionPathMatrix, tauFusionPathEntry]
      simp [hj]
    · simp
  -- Case 4 (ordinary)
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (leftTauSemanticPathMap first second third (Sum.inr (Sum.inr (Sum.inr (Sum.inl r)))))]
    · rw [Matrix.transpose_apply]
      dsimp only [tauFusionPathMatrix, tauFusionPathEntry]
      rcases col with col | col | col | col | col | col | col | col <;>
        simp [leftTauSemanticPathMap, Matrix.one_apply, rightTauFOutputOne, rightTauFOutputTwo]
    · intro j _ hj
      rw [Matrix.transpose_apply]
      dsimp only [tauFusionPathMatrix, tauFusionPathEntry]
      simp [hj]
    · simp
  -- Case 5 (ordinary)
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (leftTauSemanticPathMap first second third (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl r))))))]
    · rw [Matrix.transpose_apply]
      dsimp only [tauFusionPathMatrix, tauFusionPathEntry]
      rcases col with col | col | col | col | col | col | col | col <;>
        simp [leftTauSemanticPathMap, Matrix.one_apply, rightTauFOutputOne, rightTauFOutputTwo]
    · intro j _ hj
      rw [Matrix.transpose_apply]
      dsimp only [tauFusionPathMatrix, tauFusionPathEntry]
      simp [hj]
    · simp
  -- Case 6 (ordinary)
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (leftTauSemanticPathMap first second third (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl r)))))))]
    · rw [Matrix.transpose_apply]
      dsimp only [tauFusionPathMatrix, tauFusionPathEntry]
      rcases col with col | col | col | col | col | col | col | col <;>
        simp [leftTauSemanticPathMap, Matrix.one_apply, rightTauFOutputOne, rightTauFOutputTwo]
    · intro j _ hj
      rw [Matrix.transpose_apply]
      dsimp only [tauFusionPathMatrix, tauFusionPathEntry]
      simp [hj]
    · simp
  -- Case 7 (ordinary)
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (leftTauSemanticPathMap first second third (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl r))))))))]
    · rw [Matrix.transpose_apply]
      dsimp only [tauFusionPathMatrix, tauFusionPathEntry]
      rcases col with col | col | col | col | col | col | col | col <;>
        simp [leftTauSemanticPathMap, Matrix.one_apply, rightTauFOutputOne, rightTauFOutputTwo]
    · intro j _ hj
      rw [Matrix.transpose_apply]
      dsimp only [tauFusionPathMatrix, tauFusionPathEntry]
      simp [hj]
    · simp
  -- Case 8 (F-input-two)
  · rw [Matrix.mul_apply]
    have hne := rightTauFOutputOne_ne_two first second third r r
    have hsplit : ∀ j, tauFusionPathMatrix first second third tau scale
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr r))))))) j =
        (if j = rightTauFOutputOne first second third r then scale else 0) +
        (if j = rightTauFOutputTwo first second third r then -tau else 0) := fun j => by
      dsimp [tauFusionPathMatrix, tauFusionPathEntry]
      exact ite_ite_of_ne hne scale (-tau)
    simp_rw [hsplit, add_mul, Finset.sum_add_distrib]
    simp_rw [Matrix.transpose_apply, ite_mul, zero_mul]
    simp_rw [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have diagonal : scale * scale + tau * tau = 1 := by
      calc
        scale * scale + tau * tau = tau ^ 2 + scale ^ 2 := by ring
        _ = 1 := by rw [scale_sq]; exact tau_sq
    dsimp [tauFusionPathMatrix, tauFusionPathEntry]
    rcases col with col | col | col | col | col | col | col | col
    · simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply]
    · by_cases h : col = r
      · subst h
        have h12 : rightTauFOutputOne first second third col ≠ rightTauFOutputTwo first second third col :=
          rightTauFOutputOne_ne_two first second third col col
        simp [rightTauFOutputOne, rightTauFOutputTwo, Matrix.one_apply, h12, Ne.symm h12]
        ring
      · have h1 : rightTauFOutputOne first second third r ≠ rightTauFOutputOne first second third col := by
          intro e; exact h (rightTauFOutputOne_injective first second third e).symm
        have h2 : rightTauFOutputTwo first second third r ≠ rightTauFOutputTwo first second third col := by
          intro e; exact h (rightTauFOutputTwo_injective first second third e).symm
        have h12 : rightTauFOutputOne first second third r ≠ rightTauFOutputTwo first second third col :=
          rightTauFOutputOne_ne_two first second third r col
        have h21 : rightTauFOutputTwo first second third r ≠ rightTauFOutputOne first second third col :=
          Ne.symm (rightTauFOutputOne_ne_two first second third col r)
        simp [rightTauFOutputOne, rightTauFOutputTwo, Matrix.one_apply, h, Ne.symm h,
          h1, Ne.symm h1, h2, Ne.symm h2, h12, Ne.symm h12, h21, Ne.symm h21]
    · simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply]
    · simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply]
    · simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply]
    · simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply]
    · simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply]
    · by_cases h : col = r
      · subst h
        simp [rightTauFOutputOne, rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply, diagonal]
      · have h1 : rightTauFOutputOne first second third r ≠ rightTauFOutputOne first second third col := by
          intro e; exact h (rightTauFOutputOne_injective first second third e).symm
        have h2 : rightTauFOutputTwo first second third r ≠ rightTauFOutputTwo first second third col := by
          intro e; exact h (rightTauFOutputTwo_injective first second third e).symm
        have h12 : rightTauFOutputOne first second third r ≠ rightTauFOutputTwo first second third col :=
          rightTauFOutputOne_ne_two first second third r col
        have h21 : rightTauFOutputTwo first second third r ≠ rightTauFOutputOne first second third col :=
          Ne.symm (rightTauFOutputOne_ne_two first second third col r)
        simp [rightTauFOutputOne, rightTauFOutputTwo, Matrix.one_apply, h, Ne.symm h,
          h1, Ne.symm h1, h2, Ne.symm h2, h12, Ne.symm h12, h21, Ne.symm h21]

theorem tauFusionPathMatrix_transpose_mul (first second third : FibCat)
    (tau scale : ℂ) (scale_sq : scale ^ 2 = tau) (tau_sq : tau ^ 2 + tau = 1) :
    (tauFusionPathMatrix first second third tau scale).transpose *
        tauFusionPathMatrix first second third tau scale = 1 := by
  classical
  rw [← Matrix.mul_eq_one_comm_of_equiv (leftTauSemanticPathEquivRight first second third)]
  exact tauFusionPathMatrix_mul_transpose first second third tau scale scale_sq tau_sq

theorem unitFusionPathMatrixTransport_mul_transpose (first second third : FibCat) :
    unitFusionPathMatrixTransport first second third *
        (unitFusionPathMatrixTransport first second third).transpose = 1 := by
  classical
  unfold unitFusionPathMatrixTransport
  dsimp [Matrix.reindex]
  rw [Matrix.transpose_submatrix]
  rw [Matrix.submatrix_mul_equiv]
  rw [unitFusionPathMatrix_mul_transpose]
  rw [Matrix.submatrix_one_equiv]

theorem unitFusionPathMatrixTransport_transpose_mul (first second third : FibCat) :
    (unitFusionPathMatrixTransport first second third).transpose *
        unitFusionPathMatrixTransport first second third = 1 := by
  classical
  unfold unitFusionPathMatrixTransport
  dsimp [Matrix.reindex]
  rw [Matrix.transpose_submatrix]
  rw [Matrix.submatrix_mul_equiv]
  rw [unitFusionPathMatrix_transpose_mul]
  rw [Matrix.submatrix_one_equiv]

theorem fibonacciAssociatorHom_comp_inv (first second third : FibCat)
    (tau scale : ℂ) (scale_sq : scale ^ 2 = tau) (tau_sq : tau ^ 2 + tau = 1) :
    FibHom.comp (fibonacciAssociatorHom first second third tau scale)
        (fibonacciAssociatorInv first second third tau scale) =
      FibHom.id (fibTensorObj (fibTensorObj first second) third) := by
  apply FibHom.ext
  · exact unitFusionPathMatrixTransport_mul_transpose first second third
  · dsimp [FibHom.comp, FibHom.id, fibonacciAssociatorHom, fibonacciAssociatorInv]
    rw [Matrix.transpose_submatrix]
    rw [Matrix.submatrix_mul_equiv]
    rw [tauFusionPathMatrix_mul_transpose first second third tau scale scale_sq tau_sq]
    rw [Matrix.submatrix_one_equiv]

theorem fibonacciAssociatorInv_comp_hom (first second third : FibCat)
    (tau scale : ℂ) (scale_sq : scale ^ 2 = tau) (tau_sq : tau ^ 2 + tau = 1) :
    FibHom.comp (fibonacciAssociatorInv first second third tau scale)
        (fibonacciAssociatorHom first second third tau scale) =
      FibHom.id (fibTensorObj first (fibTensorObj second third)) := by
  apply FibHom.ext
  · exact unitFusionPathMatrixTransport_transpose_mul first second third
  · dsimp [FibHom.comp, FibHom.id, fibonacciAssociatorHom, fibonacciAssociatorInv]
    rw [Matrix.transpose_submatrix]
    rw [Matrix.submatrix_mul_equiv]
    rw [tauFusionPathMatrix_transpose_mul first second third tau scale scale_sq tau_sq]
    rw [Matrix.submatrix_one_equiv]

def fibonacciAssociatorIso (first second third : FibCat)
    (tau scale : ℂ) (scale_sq : scale ^ 2 = tau) (tau_sq : tau ^ 2 + tau = 1) :
    fibTensorObj (fibTensorObj first second) third ≅
      fibTensorObj first (fibTensorObj second third) where
  hom := fibonacciAssociatorHom first second third tau scale
  inv := fibonacciAssociatorInv first second third tau scale
  hom_inv_id := fibonacciAssociatorHom_comp_inv first second third tau scale scale_sq tau_sq
  inv_hom_id := fibonacciAssociatorInv_comp_hom first second third tau scale scale_sq tau_sq

end InfoGeometry.Categorical.FibonacciGlobalAssociator
