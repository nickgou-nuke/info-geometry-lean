import InfoGeometry.Categorical.FibonacciGlobalAssociator

noncomputable section

namespace InfoGeometry.Categorical.FibonacciGlobalAssociator

open CategoryTheory
open FibonacciGlobalChannelBasis FibonacciBraidedCategory FibonacciHomSpace

theorem tauFusionPathMatrix_mul_transpose (first second third : FibCat)
    (tau scale : ℂ) (scale_sq : scale ^ 2 = tau) (tau_sq : tau ^ 2 + tau = 1) :
    tauFusionPathMatrix first second third tau scale *
        (tauFusionPathMatrix first second third tau scale).transpose = 1 := by
  classical
  have diagonal : tau * tau + scale * scale = 1 := by
    calc
      tau * tau + scale * scale = tau ^ 2 + scale ^ 2 := by ring
      _ = 1 := by rw [scale_sq]; exact tau_sq
  have cross : tau * scale + scale * -tau = 0 := by ring
  have cross' : scale * tau + -tau * scale = 0 := by ring
  ext row column
  rcases row with row | row | row | row | row | row | row | row <;>
    rcases column with column | column | column | column | column | column | column | column <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply,
      tauFusionPathMatrix, tauFusionPathEntry, rightTauFOutputOne,
      rightTauFOutputTwo, leftTauSemanticPathMap, Matrix.one_apply,
      ite_mul, mul_ite, diagonal, cross, cross', eq_comm] <;>
    split_ifs <;> simp_all <;> ring

theorem tauFusionPathMatrix_transpose_mul (first second third : FibCat)
    (tau scale : ℂ) (scale_sq : scale ^ 2 = tau) (tau_sq : tau ^ 2 + tau = 1) :
    (tauFusionPathMatrix first second third tau scale).transpose *
        tauFusionPathMatrix first second third tau scale = 1 := by
  classical
  exact (Matrix.mul_eq_one_comm_of_equiv
    (leftTauSemanticPathEquivRight first second third)).mp
      (tauFusionPathMatrix_mul_transpose first second third tau scale scale_sq tau_sq)

theorem unitFusionPathMatrixTransport_mul_transpose (first second third : FibCat) :
    unitFusionPathMatrixTransport first second third *
        (unitFusionPathMatrixTransport first second third).transpose = 1 := by
  classical
  unfold unitFusionPathMatrixTransport
  rw [Matrix.transpose_reindex]
  change Matrix.reindexLinearEquiv ℂ ℂ _ _ _ *
    Matrix.reindexLinearEquiv ℂ ℂ _ _ _ = 1
  rw [Matrix.reindexLinearEquiv_mul, unitFusionPathMatrix_mul_transpose,
    Matrix.reindexLinearEquiv_one]

theorem unitFusionPathMatrixTransport_transpose_mul (first second third : FibCat) :
    (unitFusionPathMatrixTransport first second third).transpose *
        unitFusionPathMatrixTransport first second third = 1 := by
  classical
  unfold unitFusionPathMatrixTransport
  rw [Matrix.transpose_reindex]
  change Matrix.reindexLinearEquiv ℂ ℂ _ _ _ *
    Matrix.reindexLinearEquiv ℂ ℂ _ _ _ = 1
  rw [Matrix.reindexLinearEquiv_mul, unitFusionPathMatrix_transpose_mul,
    Matrix.reindexLinearEquiv_one]

theorem fibonacciAssociatorHom_comp_inv (first second third : FibCat)
    (tau scale : ℂ) (scale_sq : scale ^ 2 = tau) (tau_sq : tau ^ 2 + tau = 1) :
    FibHom.comp (fibonacciAssociatorHom first second third tau scale)
        (fibonacciAssociatorInv first second third tau scale) =
      FibHom.id (fibTensorObj (fibTensorObj first second) third) := by
  apply FibHom.ext
  · exact unitFusionPathMatrixTransport_mul_transpose first second third
  · change Matrix.reindex _ _ _ * (Matrix.reindex _ _ _).transpose = 1
    rw [Matrix.transpose_reindex]
    change Matrix.reindexLinearEquiv ℂ ℂ _ _ _ *
      Matrix.reindexLinearEquiv ℂ ℂ _ _ _ = 1
    rw [Matrix.reindexLinearEquiv_mul,
      tauFusionPathMatrix_mul_transpose first second third tau scale scale_sq tau_sq,
      Matrix.reindexLinearEquiv_one]

theorem fibonacciAssociatorInv_comp_hom (first second third : FibCat)
    (tau scale : ℂ) (scale_sq : scale ^ 2 = tau) (tau_sq : tau ^ 2 + tau = 1) :
    FibHom.comp (fibonacciAssociatorInv first second third tau scale)
        (fibonacciAssociatorHom first second third tau scale) =
      FibHom.id (fibTensorObj first (fibTensorObj second third)) := by
  apply FibHom.ext
  · exact unitFusionPathMatrixTransport_transpose_mul first second third
  · change (Matrix.reindex _ _ _).transpose * Matrix.reindex _ _ _ = 1
    rw [Matrix.transpose_reindex]
    change Matrix.reindexLinearEquiv ℂ ℂ _ _ _ *
      Matrix.reindexLinearEquiv ℂ ℂ _ _ _ = 1
    rw [Matrix.reindexLinearEquiv_mul,
      tauFusionPathMatrix_transpose_mul first second third tau scale scale_sq tau_sq,
      Matrix.reindexLinearEquiv_one]

def fibonacciAssociatorIso (first second third : FibCat)
    (tau scale : ℂ) (scale_sq : scale ^ 2 = tau) (tau_sq : tau ^ 2 + tau = 1) :
    fibTensorObj (fibTensorObj first second) third ≅
      fibTensorObj first (fibTensorObj second third) where
  hom := fibonacciAssociatorHom first second third tau scale
  inv := fibonacciAssociatorInv first second third tau scale
  hom_inv_id := fibonacciAssociatorHom_comp_inv first second third tau scale scale_sq tau_sq
  inv_hom_id := fibonacciAssociatorInv_comp_hom first second third tau scale scale_sq tau_sq

end InfoGeometry.Categorical.FibonacciGlobalAssociator
