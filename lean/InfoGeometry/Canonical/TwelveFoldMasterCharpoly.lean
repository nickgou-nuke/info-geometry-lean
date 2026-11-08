import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Canonical.TwelveFoldGeneralizedCliffordExtension

open scoped Matrix

namespace InfoGeometry.Canonical.TwelveFoldMasterCharpoly

open Polynomial
open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.TwelveFoldExplicitOperators

noncomputable section

private def blockEquiv : (Fin 3 ⊕ Fin 3) ≃ (Fin 2 × Fin 3) where
  toFun x := match x with
    | Sum.inl i => (0, i)
    | Sum.inr i => (1, i)
  invFun p := match p.1 with
    | 0 => Sum.inl p.2
    | 1 => Sum.inr p.2
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro p; rcases p with ⟨i, j⟩; fin_cases i <;> rfl

private def masterBlock : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ :=
  Matrix.fromBlocks (colorShift ^ 2) 0 0 (-Complex.I • (colorShift ^ 2))

private theorem masterTwelve_reindex_block :
    Matrix.reindex blockEquiv.symm blockEquiv.symm masterTwelve = masterBlock := by
  rw [masterTwelve_eq_kronecker]
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp [blockEquiv, masterBlock, omegaChi, uPlus, uMinus,
            sheetParity, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
            Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two,
            Complex.I_mul_I, pow_succ, pow_two]
      | inr j =>
          simp [blockEquiv, masterBlock, omegaChi, uPlus, uMinus,
            sheetParity, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
            Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two,
            Complex.I_mul_I, pow_succ, pow_two]
  | inr i =>
      cases j with
      | inl j =>
          simp [blockEquiv, masterBlock, omegaChi, uPlus, uMinus,
            sheetParity, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
            Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two,
            Complex.I_mul_I, pow_succ, pow_two]
      | inr j =>
          simp [blockEquiv, masterBlock, omegaChi, uPlus, uMinus,
            sheetParity, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
            Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two,
            Complex.I_mul_I, pow_succ, pow_two]

theorem masterTwelve_charpoly :
    masterTwelve.charpoly = (X ^ 3 - 1) * (X ^ 3 - C Complex.I) := by
  rw [← Matrix.charpoly_reindex blockEquiv.symm masterTwelve,
    masterTwelve_reindex_block]
  change (Matrix.fromBlocks (colorShift ^ 2) 0 0
      (-Complex.I • (colorShift ^ 2))).charpoly = _
  rw [Matrix.charpoly_fromBlocks_zero₁₂]
  rw [show (colorShift ^ 2).charpoly = X ^ 3 - 1 by
    unfold Matrix.charpoly Matrix.charmatrix
    rw [Matrix.det_fin_three]
    simp [colorShift, Matrix.mul_apply, Fin.sum_univ_three, pow_two]
    ring]
  rw [show (-Complex.I • (colorShift ^ 2)).charpoly = X ^ 3 - C Complex.I by
    unfold Matrix.charpoly Matrix.charmatrix
    rw [Matrix.det_fin_three]
    simp [colorShift, Matrix.mul_apply, Fin.sum_univ_three, pow_two,
      Complex.I_mul_I]
    norm_num [← map_mul, Complex.I_mul_I]
    ring]

end
end InfoGeometry.Canonical.TwelveFoldMasterCharpoly
