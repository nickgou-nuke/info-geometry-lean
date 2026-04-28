import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

open scoped MatrixGroups
open UpperHalfPlane

abbrev SL2R : Type := SL(2, ℝ)
abbrev SL2Z : Type := SL(2, ℤ)

theorem sl2r_neg_smul (g : SL2R) (τ : UpperHalfPlane) :
    (-g) • τ = g • τ := by
  change ((-g : SL2R) : GL (Fin 2) ℝ) • τ = ((g : SL2R) : GL (Fin 2) ℝ) • τ
  have h1 : ((-g : SL2R) : GL (Fin 2) ℝ) = - ((g : SL2R) : GL (Fin 2) ℝ) := by ext i j; rfl
  rw [h1, UpperHalfPlane.neg_smul]

theorem sl2z_neg_smul (g : SL2Z) (τ : UpperHalfPlane) :
    (-g) • τ = g • τ := by
  exact ModularGroup.SL_neg_smul g τ
