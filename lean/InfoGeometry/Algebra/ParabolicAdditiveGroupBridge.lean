import InfoGeometry.Algebra.ParabolicJordanZorn
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

noncomputable section

namespace InfoGeometry.Algebra.ParabolicAdditiveGroupBridge

open InfoGeometry.GrandUnification.Matrix2KANPauliChain
open InfoGeometry.Algebra.ParabolicJordanZorn

abbrev shearCharacter : AddChar ℝ (GL (Fin 2) ℝ) :=
  Matrix.GeneralLinearGroup.upperRightHom

def shearHom : Multiplicative ℝ →* GL (Fin 2) ℝ :=
  shearCharacter.toMonoidHom

@[simp] theorem shearCharacter_val (parameter : ℝ) :
    (shearCharacter parameter).val = NPart parameter := rfl

theorem shearCharacter_injective : Function.Injective shearCharacter :=
  Matrix.GeneralLinearGroup.injective_upperRightHom

theorem shearCharacter_add (first second : ℝ) :
    shearCharacter (first + second) = shearCharacter first * shearCharacter second :=
  shearCharacter.map_add_eq_mul first second

theorem shearCharacter_neg (parameter : ℝ) :
    shearCharacter (-parameter) = (shearCharacter parameter)⁻¹ :=
  shearCharacter.map_neg_eq_inv parameter

theorem isParabolic_iff (parameter : ℝ) :
    (NPart parameter).IsParabolic ↔ parameter ≠ 0 := by
  rw [Matrix.isParabolic_iff_of_upperTriangular (by simp [NPart])]
  simp [NPart]

theorem shearCharacter_isParabolic_iff (parameter : ℝ) :
    (shearCharacter parameter).IsParabolic ↔ parameter ≠ 0 :=
  isParabolic_iff parameter

theorem parabolic_exact_index_two (parameter : ℝ)
    (hparabolic : (NPart parameter).IsParabolic) :
    (NPart parameter - 1) ^ 2 = 0 ∧ NPart parameter - 1 ≠ 0 :=
  shear_exact_index_two parameter ((isParabolic_iff parameter).mp hparabolic)

theorem parabolic_not_similar_to_diagonal (parameter : ℝ)
    (hparabolic : (NPart parameter).IsParabolic) :
    ¬ ∃ (basisMatrix : Matrix (Fin 2) (Fin 2) ℝ) (entries : Fin 2 → ℝ),
      basisMatrix.det ≠ 0 ∧
        NPart parameter * basisMatrix = basisMatrix * Matrix.diagonal entries :=
  not_similar_to_diagonal parameter ((isParabolic_iff parameter).mp hparabolic)

end InfoGeometry.Algebra.ParabolicAdditiveGroupBridge
