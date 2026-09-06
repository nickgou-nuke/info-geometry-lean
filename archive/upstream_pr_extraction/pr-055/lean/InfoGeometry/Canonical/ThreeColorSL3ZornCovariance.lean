import Mathlib
import InfoGeometry.Canonical.ThreeColorSL3ZornActionBridge

open Matrix

namespace InfoGeometry.Canonical.ThreeColorSL3ZornCovariance

open InfoGeometry.Physics.SplitOctonionBraidSU3
open InfoGeometry.Physics.ThreeColorSL3ZornAction

/-! The contragredient `SL(3)` action preserves the native Zorn pairing.

This is the unconditional part of the covariance package.  The two cross
product covariance statements remain separate because they require the
orientation/determinant argument and are not inferred merely from pairing
invariance.
-/

theorem specialLinear_preserves_pairing
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    PreservesPairing g := by
  intro u v
  change dot3 ((g : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ u)
      (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
        Matrix (Fin 3) (Fin 3) ℂ)ᵀ *ᵥ v) =
    dot3 u v
  have hdot (x y : Fin 3 → ℂ) : dot3 x y = x ⬝ᵥ y := by
    simp [dot3, dotProduct, Fin.sum_univ_three]
  rw [hdot, hdot]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [Matrix.mulVec_mulVec]
  rw [← Matrix.SpecialLinearGroup.coe_mul]
  rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  simp

theorem specialLinear_preserves_cross_fundamental
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    PreservesCrossFundamental g := by
  intro u v
  ext i
  fin_cases i <;>
    simp [colourFundamentalAction, colourDualAction, cross3,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.adjugate_apply, Matrix.det_fin_three] <;> ring

theorem specialLinear_preserves_dual_cross
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    PreservesDualCross g := by
  intro u v
  let h : Matrix.SpecialLinearGroup (Fin 3) ℂ :=
    Matrix.SpecialLinearGroup.transpose (g⁻¹)
  have hcross : PreservesCrossFundamental h :=
    specialLinear_preserves_cross_fundamental h
  have hc := hcross u v
  have hmat :
      (((g : Matrix (Fin 3) (Fin 3) ℂ).adjugate)ᵀ).adjugateᵀ =
        (g : Matrix (Fin 3) (Fin 3) ℂ) := by
    rw [← Matrix.adjugate_transpose]
    rw [Matrix.adjugate_adjugate _ (by norm_num)]
    simp [g.det_coe]
  simpa [h, colourFundamentalAction, colourDualAction,
    Matrix.SpecialLinearGroup.coe_transpose, hmat] using hc.symm

theorem specialLinear_zornSL3Action_mul
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (X Y : InfoGeometry.Physics.ThreeColorSL3ZornAction.Zorn) :
    zornSL3Action g (zornMul X Y) =
      zornMul (zornSL3Action g X) (zornSL3Action g Y) := by
  exact zornSL3Action_mul_of_covariant g
    (specialLinear_preserves_pairing g)
    (specialLinear_preserves_cross_fundamental g)
    (specialLinear_preserves_dual_cross g) X Y

theorem specialLinear_zornSL3Action_preserves_norm
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (X : InfoGeometry.Physics.ThreeColorSL3ZornAction.Zorn) :
    zornNorm (zornSL3Action g X) = zornNorm X := by
  exact zornSL3Action_preserves_norm_of_pairing g
    (specialLinear_preserves_pairing g) X

end InfoGeometry.Canonical.ThreeColorSL3ZornCovariance
