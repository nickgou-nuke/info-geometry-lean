/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.QutritSU3AdjointDecomposition
import InfoGeometry.Canonical.ThreeColorSL3ZornActionBridge

open Matrix

namespace InfoGeometry.Canonical.ThreeColorSL3ZornCovariance

open InfoGeometry.Physics.SplitOctonionBraidSU3
open InfoGeometry.Physics.ThreeColorSL3ZornAction

/-- Matrix units witness that the exact `3 × 3` coefficient carrier used by
the special-linear and special-unitary actions is noncommutative. -/
def matrixE01 : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  if i = 0 ∧ j = 1 then 1 else 0

def matrixE10 : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  if i = 1 ∧ j = 0 then 1 else 0

theorem matrix_units_noncommute :
    matrixE01 * matrixE10 ≠ matrixE10 * matrixE01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) h
  norm_num [matrixE01, matrixE10, Matrix.mul_apply, Fin.sum_univ_three] at h00

/-! The contragredient `SL(3)` action preserves the native Zorn pairing.

The pairing and both cross-product covariance identities are proved for every
special-linear matrix below. The determinant-one condition supplies the
orientation factor needed by the cross-product identities.
-/

theorem specialLinear_preserves_pairing
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    PreservesPairing g :=
  colourActions_preserve_pairing g

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
    (specialLinear_preserves_cross_fundamental g)
    (specialLinear_preserves_dual_cross g) X Y

theorem specialLinear_zornSL3Action_preserves_norm
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (X : InfoGeometry.Physics.ThreeColorSL3ZornAction.Zorn) :
    zornNorm (zornSL3Action g X) = zornNorm X := by
  exact zornSL3Action_preserves_norm_of_pairing g X

local notation "SU3" => InfoGeometry.Canonical.QutritSU3AdjointDecomposition.SU3

/-- The native special-unitary matrix embeds into the determinant-one carrier
used by the Zorn action. -/
def specialUnitaryToSpecialLinear (g : SU3) : Matrix.SpecialLinearGroup (Fin 3) ℂ :=
  ⟨(g : Matrix (Fin 3) (Fin 3) ℂ),
    (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2⟩

@[simp] theorem specialUnitaryToSpecialLinear_coe (g : SU3) :
    (specialUnitaryToSpecialLinear g : Matrix (Fin 3) (Fin 3) ℂ) = g := rfl

@[simp] theorem specialUnitaryToSpecialLinear_one :
    specialUnitaryToSpecialLinear (1 : SU3) = 1 := by
  apply Subtype.ext
  rfl

theorem specialUnitaryToSpecialLinear_mul (g h : SU3) :
    specialUnitaryToSpecialLinear (g * h) =
      specialUnitaryToSpecialLinear g * specialUnitaryToSpecialLinear h := by
  apply Subtype.ext
  rfl

theorem specialUnitaryToSpecialLinear_injective :
    Function.Injective specialUnitaryToSpecialLinear := by
  intro g h hgh
  apply Subtype.ext
  exact congrArg (fun k : Matrix.SpecialLinearGroup (Fin 3) ℂ =>
    (k : Matrix (Fin 3) (Fin 3) ℂ)) hgh

/-- The induced special-unitary action on the existing complex Zorn carrier. -/
def su3ZornAction (g : SU3)
    (X : InfoGeometry.Physics.ThreeColorSL3ZornAction.Zorn) :=
  zornSL3Action (specialUnitaryToSpecialLinear g) X

@[simp] theorem su3ZornAction_one
    (X : InfoGeometry.Physics.ThreeColorSL3ZornAction.Zorn) :
    su3ZornAction 1 X = X := by
  simp [su3ZornAction]

theorem su3ZornAction_preserves_multiplication (g : SU3) (X Y :
    InfoGeometry.Physics.ThreeColorSL3ZornAction.Zorn) :
    su3ZornAction g (zornMul X Y) = zornMul (su3ZornAction g X) (su3ZornAction g Y) := by
  exact specialLinear_zornSL3Action_mul (specialUnitaryToSpecialLinear g) X Y

theorem su3ZornAction_preserves_norm (g : SU3)
    (X : InfoGeometry.Physics.ThreeColorSL3ZornAction.Zorn) :
    zornNorm (su3ZornAction g X) = zornNorm X := by
  exact specialLinear_zornSL3Action_preserves_norm (specialUnitaryToSpecialLinear g) X

theorem su3ZornAction_mul (g h : SU3)
    (X : InfoGeometry.Physics.ThreeColorSL3ZornAction.Zorn) :
    su3ZornAction (g * h) X = su3ZornAction g (su3ZornAction h X) := by
  unfold su3ZornAction
  rw [specialUnitaryToSpecialLinear_mul]
  exact (congrFun (zornSL3Action_comp
    (specialUnitaryToSpecialLinear h) (specialUnitaryToSpecialLinear g)) X).symm

end InfoGeometry.Canonical.ThreeColorSL3ZornCovariance
