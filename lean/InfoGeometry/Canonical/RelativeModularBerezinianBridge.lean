import InfoGeometry.Canonical.RelativeModularOperator
import InfoGeometry.Canonical.RestrictedVolumeCharacter
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import InfoGeometry.Meta.Architecture

/-!
# Relative Modular Berezinian Bridge

Bridge from the finite diagonal relative modular operator owner to the existing
restricted-sheet and Cartan Berezinian surfaces.

The owner remains `relativeModularOperator` and its scalar shadows in
`RelativeModularOperator.lean`. This file only realizes the plus/minus modular
operators as sheet automorphisms on `Fin n → ℝ` and identifies the resulting
restricted-volume and Berezinian readouts with the modular supervolume shadow.
-/

namespace InfoGeometry.Canonical.RelativeModularBerezinianBridge

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.RestrictedVolumeCharacter
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal
open InfoGeometry.Volume.Base

section Finite

variable {n : ℕ} [Nonempty (Fin n)]

local notation "Efin" => (Fin n → ℝ)

private theorem relativeModularOperator_det_isUnit
    (q q0 : PositiveRay (Fin n)) :
    IsUnit ((relativeModularOperator (n := n) q q0).det) := by
  classical
  apply isUnit_iff_ne_zero.mpr
  simpa [relativeModularVolumeShadow] using
    ne_of_gt (relativeModularVolumeShadow_pos (n := n) q q0)

/-- Finite modular operator realized as a genuine sheet automorphism. -/
@[rep_depth operator]
noncomputable def relativeModularSheetEquiv
    (q q0 : PositiveRay (Fin n)) : Efin ≃ₗ[ℝ] Efin :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin n))
    (relativeModularOperator (n := n) q q0)
    (relativeModularOperator_det_isUnit (n := n) q q0)

theorem relativeModularSheetEquiv_toLinearMap
    (q q0 : PositiveRay (Fin n)) :
    ((relativeModularSheetEquiv (n := n) q q0 : Efin ≃ₗ[ℝ] Efin) : Efin →ₗ[ℝ] Efin)
      = Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
          (relativeModularOperator (n := n) q q0) := by
  rfl

theorem relativeModularSheetEquiv_det_coe_eq_volumeShadow
    (q q0 : PositiveRay (Fin n)) :
    ((LinearEquiv.det (relativeModularSheetEquiv (n := n) q q0)) : ℝ)
      = relativeModularVolumeShadow (n := n) q q0 := by
  rw [LinearEquiv.coe_det]
  rw [relativeModularSheetEquiv_toLinearMap]
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n))]
  rw [LinearMap.toMatrix_toLin]
  unfold relativeModularVolumeShadow
  rfl

/-- The doubled-sheet restricted character carried by plus/minus modular operators. -/
@[rep_depth operator]
noncomputable def relativeModularRestrictedSheetEquiv
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    RestrictedSheetEquiv Efin where
  plus := relativeModularSheetEquiv (n := n) qPlus q0Plus
  minus := relativeModularSheetEquiv (n := n) qMinus q0Minus

theorem relativeModularRestrictedSheetEquiv_character_coe_eq_berezinianShadow
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    (((RestrictedSheetEquiv.restrictedVolumeCharacter (E := Efin)
        (relativeModularRestrictedSheetEquiv (n := n) qPlus q0Plus qMinus q0Minus)) : ℝˣ) : ℝ)
      = relativeModularBerezinianShadow (n := n) qPlus q0Plus qMinus q0Minus := by
  unfold RestrictedSheetEquiv.restrictedVolumeCharacter
    relativeModularRestrictedSheetEquiv relativeModularBerezinianShadow VolumeHom
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv,
    relativeModularSheetEquiv_det_coe_eq_volumeShadow]

/--
The restricted-volume scalar on the doubled-sheet side is exactly the
Berezinian-style supervolume shadow of the modular operator owner.
-/
@[rep_depth transport, capstone]
theorem relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_berezinianShadow
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    RestrictedSheetEquiv.restrictedVolumeScale (E := Efin)
      (relativeModularRestrictedSheetEquiv (n := n) qPlus q0Plus qMinus q0Minus)
      = relativeModularBerezinianShadow (n := n) qPlus q0Plus qMinus q0Minus := by
  rw [RestrictedSheetEquiv.restrictedVolumeScale_eq_abs_character]
  rw [relativeModularRestrictedSheetEquiv_character_coe_eq_berezinianShadow]
  exact abs_of_pos (relativeModularBerezinianShadow_pos (n := n) qPlus q0Plus qMinus q0Minus)

/--
The negative logarithmic restricted-volume readout is exactly the modular
supervolume potential.
-/
@[rep_depth thermo, capstone]
theorem neg_log_relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_supervolumePotential
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    -Real.log
        (RestrictedSheetEquiv.restrictedVolumeScale (E := Efin)
          (relativeModularRestrictedSheetEquiv (n := n) qPlus q0Plus qMinus q0Minus))
      = relativeModularSupervolumePotential (n := n) qPlus q0Plus qMinus q0Minus := by
  rw [relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_berezinianShadow]
  rfl

end Finite

end InfoGeometry.Canonical.RelativeModularBerezinianBridge
