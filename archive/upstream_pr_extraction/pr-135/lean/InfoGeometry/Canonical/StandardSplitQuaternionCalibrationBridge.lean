import InfoGeometry.Canonical.SplitG2HodgeWedgeCharacterization

namespace InfoGeometry.Canonical

/-!
# Standard split-quaternion calibration bridge

This file is a thin calibration wrapper over the native G₂ split carrier.
It does not introduce a new octonion algebra, and it does not claim any new
calibration theorem beyond the explicitly supplied restriction equalities.
-/

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

-- Standard associative and coassociative calibration carriers.
variable (StandardAssociativePlane : Submodule ℚ V)
variable (StandardCoassociativeComplement : Submodule ℚ V)

/-- Restriction of a 3-form to a submodule. -/
def restrictThreeForm
    (S : Submodule ℚ V)
    (phi : AlternatingMap ℚ V ℚ (Fin 3)) :
    AlternatingMap ℚ S ℚ (Fin 3) :=
  phi.compLinearMap S.subtype

/-- Restriction of a 4-form to a submodule. -/
def restrictFourForm
    (S : Submodule ℚ V)
    (psi : AlternatingMap ℚ V ℚ (Fin 4)) :
    AlternatingMap ℚ S ℚ (Fin 4) :=
  psi.compLinearMap S.subtype

-- Standard volume forms on the 3D and 4D slices.
variable (vol_3D : AlternatingMap ℚ StandardAssociativePlane ℚ (Fin 3))
variable (vol_4D : AlternatingMap ℚ StandardCoassociativeComplement ℚ (Fin 4))

/-- Bridge data for the standard calibration slice. -/
structure StandardSliceCalibrationData where
  canonicalThreeForm : AlternatingMap ℚ V ℚ (Fin 3)
  coassociativeFourForm : AlternatingMap ℚ V ℚ (Fin 4)
  threeForm_eq_volume :
    restrictThreeForm StandardAssociativePlane canonicalThreeForm = vol_3D
  threeForm_eq_zero_on_complement :
    restrictThreeForm StandardCoassociativeComplement canonicalThreeForm = 0
  fourForm_eq_volume :
    restrictFourForm StandardCoassociativeComplement coassociativeFourForm = vol_4D

namespace StandardSliceCalibrationData

variable (data :
  StandardSliceCalibrationData
    (V := V)
    (StandardAssociativePlane := StandardAssociativePlane)
    (StandardCoassociativeComplement := StandardCoassociativeComplement)
    (vol_3D := vol_3D)
    (vol_4D := vol_4D))

theorem standard_coassociative_complement_phi_vanishes :
    restrictThreeForm StandardCoassociativeComplement data.canonicalThreeForm = 0 :=
  data.threeForm_eq_zero_on_complement

theorem standard_associative_volume_calibration :
    restrictThreeForm StandardAssociativePlane data.canonicalThreeForm = vol_3D :=
  data.threeForm_eq_volume

theorem standard_coassociative_volume_calibration :
    restrictFourForm StandardCoassociativeComplement data.coassociativeFourForm = vol_4D :=
  data.fourForm_eq_volume

theorem standard_split_quaternion_calibration_synthesis :
    (restrictThreeForm StandardAssociativePlane data.canonicalThreeForm = vol_3D) ∧
    (restrictThreeForm StandardCoassociativeComplement data.canonicalThreeForm = 0) ∧
    (restrictFourForm StandardCoassociativeComplement data.coassociativeFourForm = vol_4D) :=
  ⟨standard_associative_volume_calibration
      (StandardAssociativePlane := StandardAssociativePlane)
      (StandardCoassociativeComplement := StandardCoassociativeComplement)
      (vol_3D := vol_3D) (vol_4D := vol_4D) data,
   standard_coassociative_complement_phi_vanishes
      (StandardAssociativePlane := StandardAssociativePlane)
      (StandardCoassociativeComplement := StandardCoassociativeComplement)
      (vol_3D := vol_3D) (vol_4D := vol_4D) data,
   standard_coassociative_volume_calibration
      (StandardAssociativePlane := StandardAssociativePlane)
      (StandardCoassociativeComplement := StandardCoassociativeComplement)
      (vol_3D := vol_3D) (vol_4D := vol_4D) data⟩

end StandardSliceCalibrationData

end InfoGeometry.Canonical
