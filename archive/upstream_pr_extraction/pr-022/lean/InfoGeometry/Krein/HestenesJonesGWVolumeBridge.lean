import InfoGeometry.Krein.HestenesJonesFiltrationBridge
import InfoGeometry.Canonical.WeylGWVolumeBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace BigOperators

noncomputable section

namespace InfoGeometry.Krein.HestenesJonesGWVolumeBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.HestenesJonesFiltrationBridge
open InfoGeometry.Canonical.StandardFormOmegaVolumeBridge
open InfoGeometry.Canonical.WeylGWVolumeBridge
open InfoGeometry.Volume.ConnesCocycle

section Core

variable {H Functional State G T Target Coeff Word : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace (DoubledSpace H)]
variable [Fintype Word] [DecidableEq Word]

local notation "H₂" => DoubledSpace H
local notation "EndH" => AlgebraEnd H

noncomputable local instance instNormedRingEndH : NormedRing EndH := inferInstance
noncomputable local instance instNormedAlgebraRealEndH : NormedAlgebra ℝ EndH := inferInstance
local instance instTopologicalRingEndH : IsTopologicalRing EndH := inferInstance
local instance instCompleteSpaceEndH : CompleteSpace EndH := inferInstance

/--
Adapter from the Hestenes/Jones Ω-filtration readout to the existing
projective Weyl/GW physical-volume bridge.

This is only a socket: it does not construct a Type III determinant or trace.
It records that the GW face-volume owner and the Hestenes/Jones owner use the
same standard-form Ω-volume carrier.
-/
@[rep_depth krein]
structure HestenesJonesGWVolumeBridge where
  /-- Hestenes/Krein vacuum readout over Jones/Cantor atoms. -/
  jones :
    HestenesJonesFiltrationBridge (H := H) (Word := Word)

  /-- Existing projective Weyl/GW face-volume bridge. -/
  gw :
    StandardFormFaceWeylGWVolumeFusion
      (H := H) (Functional := Functional) (State := State)
      (G := G) (T := T) (Target := Target) (Coeff := Coeff) (Word := Word)

  /-- Both bridges use the same Ω-volume carrier. -/
  omegaVolume_eq :
    gw.omegaVolume = jones.omegaVolume

namespace HestenesJonesGWVolumeBridge

variable (B :
  HestenesJonesGWVolumeBridge
    (H := H) (Functional := Functional) (State := State)
    (G := G) (T := T) (Target := Target) (Coeff := Coeff) (Word := Word))

/-- GW physical face volume is the localized Ω-expectation from the Jones bridge. -/
@[rep_depth krein]
theorem physicalVolume_eq_localizedExpectation
    (w : Word) :
    B.gw.projectiveFace.base.physicalVolume (B.gw.wordToState w) =
      NaturalConeVolumeBridge.localizedExpectation B.jones.omegaVolume w := by
  calc
    B.gw.projectiveFace.base.physicalVolume (B.gw.wordToState w)
        = NaturalConeVolumeBridge.localizedExpectation B.gw.omegaVolume w :=
            StandardFormFaceWeylGWVolumeFusion.physicalVolume_eq_localizedExpectation B.gw w
    _ = NaturalConeVolumeBridge.localizedExpectation B.jones.omegaVolume w := by
            rw [B.omegaVolume_eq]

/--
GW physical face volume is the Hestenes vacuum expectation of the localized
standard-form face operator.
-/
@[rep_depth krein]
theorem physicalVolume_eq_hestenesLocalizedExpectation
    (w : Word) :
    B.gw.projectiveFace.base.physicalVolume (B.gw.wordToState w) =
      B.jones.vacuum.vacuumRealState
        (NaturalConeVolumeBridge.localizationOp B.jones.omegaVolume w) := by
  calc
    B.gw.projectiveFace.base.physicalVolume (B.gw.wordToState w)
        = NaturalConeVolumeBridge.localizedExpectation B.jones.omegaVolume w :=
            B.physicalVolume_eq_localizedExpectation w
    _ = B.jones.vacuum.vacuumRealState
          (NaturalConeVolumeBridge.localizationOp B.jones.omegaVolume w) :=
            HestenesJonesFiltrationBridge.localizedExpectation_eq_vacuumRealState B.jones w

/-- Projective Weyl scale changes leave the GW physical volume unchanged. -/
@[rep_depth krein]
theorem physicalVolume_scale_invariant
    (c : ℝ) (hc : c ≠ 0) (s : State) :
    B.gw.projectiveFace.base.physicalVolume (B.gw.projectiveFace.base.scaleState c s) =
      B.gw.projectiveFace.base.physicalVolume s :=
  StandardFormFaceWeylGWVolumeFusion.physicalVolume_scale_invariant B.gw c hc s

/--
The modular volume potential of the common Ω-carrier is the negative log of
the Hestenes vacuum expectation of the Jones atom.
-/
@[rep_depth krein]
theorem modularVolumePotential_eq_neg_log_vacuumRealState
    (w : Word) :
    NaturalConeVolumeBridge.modularVolumePotential B.gw.omegaVolume w =
      -Real.log
        (B.jones.vacuum.vacuumRealState
          (NaturalConeVolumeBridge.wignerJonesAtom B.jones.omegaVolume w)) := by
  rw [B.omegaVolume_eq]
  exact HestenesJonesFiltrationBridge.modularVolumePotential_eq_neg_log_vacuumRealState
    B.jones w

/--
If the localized Jones faces partition the operator unit, the calibrated
projective GW physical volumes sum to one.
-/
@[rep_depth krein]
theorem total_projective_face_volume_is_unity
    (hLocalPartition :
      (∑ w : Word, NaturalConeVolumeBridge.localizationOp B.jones.omegaVolume w) =
        (1 : EndH)) :
    (∑ w : Word, B.gw.projectiveFace.base.physicalVolume (B.gw.wordToState w)) = 1 := by
  apply StandardFormFaceWeylGWVolumeFusion.total_projective_face_volume_is_unity B.gw
  rw [B.omegaVolume_eq]
  exact hLocalPartition

end HestenesJonesGWVolumeBridge

end Core

end InfoGeometry.Krein.HestenesJonesGWVolumeBridge
