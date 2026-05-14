import InfoGeometry.Krein.HestenesPhaseVolumeBridge
import InfoGeometry.Canonical.StandardFormOmegaVolumeBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace BigOperators

noncomputable section

namespace InfoGeometry.Krein.HestenesJonesFiltrationBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.HestenesModularKMSBridge
open InfoGeometry.Krein.HestenesKreinVacuumBridge
open InfoGeometry.Krein.HestenesPhaseVolumeBridge
open InfoGeometry.Canonical.StandardFormOmegaVolumeBridge
open InfoGeometry.Volume.ConnesCocycle

section Core

variable {H Word : Type*}
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
Jones/Wigner atom filtration bridge for the Hestenes/Krein phase-volume socket.

This adapter connects the core Hestenes vacuum state `V.vacuumRealState` to the
existing standard-form Ω-volume owner `NaturalConeVolumeBridge`.  It does not
claim that Wigner--Jones projectors are invertible or that a determinant exists
on them.  It only identifies the trace-replacement readout:

`ωΩ(p_w) = [p_w Ω, Ω]_J`.
-/
@[rep_depth krein]
structure HestenesJonesFiltrationBridge where
  /-- Hestenes/Krein KMS packet. -/
  packet :
    HestenesKreinKMSPacket (E := H₂)

  /-- Hestenes/Krein vacuum vector socket. -/
  vacuum :
    HestenesKreinVacuum (E := H₂) packet

  /-- Core Hestenes phase-volume/log-det socket on units. -/
  phase :
    HestenesPhaseVolumeBridge (E := H₂) packet vacuum

  /-- Existing finite Wigner--Jones/Ω-volume owner. -/
  omegaVolume :
    NaturalConeVolumeBridge (H := H) Word

  /-- The Ω-vector used by the volume owner is the Hestenes vacuum. -/
  omega_eq_vacuum :
    omegaVolume.Omega = vacuum.omega

namespace HestenesJonesFiltrationBridge

variable (B :
  InfoGeometry.Krein.HestenesJonesFiltrationBridge.HestenesJonesFiltrationBridge
    (H := H) (Word := Word))

/-- The installed Ω-volume state agrees with the Hestenes vacuum real state. -/
@[rep_depth krein]
theorem volumeState_eq_vacuumRealState
    (A : EndH) :
    B.omegaVolume.volumeState A = B.vacuum.vacuumRealState A := by
  rw [B.omegaVolume.volumeState_eq_omega_kreinExpectation A]
  unfold HestenesKreinVacuum.vacuumRealState
  unfold HestenesKreinKMSPacket.hestenesExpectation
  rw [B.omega_eq_vacuum]

/-- Wigner--Jones atom expectation is the Hestenes vacuum expectation. -/
@[rep_depth krein]
theorem atomExpectation_eq_vacuumRealState
    (w : Word) :
    NaturalConeVolumeBridge.atomExpectation B.omegaVolume w =
      B.vacuum.vacuumRealState
        (NaturalConeVolumeBridge.wignerJonesAtom B.omegaVolume w) := by
  unfold NaturalConeVolumeBridge.atomExpectation
  exact B.volumeState_eq_vacuumRealState
    (NaturalConeVolumeBridge.wignerJonesAtom B.omegaVolume w)

/-- Localized face expectation is the Hestenes vacuum expectation. -/
@[rep_depth krein]
theorem localizedExpectation_eq_vacuumRealState
    (w : Word) :
    NaturalConeVolumeBridge.localizedExpectation B.omegaVolume w =
      B.vacuum.vacuumRealState
        (NaturalConeVolumeBridge.localizationOp B.omegaVolume w) := by
  unfold NaturalConeVolumeBridge.localizedExpectation
  exact B.volumeState_eq_vacuumRealState
    (NaturalConeVolumeBridge.localizationOp B.omegaVolume w)

/--
The finite Wigner--Jones atom filtration has total unit Hestenes vacuum volume.

This is the same theorem as `NaturalConeVolumeBridge.total_expectation_is_unity`,
read through the Hestenes/Krein vacuum state.
-/
@[rep_depth krein]
theorem total_wignerJones_vacuumExpectation_is_unity :
    (∑ w : Word,
      B.vacuum.vacuumRealState
        (NaturalConeVolumeBridge.wignerJonesAtom B.omegaVolume w)) = 1 := by
  calc
    (∑ w : Word,
      B.vacuum.vacuumRealState
        (NaturalConeVolumeBridge.wignerJonesAtom B.omegaVolume w))
        =
      ∑ w : Word, NaturalConeVolumeBridge.atomExpectation B.omegaVolume w := by
        exact Finset.sum_congr rfl
          (fun w _ => (B.atomExpectation_eq_vacuumRealState w).symm)
    _ = 1 := NaturalConeVolumeBridge.total_expectation_is_unity B.omegaVolume

/--
The Type-III atom log-volume potential is the negative logarithm of the
Hestenes vacuum expectation of the corresponding Wigner--Jones atom.
-/
@[rep_depth krein]
theorem modularVolumePotential_eq_neg_log_vacuumRealState
    (w : Word) :
    NaturalConeVolumeBridge.modularVolumePotential B.omegaVolume w =
      -Real.log
        (B.vacuum.vacuumRealState
          (NaturalConeVolumeBridge.wignerJonesAtom B.omegaVolume w)) := by
  calc
    NaturalConeVolumeBridge.modularVolumePotential B.omegaVolume w
        = -Real.log (NaturalConeVolumeBridge.atomExpectation B.omegaVolume w) :=
          NaturalConeVolumeBridge.modularVolumePotential_eq_neg_log_atomExpectation
            B.omegaVolume w
    _ =
      -Real.log
        (B.vacuum.vacuumRealState
          (NaturalConeVolumeBridge.wignerJonesAtom B.omegaVolume w)) := by
          rw [B.atomExpectation_eq_vacuumRealState w]

/--
The Type-III log-volume increment is the negative logarithm of the ratio of
Hestenes vacuum expectations on child and parent Wigner--Jones atoms.
-/
@[rep_depth krein]
theorem modularVolumeIncrement_eq_neg_log_vacuumRealState_ratio
    (parent child : Word) :
    NaturalConeVolumeBridge.modularVolumeIncrement B.omegaVolume parent child =
      -Real.log
        (B.vacuum.vacuumRealState
            (NaturalConeVolumeBridge.wignerJonesAtom B.omegaVolume child) /
          B.vacuum.vacuumRealState
            (NaturalConeVolumeBridge.wignerJonesAtom B.omegaVolume parent)) := by
  calc
    NaturalConeVolumeBridge.modularVolumeIncrement B.omegaVolume parent child
        =
      -Real.log
        (NaturalConeVolumeBridge.atomExpectation B.omegaVolume child /
          NaturalConeVolumeBridge.atomExpectation B.omegaVolume parent) :=
          NaturalConeVolumeBridge.modularVolumeIncrement_eq_neg_log_ratio
            B.omegaVolume parent child
    _ =
      -Real.log
        (B.vacuum.vacuumRealState
            (NaturalConeVolumeBridge.wignerJonesAtom B.omegaVolume child) /
          B.vacuum.vacuumRealState
            (NaturalConeVolumeBridge.wignerJonesAtom B.omegaVolume parent)) := by
          rw [B.atomExpectation_eq_vacuumRealState child,
            B.atomExpectation_eq_vacuumRealState parent]

end HestenesJonesFiltrationBridge

end Core

end InfoGeometry.Krein.HestenesJonesFiltrationBridge
