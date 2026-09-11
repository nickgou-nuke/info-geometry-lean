import InfoGeometry.Krein.BoundedKMSHestenesVacuumBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.HestenesConnesWilsonBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace BigOperators

noncomputable section

/-!
# InfoGeometry.Krein.BoundedKMSHestenesConnesWilsonBridge

Adapter from the bounded KMS/Hestenes/vacuum lane to the existing
Hestenes--Connes--Wilson Ω-volume owner.

The file does not introduce a new Wilson calculus.  It packages the remaining
identifications needed to instantiate `HestenesConnesWilsonBridge` from the
bounded KMS state-functional pipeline.
-/

namespace InfoGeometry.Krein.BoundedKMSHestenesConnesWilson

open InfoGeometry.Krein.BoundedKMSHestenesVacuum
open InfoGeometry.Krein.HestenesConnesWilsonBridge
open InfoGeometry.Canonical.StandardFormOmegaVolumeBridge

section Core

variable {E LieAlgebra : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH :=
  inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH :=
  inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH :=
  inferInstance
local instance : CompleteSpace EndH :=
  inferInstance
local instance : SMulCommClass ℝ EndH EndH :=
  inferInstance
local instance : IsScalarTower ℝ EndH EndH :=
  inferInstance

/--
Bounded KMS Hestenes--Connes--Wilson adapter.

`boundedVacuum` supplies the bounded KMS real state and the Hestenes vacuum
vector.  `volume` supplies the standard-form finite Ω-volume atom layer.
The remaining fields calibrate the two Ω/readout surfaces and the Wilson/RN
logarithmic holonomy data.
-/
@[rep_depth krein]
structure BoundedKMSHestenesConnesWilsonBridge
    (Word : Type*) [Fintype Word] [DecidableEq Word] where
  /-- Bounded KMS state-functional lane translated to a Hestenes vacuum vector. -/
  boundedVacuum :
    BoundedKMSHestenesVacuumBridge (E := H₂) (LieAlgebra := LieAlgebra)

  /-- Standard-form Ω-volume atom bridge. -/
  volume :
    NaturalConeVolumeBridge (H := E) Word

  /-- The Ω used by the volume bridge is the Hestenes/Krein vacuum vector. -/
  volume_omega_eq_vacuum :
    volume.Omega = boundedVacuum.vacuum.omega

  /-- The bounded real KMS readout is the normalized Ω-volume state. -/
  boundedRealState_eq_volumeState :
    ∀ A : EndH,
      boundedVacuum.boundedHestenes.realState A = volume.volumeState A

  /-- Wilson holonomy readout on parent/child atom transitions. -/
  wilsonHolonomy : Word → Word → ℝ

  /-- Projective logarithmic Radon--Nikodym increment readout. -/
  radonNikodymLog : Word → Word → ℝ

  /-- Wilson holonomy is calibrated to the logarithmic RN increment. -/
  wilsonHolonomy_eq_radonNikodymLog :
    ∀ parent child : Word,
      wilsonHolonomy parent child = radonNikodymLog parent child

  /-- The logarithmic RN increment is the Ω-volume modular log increment. -/
  radonNikodymLog_eq_modularVolumeIncrement :
    ∀ parent child : Word,
      radonNikodymLog parent child =
        NaturalConeVolumeBridge.modularVolumeIncrement volume parent child

namespace BoundedKMSHestenesConnesWilsonBridge

variable {Word : Type*}
variable [Fintype Word] [DecidableEq Word]
variable (B : BoundedKMSHestenesConnesWilsonBridge
  (E := E) (LieAlgebra := LieAlgebra) Word)

/-- The installed Hestenes--Connes--Wilson owner induced by the bounded KMS lane. -/
@[rep_depth krein]
def toHestenesConnesWilsonBridge :
    _root_.InfoGeometry.Krein.HestenesConnesWilsonBridge.Bridge (E := E) Word where
  kmsPacket := B.boundedVacuum.boundedHestenes.hestenes
  beta := B.boundedVacuum.boundedHestenes.boundedKMS.beta
  realState := B.boundedVacuum.boundedHestenes.realState
  real_kms_boundary := B.boundedVacuum.boundedHestenes.hestenesKMS
  vacuum := B.boundedVacuum.vacuum
  volume := B.volume
  volume_omega_eq_vacuum := B.volume_omega_eq_vacuum
  realState_eq_volumeState := B.boundedRealState_eq_volumeState
  wilsonHolonomy := B.wilsonHolonomy
  radonNikodymLog := B.radonNikodymLog
  wilsonHolonomy_eq_radonNikodymLog := B.wilsonHolonomy_eq_radonNikodymLog
  radonNikodymLog_eq_modularVolumeIncrement :=
    B.radonNikodymLog_eq_modularVolumeIncrement

/-- Readback: the induced Connes--Wilson real state is the bounded real state. -/
@[rep_depth krein]
theorem connesWilson_realState_eq_boundedRealState
    (A : EndH) :
    B.toHestenesConnesWilsonBridge.realState A =
      B.boundedVacuum.boundedHestenes.realState A :=
  rfl

/-- Readback: the induced Connes--Wilson volume owner is the supplied volume owner. -/
@[rep_depth krein]
theorem connesWilson_volume_eq :
    B.toHestenesConnesWilsonBridge.volume = B.volume :=
  rfl

/-- The bounded real KMS readout is the normalized Ω-volume state. -/
@[rep_depth krein]
theorem boundedRealState_eq_volumeState_apply
    (A : EndH) :
    B.boundedVacuum.boundedHestenes.realState A =
      B.volume.volumeState A :=
  B.boundedRealState_eq_volumeState A

/-- The bounded real KMS readout is the Hestenes/Krein vacuum state. -/
@[rep_depth krein]
theorem boundedRealState_eq_vacuumRealState
    (A : EndH) :
    B.boundedVacuum.boundedHestenes.realState A =
      B.boundedVacuum.vacuum.vacuumRealState A :=
  B.boundedVacuum.realState_eq_vacuumRealState_apply A

/-- The Ω-volume state is the Hestenes/Krein vacuum state. -/
@[rep_depth krein]
theorem volumeState_eq_vacuumRealState
    (A : EndH) :
    B.volume.volumeState A =
      B.boundedVacuum.vacuum.vacuumRealState A := by
  calc
    B.volume.volumeState A
        = B.boundedVacuum.boundedHestenes.realState A := by
            rw [B.boundedRealState_eq_volumeState_apply A]
    _ = B.boundedVacuum.vacuum.vacuumRealState A :=
            B.boundedRealState_eq_vacuumRealState A

/-- Detailed balance in the Ω-volume state, routed through the induced owner. -/
@[rep_depth krein]
theorem volumeState_detailedBalance
    (A C : EndH) :
    B.volume.volumeState
        (A * B.boundedVacuum.boundedHestenes.hestenes.modularFlow.flow
          B.boundedVacuum.boundedHestenes.boundedKMS.beta C) =
      B.volume.volumeState (C * A) :=
  B.toHestenesConnesWilsonBridge.volumeState_detailedBalance A C

/-- Wilson holonomy readback through the Ω-volume modular log increment. -/
@[rep_depth projective]
theorem wilsonHolonomy_eq_modularVolumeIncrement
    (parent child : Word) :
    B.wilsonHolonomy parent child =
      NaturalConeVolumeBridge.modularVolumeIncrement B.volume parent child :=
  B.toHestenesConnesWilsonBridge.wilsonHolonomy_eq_modularVolumeIncrement
    parent child

/-- Wilson holonomy as the projective logarithmic ratio of Ω-atom weights. -/
@[rep_depth projective]
theorem wilsonHolonomy_eq_neg_log_ratio
    (parent child : Word) :
    B.wilsonHolonomy parent child =
      -Real.log
        (NaturalConeVolumeBridge.atomExpectation B.volume child /
          NaturalConeVolumeBridge.atomExpectation B.volume parent) :=
  B.toHestenesConnesWilsonBridge.wilsonHolonomy_eq_neg_log_ratio parent child

end BoundedKMSHestenesConnesWilsonBridge

end Core

end InfoGeometry.Krein.BoundedKMSHestenesConnesWilson
