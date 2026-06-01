import InfoGeometry.Krein.BoundedKMSHestenesMoebiusClosureBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace BigOperators

noncomputable section

/-!
# InfoGeometry.Krein.BoundedKMSHestenesPhaseVolume

Phase-volume/determinant-channel adapter for the bounded KMS/Hestenes lane.

The determinant data is deliberately not a ring homomorphism out of operators.
The multiplicative determinant channel is carried only on units, while the
general operator phase-volume is a supplied readout with explicit invariance
witnesses.
-/

namespace InfoGeometry.Krein.BoundedKMSHestenesPhaseVolume

open InfoGeometry.Krein.BoundedKMSHestenesMoebiusClosureBridge
open InfoGeometry.Krein.HestenesMoebiusClosureBridge
open InfoGeometry.Krein.BoundedKMSHestenesConnesWilsonBridge
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
Bounded KMS Hestenes phase-volume socket.

`detUnits` is the multiplicative determinant/phase-volume channel on invertible
operators.  `phaseVolume` is the general readout used on arbitrary bounded
operators.  Its invariance under modular time and Möbius reparameterization is
supplied as model data, not derived from Type-III structure.
-/
@[rep_depth krein]
structure BoundedKMSHestenesPhaseVolumeBridge
    (Word : Type*) [Fintype Word] [DecidableEq Word] where
  /-- Bounded KMS/Hestenes/Möbius owner. -/
  boundedMoebius :
    BoundedKMSHestenesMoebiusClosureBridge
      (E := E) (LieAlgebra := LieAlgebra) Word

  /-- General phase-volume readout on bounded doubled-space operators. -/
  phaseVolume : EndH → ℝ

  /-- Multiplicative determinant channel on invertible operators only. -/
  detUnits : Units EndH →* ℝˣ

  /-- On units, the phase-volume readout agrees with the determinant channel. -/
  phaseVolume_eq_detUnits_on_units :
    ∀ U : Units EndH, phaseVolume (U : EndH) = (detUnits U : ℝ)

  /-- Modular/Hestenes flow preserves the supplied phase-volume readout. -/
  phaseVolume_modularFlow_invariant :
    ∀ (t : ℝ) (A : EndH),
      phaseVolume
          (boundedMoebius.boundedWilson.boundedVacuum.boundedHestenes.hestenes.modularFlow.flow t A) =
        phaseVolume A

  /-- Möbius operator action preserves the supplied phase-volume readout. -/
  phaseVolume_moebius_invariant :
    ∀ (g : MoebiusParameter) (A : EndH),
      phaseVolume (boundedMoebius.operatorAction g A) = phaseVolume A

  /-- Calibration to the existing Ω-volume state readout. -/
  phaseVolume_eq_volumeState :
    ∀ A : EndH,
      phaseVolume A =
        boundedMoebius.boundedWilson.toHestenesConnesWilsonBridge.volume.volumeState A


namespace BoundedKMSHestenesPhaseVolumeBridge

variable {Word : Type*}
variable [Fintype Word] [DecidableEq Word]
variable (B : BoundedKMSHestenesPhaseVolumeBridge
  (E := E) (LieAlgebra := LieAlgebra) Word)

/-- Multiplicativity is only asserted on units. -/
@[rep_depth operator]
theorem detUnits_mul
    (U V : Units EndH) :
    B.detUnits (U * V) = B.detUnits U * B.detUnits V :=
  map_mul B.detUnits U V

/-- The determinant channel sends the unit operator to unit scalar volume. -/
@[rep_depth operator]
theorem detUnits_one :
    B.detUnits (1 : Units EndH) = 1 :=
  map_one B.detUnits

/-- On invertible operators, phase-volume reads back through `detUnits`. -/
@[rep_depth operator]
theorem phaseVolume_unit_readback
    (U : Units EndH) :
    B.phaseVolume (U : EndH) = (B.detUnits U : ℝ) :=
  B.phaseVolume_eq_detUnits_on_units U

/-- Multiplicative phase-volume readback on invertible products. -/
@[rep_depth operator]
theorem phaseVolume_unit_mul_readback
    (U V : Units EndH) :
    B.phaseVolume ((U * V : Units EndH) : EndH) =
      ((B.detUnits U * B.detUnits V : ℝˣ) : ℝ) := by
  calc
    B.phaseVolume ((U * V : Units EndH) : EndH)
        = (B.detUnits (U * V) : ℝ) :=
            B.phaseVolume_eq_detUnits_on_units (U * V)
    _ = ((B.detUnits U * B.detUnits V : ℝˣ) : ℝ) := by
          rw [map_mul]

/-- The phase-volume of the invertible unit is normalized. -/
@[rep_depth operator]
theorem phaseVolume_unit_one :
    B.phaseVolume ((1 : Units EndH) : EndH) = 1 := by
  calc
    B.phaseVolume ((1 : Units EndH) : EndH)
        = (B.detUnits (1 : Units EndH) : ℝ) :=
            B.phaseVolume_eq_detUnits_on_units 1
    _ = 1 := by simp

/-- Modular/Hestenes flow preserves the calibrated phase-volume readout. -/
@[rep_depth thermo]
theorem phaseVolume_modularFlow_invariant_apply
    (t : ℝ) (A : EndH) :
    B.phaseVolume
        (B.boundedMoebius.boundedWilson.boundedVacuum.boundedHestenes.hestenes.modularFlow.flow t A) =
      B.phaseVolume A :=
  B.phaseVolume_modularFlow_invariant t A

/-- Möbius reparameterization preserves the calibrated phase-volume readout. -/
@[rep_depth projective]
theorem phaseVolume_moebius_invariant_apply
    (g : MoebiusParameter) (A : EndH) :
    B.phaseVolume (B.boundedMoebius.operatorAction g A) =
      B.phaseVolume A :=
  B.phaseVolume_moebius_invariant g A

/-- The phase-volume channel is calibrated to the existing Ω-volume state. -/
@[rep_depth krein]
theorem phaseVolume_eq_volumeState_apply
    (A : EndH) :
    B.phaseVolume A =
      B.boundedMoebius.boundedWilson.toHestenesConnesWilsonBridge.volume.volumeState A :=
  B.phaseVolume_eq_volumeState A

/-- Wigner--Jones atom phase-volume equals the installed atom expectation. -/
@[rep_depth projective]
theorem phaseVolume_wignerJonesAtom
    (w : Word) :
    B.phaseVolume
        (NaturalConeVolumeBridge.wignerJonesAtom
          B.boundedMoebius.boundedWilson.toHestenesConnesWilsonBridge.volume w) =
      NaturalConeVolumeBridge.atomExpectation
        B.boundedMoebius.boundedWilson.toHestenesConnesWilsonBridge.volume w := by
  unfold NaturalConeVolumeBridge.atomExpectation
  rw [B.phaseVolume_eq_volumeState_apply]

/--
Wilson holonomy as the negative logarithmic ratio of calibrated phase-volumes
on Wigner--Jones atoms.
-/
@[rep_depth projective]
theorem wilsonHolonomy_eq_neg_log_phaseVolume_ratio
    (parent child : Word) :
    B.boundedMoebius.boundedWilson.wilsonHolonomy parent child =
      -Real.log
        (B.phaseVolume
            (NaturalConeVolumeBridge.wignerJonesAtom
              B.boundedMoebius.boundedWilson.toHestenesConnesWilsonBridge.volume child) /
          B.phaseVolume
            (NaturalConeVolumeBridge.wignerJonesAtom
              B.boundedMoebius.boundedWilson.toHestenesConnesWilsonBridge.volume parent)) := by
  calc
    B.boundedMoebius.boundedWilson.wilsonHolonomy parent child
        =
      -Real.log
        (NaturalConeVolumeBridge.atomExpectation
            B.boundedMoebius.boundedWilson.toHestenesConnesWilsonBridge.volume child /
          NaturalConeVolumeBridge.atomExpectation
            B.boundedMoebius.boundedWilson.toHestenesConnesWilsonBridge.volume parent) :=
        B.boundedMoebius.boundedWilson.wilsonHolonomy_eq_neg_log_ratio parent child
    _ =
      -Real.log
        (B.phaseVolume
            (NaturalConeVolumeBridge.wignerJonesAtom
              B.boundedMoebius.boundedWilson.toHestenesConnesWilsonBridge.volume child) /
          B.phaseVolume
            (NaturalConeVolumeBridge.wignerJonesAtom
              B.boundedMoebius.boundedWilson.toHestenesConnesWilsonBridge.volume parent)) := by
        unfold NaturalConeVolumeBridge.atomExpectation
        rw [B.phaseVolume_eq_volumeState_apply,
          B.phaseVolume_eq_volumeState_apply]

end BoundedKMSHestenesPhaseVolumeBridge

end Core

end InfoGeometry.Krein.BoundedKMSHestenesPhaseVolume
