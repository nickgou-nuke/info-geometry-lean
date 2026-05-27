import InfoGeometry.Krein.HestenesKreinVacuumBridge
import InfoGeometry.Canonical.StandardFormOmegaVolumeBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace BigOperators

noncomputable section

set_option linter.dupNamespace false

/-!
# InfoGeometry.Krein.HestenesConnesWilsonBridge

Connes--Wilson readback for the Hestenes--Krein detailed-balance lane.

This file is deliberately a thin calibration socket.  It does not construct a
new noncommutative differential calculus, a Connes 2-cycle complex, or a global
Type-III determinant.  Instead it identifies three already theorem-safe
surfaces:

* the real Hestenes KMS boundary `φ(A σ_β(B)) = φ(BA)`;
* the Ω-expectation atom weights from `StandardFormOmegaVolumeBridge`;
* the projective logarithmic Radon--Nikodym increment
  `-log(ωΩ(p_child) / ωΩ(p_parent))`.

The Wilson holonomy is supplied as a bounded readout and calibrated to that
projective log increment.  Hence Weyl gauge invariance is inherited from the
existing cylinder-log theorem, rather than asserted for arbitrary operators.
-/

namespace InfoGeometry.Krein.HestenesConnesWilsonBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.HestenesModularKMSBridge
open InfoGeometry.Krein.HestenesKreinVacuumBridge
open InfoGeometry.Canonical.StandardFormOmegaVolumeBridge
open InfoGeometry.Canonical.ModularCartanCantorSystem

/--
Abstract Connes--Wilson holonomy carrier.

`Loop` is the loop, 2-cycle, or horizon holonomy carrier.
`Obj` is the operator, sector, cone-face, or cylinder object being compared.

No Connes-cycle theorem is asserted here.  This is only the projective
calibration surface used by concrete Hestenes/Krein and Cantor instances.
-/
@[rep_depth thermo]
structure ConnesWilsonCarrier
    (Obj Loop : Type*) where
  /-- Build the loop/cycle associated to a pair of local sectors/operators. -/
  loopOfPair : Obj → Obj → Loop

  /-- Wilson holonomy readout. -/
  wilsonLoop : Loop → ℝ

  /-- Logarithmic Radon--Nikodym / modular log-increment readout. -/
  radonNikodymLog : Obj → Obj → ℝ

  /-- Projective/Weyl scaling action on the compared objects. -/
  scale : ℝ → Obj → Obj

/--
Calibration predicate: Wilson holonomy equals the logarithmic
Radon--Nikodym increment for the loop associated to a pair.
-/
def IsWilsonRadonNikodymCalibrated
    {Obj Loop : Type*}
    (B : ConnesWilsonCarrier Obj Loop) : Prop :=
  ∀ A C,
    B.wilsonLoop (B.loopOfPair A C) =
      B.radonNikodymLog A C

/--
Predicate: the logarithmic RN increment is invariant under common positive
Weyl rescaling.

This is the abstract socket for the concrete identity
`log ((c * x) / (c * y)) = log (x / y)` with `c > 0`.
-/
def IsRNLogCommonPositiveScaleInvariant
    {Obj Loop : Type*}
    (B : ConnesWilsonCarrier Obj Loop) : Prop :=
  ∀ (c : ℝ) (A C : Obj), 0 < c →
    B.radonNikodymLog (B.scale c A) (B.scale c C) =
      B.radonNikodymLog A C

namespace ConnesWilsonCarrier

variable {Obj Loop : Type*}
variable (B : ConnesWilsonCarrier Obj Loop)

/--
If Wilson holonomy is calibrated by RN log-increment, and the RN log-increment
is invariant under common positive Weyl scaling, then the Wilson holonomy is
also Weyl invariant.
-/
@[rep_depth thermo]
theorem wilson_loop_common_positive_scale_invariant
    (hCal : IsWilsonRadonNikodymCalibrated B)
    (hRN : IsRNLogCommonPositiveScaleInvariant B)
    (c : ℝ) (A C : Obj) (hc : 0 < c) :
    B.wilsonLoop (B.loopOfPair (B.scale c A) (B.scale c C)) =
      B.wilsonLoop (B.loopOfPair A C) := by
  calc
    B.wilsonLoop (B.loopOfPair (B.scale c A) (B.scale c C))
        = B.radonNikodymLog (B.scale c A) (B.scale c C) := by
            exact hCal (B.scale c A) (B.scale c C)
    _ = B.radonNikodymLog A C := by
            exact hRN c A C hc
    _ = B.wilsonLoop (B.loopOfPair A C) := by
            exact (hCal A C).symm

end ConnesWilsonCarrier

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance hestenesConnesWilsonNormedRing : NormedRing EndH :=
  inferInstance
noncomputable local instance hestenesConnesWilsonNormedAlgebra : NormedAlgebra ℝ EndH :=
  inferInstance
noncomputable local instance hestenesConnesWilsonNormedAlgebraRat : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance hestenesConnesWilsonTopologicalRing : IsTopologicalRing EndH :=
  inferInstance
local instance hestenesConnesWilsonCompleteSpace : CompleteSpace EndH :=
  inferInstance
local instance hestenesConnesWilsonSMulCommClass : SMulCommClass ℝ EndH EndH :=
  inferInstance
local instance hestenesConnesWilsonIsScalarTower : IsScalarTower ℝ EndH EndH :=
  inferInstance

/--
Hestenes--Connes--Wilson calibration bridge.

`Word` indexes the finite cylinder/Jones atom layer.  A concrete Cantor/Jones
model can instantiate it by binary words at a fixed depth.  This bridge only
requires a finite atom partition supplied by `StandardFormOmegaVolumeBridge`.
-/
@[rep_depth krein]
structure HestenesConnesWilsonBridge
    (Word : Type*) [Fintype Word] [DecidableEq Word] where
  /-- Real Hestenes KMS packet on the doubled carrier. -/
  kmsPacket : HestenesKreinKMSPacket (E := H₂)

  /-- Inverse temperature for the real Hestenes KMS boundary. -/
  beta : ℝ

  /-- Real state/readout used by the Hestenes KMS socket. -/
  realState : EndH → ℝ

  /-- Real KMS/detailed-balance boundary for the supplied readout. -/
  real_kms_boundary : kmsPacket.IsHestenesKMSCondition beta realState

  /-- Vacuum vector packet for the KMS readout. -/
  vacuum : HestenesKreinVacuum (E := H₂) kmsPacket

  /-- Ω-expectation finite atom volume bridge. -/
  volume : NaturalConeVolumeBridge (H := E) Word

  /-- The Ω used by the volume bridge is the vacuum vector used by the KMS packet. -/
  volume_omega_eq_vacuum : volume.Omega = vacuum.omega

  /-- The real KMS readout is the same normalized Ω-volume state. -/
  realState_eq_volumeState : ∀ A : EndH, realState A = volume.volumeState A

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

namespace HestenesConnesWilsonBridge

variable {Word : Type*}
variable [Fintype Word] [DecidableEq Word]
variable (W : HestenesConnesWilsonBridge (E := E) Word)

/-- The volume state is the vacuum real state attached to the same `Ω`. -/
@[rep_depth krein]
theorem volumeState_eq_vacuumRealState (A : EndH) :
    W.volume.volumeState A = W.vacuum.vacuumRealState A := by
  rw [W.volume.volumeState_eq_omega_kreinExpectation]
  unfold HestenesKreinVacuum.vacuumRealState
  unfold HestenesKreinKMSPacket.hestenesExpectation
  rw [W.volume_omega_eq_vacuum]

/-- The real KMS readout is the vacuum real state. -/
@[rep_depth krein]
theorem realState_eq_vacuumRealState (A : EndH) :
    W.realState A = W.vacuum.vacuumRealState A := by
  rw [W.realState_eq_volumeState A]
  exact W.volumeState_eq_vacuumRealState A

/-- Detailed balance in the normalized Ω-volume state. -/
@[rep_depth krein]
theorem volumeState_detailedBalance (A B : EndH) :
    W.volume.volumeState (A * W.kmsPacket.modularFlow.flow W.beta B) =
      W.volume.volumeState (B * A) := by
  calc
    W.volume.volumeState (A * W.kmsPacket.modularFlow.flow W.beta B)
        = W.realState (A * W.kmsPacket.modularFlow.flow W.beta B) := by
            exact (W.realState_eq_volumeState
              (A * W.kmsPacket.modularFlow.flow W.beta B)).symm
    _ = W.realState (B * A) := by
            exact W.real_kms_boundary A B
    _ = W.volume.volumeState (B * A) :=
            W.realState_eq_volumeState (B * A)

/-- Detailed balance in the explicit Hestenes--Krein vacuum expectation. -/
@[rep_depth krein]
theorem vacuumRealState_detailedBalance (A B : EndH) :
    W.vacuum.vacuumRealState
        (A * W.kmsPacket.modularFlow.flow W.beta B) =
      W.vacuum.vacuumRealState (B * A) := by
  calc
    W.vacuum.vacuumRealState
        (A * W.kmsPacket.modularFlow.flow W.beta B)
        = W.volume.volumeState
            (A * W.kmsPacket.modularFlow.flow W.beta B) := by
            exact (W.volumeState_eq_vacuumRealState
              (A * W.kmsPacket.modularFlow.flow W.beta B)).symm
    _ = W.volume.volumeState (B * A) :=
            W.volumeState_detailedBalance A B
    _ = W.vacuum.vacuumRealState (B * A) :=
            W.volumeState_eq_vacuumRealState (B * A)

/-- Wilson holonomy readback through the Ω-volume modular log increment. -/
@[rep_depth projective]
theorem wilsonHolonomy_eq_modularVolumeIncrement
    (parent child : Word) :
    W.wilsonHolonomy parent child =
      NaturalConeVolumeBridge.modularVolumeIncrement W.volume parent child := by
  calc
    W.wilsonHolonomy parent child
        = W.radonNikodymLog parent child :=
            W.wilsonHolonomy_eq_radonNikodymLog parent child
    _ = NaturalConeVolumeBridge.modularVolumeIncrement W.volume parent child :=
            W.radonNikodymLog_eq_modularVolumeIncrement parent child

/-- Radon--Nikodym logarithmic readback as `-log(ωΩ(child)/ωΩ(parent))`. -/
@[rep_depth projective]
theorem radonNikodymLog_eq_neg_log_ratio
    (parent child : Word) :
    W.radonNikodymLog parent child =
      -Real.log
        (NaturalConeVolumeBridge.atomExpectation W.volume child /
          NaturalConeVolumeBridge.atomExpectation W.volume parent) := by
  calc
    W.radonNikodymLog parent child
        = NaturalConeVolumeBridge.modularVolumeIncrement W.volume parent child :=
            W.radonNikodymLog_eq_modularVolumeIncrement parent child
    _ = -Real.log
          (NaturalConeVolumeBridge.atomExpectation W.volume child /
            NaturalConeVolumeBridge.atomExpectation W.volume parent) :=
            NaturalConeVolumeBridge.modularVolumeIncrement_eq_neg_log_ratio
              W.volume parent child

/-- Wilson holonomy readback as the same projective logarithmic ratio. -/
@[rep_depth projective]
theorem wilsonHolonomy_eq_neg_log_ratio
    (parent child : Word) :
    W.wilsonHolonomy parent child =
      -Real.log
        (NaturalConeVolumeBridge.atomExpectation W.volume child /
          NaturalConeVolumeBridge.atomExpectation W.volume parent) := by
  calc
    W.wilsonHolonomy parent child
        = W.radonNikodymLog parent child :=
            W.wilsonHolonomy_eq_radonNikodymLog parent child
    _ = -Real.log
          (NaturalConeVolumeBridge.atomExpectation W.volume child /
            NaturalConeVolumeBridge.atomExpectation W.volume parent) :=
            W.radonNikodymLog_eq_neg_log_ratio parent child

/--
Projective Weyl gauge invariance of the RN logarithmic increment.

Common positive rescaling of all Ω-atom weights cancels before taking the log.
-/
@[rep_depth projective]
theorem radonNikodymLog_common_pos_smul
    (parent child : Word) {c : ℝ} (hc : 0 < c) :
    cylinderLogIncrement
        (fun w : Word => c * NaturalConeVolumeBridge.atomExpectation W.volume w)
        parent child =
      W.radonNikodymLog parent child := by
  calc
    cylinderLogIncrement
        (fun w : Word => c * NaturalConeVolumeBridge.atomExpectation W.volume w)
        parent child
        = NaturalConeVolumeBridge.modularVolumeIncrement W.volume parent child :=
            NaturalConeVolumeBridge.modularVolumeIncrement_common_pos_smul
              W.volume parent child hc
    _ = W.radonNikodymLog parent child :=
            (W.radonNikodymLog_eq_modularVolumeIncrement parent child).symm

/-- Projective Weyl gauge invariance of the calibrated Wilson holonomy. -/
@[rep_depth projective]
theorem wilsonHolonomy_common_pos_smul
    (parent child : Word) {c : ℝ} (hc : 0 < c) :
    cylinderLogIncrement
        (fun w : Word => c * NaturalConeVolumeBridge.atomExpectation W.volume w)
        parent child =
      W.wilsonHolonomy parent child := by
  calc
    cylinderLogIncrement
        (fun w : Word => c * NaturalConeVolumeBridge.atomExpectation W.volume w)
        parent child
        = W.radonNikodymLog parent child :=
            W.radonNikodymLog_common_pos_smul parent child hc
    _ = W.wilsonHolonomy parent child :=
            (W.wilsonHolonomy_eq_radonNikodymLog parent child).symm

/--
Alias for the Connes--Wilson Weyl-gauge invariance readback.

This is the theorem-safe form of Wilson-loop gauge invariance in this file:
the loop is indexed by finite Ω-atom transitions, and common positive
rescaling of all atom weights cancels in the logarithmic RN increment.  No
claim is made for arbitrary `EndH → EndH → ℝ` Radon--Nikodym logs.
-/
@[rep_depth projective]
theorem wilson_loop_weyl_gauge_invariant
    (parent child : Word) {c : ℝ} (hc : 0 < c) :
    cylinderLogIncrement
        (fun w : Word => c * NaturalConeVolumeBridge.atomExpectation W.volume w)
        parent child =
      W.wilsonHolonomy parent child :=
  W.wilsonHolonomy_common_pos_smul parent child hc

/--
Alias for projective Weyl-gauge invariance of the calibrated
Radon--Nikodym logarithmic increment.
-/
@[rep_depth projective]
theorem radon_nikodym_log_weyl_gauge_invariant
    (parent child : Word) {c : ℝ} (hc : 0 < c) :
    cylinderLogIncrement
        (fun w : Word => c * NaturalConeVolumeBridge.atomExpectation W.volume w)
        parent child =
      W.radonNikodymLog parent child :=
  W.radonNikodymLog_common_pos_smul parent child hc

/-- The finite atom expectation partition still has total unit volume. -/
@[rep_depth operator]
theorem total_wilson_atom_volume_is_unity :
    (∑ w : Word, NaturalConeVolumeBridge.atomExpectation W.volume w) = 1 :=
  NaturalConeVolumeBridge.total_expectation_is_unity W.volume

end HestenesConnesWilsonBridge

end Core

end InfoGeometry.Krein.HestenesConnesWilsonBridge
