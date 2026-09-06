import InfoGeometry.Canonical.SpectroscopicGaugeKMSBridge
import InfoGeometry.Canonical.ModularSourceBridge
import InfoGeometry.Canonical.OnsagerReciprocity
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Dynamics.UnruhKMS
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SpectroscopicGauge

Spectroscopic-gauge scaffold for repo-native measurement relativity:

- downstream compatibility with the owned Unruh KMS lane,
- compatible lane-local response datum (`PotentialDatum`),
- a chiral analyzer/projector,
- a probing perturbation channel,
- symmetric/skew measured packets via existing Onsager response lanes,
- obstruction readout as analyzer-observable commutator.

This file is a translator/coherence surface; it does not introduce a new KMS
owner for thermodynamics.
-/

namespace InfoGeometry.Canonical.SpectroscopicGauge

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.OnsagerReciprocity
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.SpectroscopicGaugeKMSBridge
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
Spectroscopic gauge package for one measurement channel.

`kmsCompat` keeps compatibility with the owned Unruh KMS lane.
`datum` keeps compatibility with the existing Onsager response lane.
-/
@[rep_depth transport]
structure SpectroscopicGaugeData where
  kmsCompat : SpectroscopicKMSCompatible (E := E)
  datum : PotentialDatum (E := E)
  probe_eq_referenceState : datum.probe = kmsCompat.state
  chiralAnalyzer : EndH
  isProjector : chiralAnalyzer * chiralAnalyzer = chiralAnalyzer
  probingChannel : EndH

/-- The reference-state functional used by the spectroscopic gauge. -/
@[rep_depth transport]
noncomputable def referenceState
    (gauge : SpectroscopicGaugeData (E := E)) : EndH →L[ℝ] ℝ :=
  gauge.kmsCompat.state

/-- Inverse temperature carried by the owned-KMS-compatible reference package. -/
@[rep_depth transport]
noncomputable def inverseTemperature
    (gauge : SpectroscopicGaugeData (E := E)) : ℝ :=
  gauge.kmsCompat.inverseTemperature

@[rep_depth transport, simp]
theorem referenceState_eq_probe
    (gauge : SpectroscopicGaugeData (E := E)) :
    referenceState (E := E) gauge = gauge.datum.probe := by
  simpa [referenceState] using gauge.probe_eq_referenceState.symm

/--
The gauge reference-state satisfies the KMS-like identity for the owned Unruh
modular Hamiltonian lane at the packaged inverse temperature.
-/
@[rep_depth transport]
theorem referenceState_owned_unruh_kms_identity
    (gauge : SpectroscopicGaugeData (E := E))
    (A B : EndH) :
    referenceState (E := E) gauge
      (A * modular_shift
        (E := E)
        (InfoGeometry.Dynamics.modularHamiltonian (E := E))
        (inverseTemperature (E := E) gauge) B)
      =
    referenceState (E := E) gauge (B * A) := by
  simpa [referenceState, inverseTemperature] using
    (gauge.kmsCompat.kms_identity A B)

/-- Symmetric/skew cross-channel response packet at a fixed observable. -/
@[rep_depth transport]
noncomputable def measuredCrossPacket
    (gauge : SpectroscopicGaugeData (E := E))
    (left right observable : EndH) : ℝ × ℝ :=
  ( responseCoefficient (E := E) gauge.datum left right observable
  , curvatureCoefficient (E := E) gauge.datum left right observable )

/-- One-channel measured packet (self-coupled probe). -/
@[rep_depth transport]
noncomputable def measuredSpectralPacket
    (gauge : SpectroscopicGaugeData (E := E))
    (observable : EndH) : ℝ × ℝ :=
  measuredCrossPacket (E := E) gauge gauge.probingChannel gauge.probingChannel observable

/-- Obstruction/leakage readout for analyzer-observable mismatch. -/
@[rep_depth transport]
noncomputable def gaugeObstruction
    (gauge : SpectroscopicGaugeData (E := E))
    (observable : EndH) : EndH :=
  gauge.chiralAnalyzer * observable - observable * gauge.chiralAnalyzer

@[rep_depth transport, simp]
theorem gaugeObstruction_eq_zero_of_commute
    (gauge : SpectroscopicGaugeData (E := E))
    (observable : EndH)
    (hcomm : Commute gauge.chiralAnalyzer observable) :
    gaugeObstruction (E := E) gauge observable = 0 := by
  unfold gaugeObstruction
  exact sub_eq_zero.mpr hcomm.eq

/-- Symmetric part is reciprocal; skew part flips sign under channel swap. -/
@[rep_depth transport]
theorem measuredCrossPacket_swap
    (gauge : SpectroscopicGaugeData (E := E))
    (left right observable : EndH) :
    measuredCrossPacket (E := E) gauge right left observable
      =
    ( (measuredCrossPacket (E := E) gauge left right observable).1
    , -(measuredCrossPacket (E := E) gauge left right observable).2 ) := by
  have hSymm :
      responseCoefficient (E := E) gauge.datum right left observable
        =
      responseCoefficient (E := E) gauge.datum left right observable := by
    simpa using
      (responseCoefficient_swap (E := E) gauge.datum right left observable)
  have hSkew :
      curvatureCoefficient (E := E) gauge.datum right left observable
        =
      -curvatureCoefficient (E := E) gauge.datum left right observable := by
    simpa using
      (curvatureCoefficient_swap_neg (E := E) gauge.datum left right observable)
  ext <;> simp [measuredCrossPacket, hSymm, hSkew]

/--
Relativity baseline: measured packets depend on datum/channel choice.
If those are unchanged, packet readout is unchanged.
-/
@[rep_depth transport]
theorem relativity_of_measurements_of_same_datum_and_probe
    (gauge₁ gauge₂ : SpectroscopicGaugeData (E := E))
    (observable : EndH)
    (hDatum : gauge₁.datum = gauge₂.datum)
    (hProbe : gauge₁.probingChannel = gauge₂.probingChannel) :
    measuredSpectralPacket (E := E) gauge₁ observable
      =
    measuredSpectralPacket (E := E) gauge₂ observable := by
  simp [measuredSpectralPacket, measuredCrossPacket, hDatum, hProbe]

/--
Difference packet between two gauges for the same observable.
This is the packaged "spectral shift" readout surface.
-/
@[rep_depth transport]
noncomputable def spectralPacketShift
    (gauge₁ gauge₂ : SpectroscopicGaugeData (E := E))
    (observable : EndH) : ℝ × ℝ :=
  let p₁ := measuredSpectralPacket (E := E) gauge₁ observable
  let p₂ := measuredSpectralPacket (E := E) gauge₂ observable
  (p₁.1 - p₂.1, p₁.2 - p₂.2)

@[rep_depth transport, simp]
theorem spectralPacketShift_eq_zero_of_same_datum_and_probe
    (gauge₁ gauge₂ : SpectroscopicGaugeData (E := E))
    (observable : EndH)
    (hDatum : gauge₁.datum = gauge₂.datum)
    (hProbe : gauge₁.probingChannel = gauge₂.probingChannel) :
    spectralPacketShift (E := E) gauge₁ gauge₂ observable = (0, 0) := by
  unfold spectralPacketShift
  rw [relativity_of_measurements_of_same_datum_and_probe (E := E) gauge₁ gauge₂ observable hDatum hProbe]
  simp

/--
Certified-kernel bridge:
if the gauge analyzer is the certified spectral projector, the gauge
obstruction of the certified metric projector is exactly the certified left
chiral anomaly.
-/
@[rep_depth transport]
theorem geometric_anomaly_is_gaugeObstruction
    (gauge : SpectroscopicGaugeData (E := E))
    (CIK : CertifiedInverseKernel H₂)
    (hAnalyzer : gauge.chiralAnalyzer = CIK.spectralProjector) :
    gaugeObstruction (E := E) gauge CIK.metricProjector = CIK.chiralAnomaly := by
  rw [gaugeObstruction, hAnalyzer]
  simp [CertifiedInverseKernel.chiralAnomaly,
    CertifiedInverseKernel.toInverseKernel', InverseKernel.chiralAnomaly]

end Core

end InfoGeometry.Canonical.SpectroscopicGauge
