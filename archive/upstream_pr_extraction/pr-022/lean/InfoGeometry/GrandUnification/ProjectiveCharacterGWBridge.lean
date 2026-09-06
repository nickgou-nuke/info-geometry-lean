import InfoGeometry.ErlangenLanglandsLane
import InfoGeometry.GromovWittenProjectiveLane
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.ModularVolumePotential
import Mathlib

noncomputable section

namespace InfoGeometry.GrandUnification

open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.GromovWittenProjectiveLane
open InfoGeometry.ModularVolumePotential

/--
Projective character / Gromov–Witten bridge.

This packet is intentionally thin and theorem-safe: it reuses existing lane
structures and records only the compatibility witnesses needed to connect:

* projective / equivariant geometry
* Souriau operatorial log-potential data
* modular-volume finite spectral normalization
* GW virtual-localization readout.
-/
structure ProjectiveCharacterGWBridgePacket
    (finiteSpectralIndex : Type*) [Fintype finiteSpectralIndex] where
  /-- Projective bundle data. -/
  projectiveSubstrate : ProjectiveBundlePacket
  /-- Virtual localization sector. -/
  gwLocalizationSector : GWVirtualLocalizationPacket
  /-- Quantum-metric control sector. -/
  quantumMetricOperatorSector : QuantumMetricOperatorPacket

  /-- Souriau carrier for logarithmic Radon–Nikodym data. -/
  souriauStateCarrier : Type*
  /-- Souriau log-density packet on the above carrier. -/
  souriauLogRadonNikodym :
    LogRadonNikodymData souriauStateCarrier

  /-- Operatorial exponential-family parameter/op carrier. -/
  souriauParameter : Type*
  /-- Operatorial exponential-family carrier. -/
  souriauOperatorCarrier : Type*
  /-- Operatorial exponential family on which partition readout lemmas apply. -/
  souriauExponentialFamily :
    OperatorialExponentialFamily souriauParameter souriauOperatorCarrier

  /-- Concrete finite spectral witness carried by the bridge packet. -/
  finiteSpectralPartition :
    FiniteSpectralBoltzmannPartition finiteSpectralIndex

  /-- Modular-volume bridge payload that is already theorem-safe per lane. -/
  modularVolumeBridge : ModularVolumeBridgePacket

/-- Projective character bridge target as explicit witness conjunction. -/
def ProjectiveCharacterGWBridgeTarget
    {S : Type*} [Fintype S] (_P : ProjectiveCharacterGWBridgePacket S) :
    Prop :=
  ModularVolumeBridgeTarget _P.modularVolumeBridge ∧
    FiniteSpectralThermodynamicNormalizationSchema S

/-- Constructor from explicit bridge payload data. -/
theorem constructProjectiveCharacterGWBridgeTarget
    {S : Type*} [Fintype S] (_P : ProjectiveCharacterGWBridgePacket S) :
    ProjectiveCharacterGWBridgeTarget _P := by
  exact
    ⟨ constructModularVolumeBridgeTarget _P.modularVolumeBridge
    , constructFiniteSpectralThermodynamicNormalizationSchema S ⟩

/--
Trace/KMS form of an untraced operatorial exponential family partition,
imported directly from the operatorial lane.
-/
theorem projectiveCharacter_partitionReadout_is_traceReadout
    (S : Type*) [Fintype S]
    (P : ProjectiveCharacterGWBridgePacket S) (β : P.souriauParameter) :
    P.souriauExponentialFamily.partitionFunction β =
      P.souriauExponentialFamily.traceReadout
        (P.souriauExponentialFamily.untracedExponential β) := by
  simpa using OperatorialExponentialFamily.partitionFunction_eq_trace_theorem
    (E := P.souriauExponentialFamily) β

/-- Log-partition is the logarithm of the trace/readout. -/
theorem projectiveCharacter_logPartition_is_log_trace
    (S : Type*) [Fintype S]
    (P : ProjectiveCharacterGWBridgePacket S) (β : P.souriauParameter) :
    P.souriauExponentialFamily.partitionPotential β =
      Real.log (P.souriauExponentialFamily.traceReadout
        (P.souriauExponentialFamily.untracedExponential β)) := by
  simpa using OperatorialExponentialFamily.partitionPotential_eq_log_trace_theorem
    (E := P.souriauExponentialFamily) β

/-- KL readout alias for the carried Souriau Radon–Nikodym packet. -/
theorem projectiveCharacter_kl_eq_expectation_logDensity
    (S : Type*) [Fintype S]
    (P : ProjectiveCharacterGWBridgePacket S) :
    P.souriauLogRadonNikodym.KL =
      P.souriauLogRadonNikodym.expectationNu P.souriauLogRadonNikodym.logDensity := by
  simpa using
    LogRadonNikodymData.KL_eq_expectation_logDensity (D := P.souriauLogRadonNikodym)

/-- Finite spectral normalization in the bridge spelling. -/
theorem projectiveCharacter_finiteSpectral_partitionNormalization
    (S : Type*) [Fintype S]
    (P : ProjectiveCharacterGWBridgePacket S) :
    P.finiteSpectralPartition.partition =
      ∑ s : S,
        Real.exp (-(P.finiteSpectralPartition.spectrum.inverseTemperature *
          P.finiteSpectralPartition.spectrum.spectralEnergy s)) *
            P.finiteSpectralPartition.spectrum.spectralVolume s := by
  simpa using
    finiteSpectralPartitionNormalization
      (S := S) P.finiteSpectralPartition

/-- Projective diagonal is documented as a shadow readout after diagonalization. -/
theorem finite_projective_shadow_only_ofModularReadout
    (S : Type*) [Fintype S]
    (P : ProjectiveCharacterGWBridgePacket S) :
    P.finiteSpectralPartition.partition =
      ∑ s : S,
        Real.exp (-(P.finiteSpectralPartition.spectrum.inverseTemperature *
          P.finiteSpectralPartition.spectrum.spectralEnergy s)) *
            P.finiteSpectralPartition.spectrum.spectralVolume s := by
  simpa using
    projectiveCharacter_finiteSpectral_partitionNormalization (S := S) P

end InfoGeometry.GrandUnification
