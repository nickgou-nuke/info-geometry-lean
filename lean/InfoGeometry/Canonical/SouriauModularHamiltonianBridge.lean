import InfoGeometry.Canonical.SouriauSurprisalKLFreeEnergyBridge
import InfoGeometry.Canonical.SuperchargeModularHamiltonianBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.SouriauModularHamiltonianBridge

Calibrated bridge between the Souriau negative-log/free-energy readout and the
Drazin/MP supercharge modular-Hamiltonian surrogate.

This is a capstone socket, not an identity theorem.  It does not claim
`K_mod = F_beta` unconditionally.  It records the exact point where a concrete
model may identify:

* the bounded regular-support supercharge surrogate
  `K_sur = μ_Q • P_D Q² P_D`;
* the Souriau/operatorial free-energy or negative-log readout.

The identification is an explicit external predicate.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauModularHamiltonianBridge

open scoped InnerProductSpace
open InfoGeometry.Canonical.SouriauSurprisalKLFreeEnergyBridge
open InfoGeometry.Canonical.SuperchargeModularHamiltonianBridge

variable {E State BetaSource : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

/--
Carrier joining a bounded supercharge modular surrogate with a Souriau
free-energy readout in the same operator carrier.

`betaSource` is intentionally polymorphic: it may be a Lie-algebra/source object,
an operatorial beta channel, or a later scalar-gauge witness carrier.
-/
@[rep_depth thermo]
structure SouriauModularHamiltonianCarrier where
  /-- Drazin/MP supercharge modular-Hamiltonian surrogate. -/
  supercharge : SuperchargeModularHamiltonianBridge (E := E)

  /-- Souriau/operatorial thermodynamic carrier valued in bounded endomorphisms. -/
  thermodynamics : SouriauThermodynamicCarrier State EndH

  /-- Selected state whose free-energy readout is compared with `K_sur`. -/
  state : State

  /-- Operatorial Souriau beta/source channel.  Not scalar by default. -/
  betaSource : BetaSource

  /-- Optional scalar gauge readout of the beta source. -/
  scalarBetaGauge : BetaSource → ℝ

namespace SouriauModularHamiltonianCarrier

variable (C : SouriauModularHamiltonianCarrier (E := E) (State := State)
  (BetaSource := BetaSource))

/-- Bounded supercharge modular-Hamiltonian surrogate. -/
@[rep_depth thermo]
abbrev Ksur : EndH :=
  C.supercharge.Ksur

/-- Souriau free-energy operator readout at the selected state. -/
@[rep_depth thermo]
abbrev freeEnergyOperator : EndH :=
  C.thermodynamics.freeEnergy C.state

/-- The supercharge surrogate calibration inherited from its owner module. -/
@[rep_depth thermo]
theorem Ksur_eq_calibrated_regularRestrictedSuperHamiltonian :
    C.Ksur =
      C.supercharge.modularEnergyUnit •
        DrazinSupercharge.CertifiedInverseKernel.regularRestrictedSuperHamiltonian
          C.supercharge.CIK :=
  C.supercharge.Ksur_eq_calibrated_regularRestrictedSuperHamiltonian

/--
External predicate: the bounded supercharge surrogate is calibrated as the
Souriau free-energy operator.
-/
@[rep_depth thermo]
def IsSouriauModularHamiltonianOrigin : Prop :=
  C.Ksur = C.freeEnergyOperator

/-- Readback of an explicitly supplied Souriau/modular-Hamiltonian calibration. -/
@[rep_depth thermo]
theorem Ksur_eq_freeEnergy_of_origin
    (h : C.IsSouriauModularHamiltonianOrigin) :
    C.Ksur = C.freeEnergyOperator :=
  h

/--
The calibrated surrogate inherits left support stability from the supercharge
modular-Hamiltonian owner.
-/
@[rep_depth thermo]
theorem spectralProjector_mul_Ksur :
    C.supercharge.CIK.spectralProjector * C.Ksur = C.Ksur :=
  C.supercharge.spectralProjector_mul_Ksur

/--
The calibrated surrogate inherits right support stability from the supercharge
modular-Hamiltonian owner.
-/
@[rep_depth thermo]
theorem Ksur_mul_spectralProjector :
    C.Ksur * C.supercharge.CIK.spectralProjector = C.Ksur :=
  C.supercharge.Ksur_mul_spectralProjector

/-- The calibrated surrogate remains in the even/spectrally compact lane. -/
@[rep_depth thermo]
theorem Ksur_isSpectralCompact :
    let T := C.supercharge.CIK.toInformationCartanTriple
    T.IsSpectralCompact C.Ksur :=
  C.supercharge.Ksur_isSpectralCompact

end SouriauModularHamiltonianCarrier

end InfoGeometry.Canonical.SouriauModularHamiltonianBridge
