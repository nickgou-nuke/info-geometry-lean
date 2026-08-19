import InfoGeometry.Canonical.WeylFiveGradeBalanceBridge
import InfoGeometry.Canonical.WeylGWVolumeBridge
import InfoGeometry.Canonical.WeylBKMDriftMassBridge
import InfoGeometry.Canonical.WeylNormalizedCARCCRBridge
import InfoGeometry.Canonical.SuperchargeModularHamiltonianBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.WeylFiveGradePhysicalReadoutBridge

Routing facade for physical grade-zero readouts.

The owner modules prove the actual normalization theorems:

* `WeylGWVolumeBridge`: gauge-fixed volume is projectively invariant.
* `WeylBKMDriftMassBridge`: gauge-fixed BKM mass/stiffness is projectively invariant.
* `WeylNormalizedCARCCRBridge`: scaled CAR/CCR pairs become canonical.
* `SuperchargeModularHamiltonianBridge`: `Ksur` is the calibrated regular-support
  super-Hamiltonian surrogate.

This file only records the five-grade routing/readback fact that these outputs
are intended to live in the grade-zero physical lane.  It does not prove a new
Virasoro, Sugawara, Type III, or anomaly-cancellation theorem.
-/

namespace InfoGeometry.Canonical.WeylFiveGradePhysicalReadoutBridge

open InfoGeometry.Canonical.WeylFiveGradeBalanceBridge
open InfoGeometry.Canonical.WeylGWVolumeBridge
open InfoGeometry.Canonical.WeylBKMDriftMassBridge
open InfoGeometry.Canonical.WeylNormalizedCARCCRBridge

/-- Tags for the already-normalized physical readouts. -/
@[rep_depth operator]
inductive PhysicalReadoutKind where
  | volume
  | bkmMass
  | normalizedCAR
  | normalizedCCR
  | modularHamiltonianSurrogate
deriving DecidableEq, Repr

namespace PhysicalReadoutKind

/-- Every physical readout kind is routed to the grade-zero lane. -/
@[rep_depth operator]
def grade : PhysicalReadoutKind → WeylFiveGrade
  | volume => WeylFiveGrade.zero
  | bkmMass => WeylFiveGrade.zero
  | normalizedCAR => WeylFiveGrade.zero
  | normalizedCCR => WeylFiveGrade.zero
  | modularHamiltonianSurrogate => WeylFiveGrade.zero

@[rep_depth operator]
theorem volume_grade_zero :
    grade volume = WeylFiveGrade.zero := rfl

@[rep_depth operator]
theorem bkmMass_grade_zero :
    grade bkmMass = WeylFiveGrade.zero := rfl

@[rep_depth operator]
theorem normalizedCAR_grade_zero :
    grade normalizedCAR = WeylFiveGrade.zero := rfl

@[rep_depth operator]
theorem normalizedCCR_grade_zero :
    grade normalizedCCR = WeylFiveGrade.zero := rfl

@[rep_depth operator]
theorem modularHamiltonianSurrogate_grade_zero :
    grade modularHamiltonianSurrogate = WeylFiveGrade.zero := rfl

end PhysicalReadoutKind

/-- Carrier grouping the volume and BKM mass readout surfaces. -/
@[rep_depth operator]
structure WeylScalarPhysicalReadoutCarrier
    (VolumeState MassState : Type*) where
  volume : WeylGWVolumeCarrier VolumeState
  bkmMass : WeylBKMDriftMassCarrier MassState

namespace WeylScalarPhysicalReadoutCarrier

variable {VolumeState MassState : Type*}
variable (C : WeylScalarPhysicalReadoutCarrier VolumeState MassState)

@[rep_depth operator]
theorem volume_grade_zero :
    PhysicalReadoutKind.grade .volume = WeylFiveGrade.zero := rfl

@[rep_depth operator]
theorem bkmMass_grade_zero :
    PhysicalReadoutKind.grade .bkmMass = WeylFiveGrade.zero := rfl

end WeylScalarPhysicalReadoutCarrier

/-! ## CAR/CCR normalized readouts -/

section Fock

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Carrier grouping Weyl-normalized CAR and CCR pairs. -/
@[rep_depth krein]
structure WeylFockPhysicalReadoutCarrier where
  car : ScaledCARPair E
  ccr : ScaledCCRPair E

namespace WeylFockPhysicalReadoutCarrier

variable (C : WeylFockPhysicalReadoutCarrier (E := E))

@[rep_depth krein]
theorem normalizedCAR_grade_zero :
    PhysicalReadoutKind.grade .normalizedCAR = WeylFiveGrade.zero := rfl

@[rep_depth krein]
theorem normalizedCCR_grade_zero :
    PhysicalReadoutKind.grade .normalizedCCR = WeylFiveGrade.zero := rfl

/-- The normalized CAR pair theorem is inherited from `WeylNormalizedCARCCRBridge`. -/
@[rep_depth krein]
theorem car_is_normalized :
    InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
      (E := E) C.car.normalizedAnnihilation C.car.normalizedCreation :=
  C.car.normalized_isCARPair

/-- The normalized CCR pair theorem is inherited from `WeylNormalizedCARCCRBridge`. -/
@[rep_depth krein]
theorem ccr_is_normalized :
    IsCCRPair (E := E) C.ccr.normalizedAnnihilation C.ccr.normalizedCreation :=
  C.ccr.normalized_isCCRPair

end WeylFockPhysicalReadoutCarrier

namespace WeylCARPhysicalReadoutCarrier

variable (C : ScaledCARPair E)

@[rep_depth krein]
theorem normalizedCAR_grade_zero :
    PhysicalReadoutKind.grade .normalizedCAR = WeylFiveGrade.zero := rfl

/-- The normalized CAR pair theorem is inherited from `WeylNormalizedCARCCRBridge`. -/
@[rep_depth krein]
theorem car_is_normalized :
    InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
      (E := E) C.normalizedAnnihilation C.normalizedCreation :=
  C.normalized_isCARPair

end WeylCARPhysicalReadoutCarrier

/-- Concrete split-`Cl(1,1)` CAR readout at grade zero. -/
@[rep_depth krein]
noncomputable def concreteCl11WeylCARPhysicalReadoutCarrier :
    ScaledCARPair E :=
  concreteCl11ScaledCARPair (E := E)

/-- The concrete split-`Cl(1,1)` CAR readout is normalized. -/
@[rep_depth krein]
theorem concreteCl11WeylCAR_is_normalized :
    InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
      (E := E)
      (concreteCl11WeylCARPhysicalReadoutCarrier (E := E)).normalizedAnnihilation
      (concreteCl11WeylCARPhysicalReadoutCarrier (E := E)).normalizedCreation :=
  (concreteCl11WeylCARPhysicalReadoutCarrier (E := E)).normalized_isCARPair

end Fock

/-! ## Modular-Hamiltonian surrogate readout -/

section ModularHamiltonian

/-- Carrier routing the calibrated supercharge modular-Hamiltonian surrogate to grade zero. -/
@[rep_depth operator]
structure WeylModularHamiltonianPhysicalReadoutCarrier
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  bridge :
    InfoGeometry.Canonical.SuperchargeModularHamiltonianBridge.Bridge
      (E := E)

namespace WeylModularHamiltonianPhysicalReadoutCarrier

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (C : WeylModularHamiltonianPhysicalReadoutCarrier E)

@[rep_depth operator]
theorem modularHamiltonianSurrogate_grade_zero :
    PhysicalReadoutKind.grade .modularHamiltonianSurrogate = WeylFiveGrade.zero := rfl

/-- The calibrated `Ksur` law is inherited from `SuperchargeModularHamiltonianBridge`. -/
@[rep_depth operator]
theorem Ksur_eq_calibrated :
    C.bridge.Ksur =
      C.bridge.modularEnergyUnit •
        DrazinSupercharge.CertifiedInverseKernel.regularRestrictedSuperHamiltonian
          C.bridge.CIK :=
  C.bridge.Ksur_eq

end WeylModularHamiltonianPhysicalReadoutCarrier

end ModularHamiltonian

/--
Unified grade-zero physical readout carrier.

This is a routing object only.  The underlying volume, mass, Fock, and modular
Hamiltonian theorems remain owned by their respective bridge modules.
-/
@[rep_depth operator]
structure WeylFiveGradePhysicalReadoutCarrier
    (VolumeState MassState : Type*) (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  scalarReadouts : WeylScalarPhysicalReadoutCarrier VolumeState MassState
  fockReadouts : WeylFockPhysicalReadoutCarrier (E := E)
  modularReadout : WeylModularHamiltonianPhysicalReadoutCarrier E

namespace WeylFiveGradePhysicalReadoutCarrier

variable {VolumeState MassState : Type*} {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (C : WeylFiveGradePhysicalReadoutCarrier VolumeState MassState E)

@[rep_depth operator]
theorem volume_grade_zero :
    PhysicalReadoutKind.grade .volume = WeylFiveGrade.zero := rfl

@[rep_depth operator]
theorem bkmMass_grade_zero :
    PhysicalReadoutKind.grade .bkmMass = WeylFiveGrade.zero := rfl

@[rep_depth operator]
theorem normalizedCAR_grade_zero :
    PhysicalReadoutKind.grade .normalizedCAR = WeylFiveGrade.zero := rfl

@[rep_depth operator]
theorem normalizedCCR_grade_zero :
    PhysicalReadoutKind.grade .normalizedCCR = WeylFiveGrade.zero := rfl

@[rep_depth operator]
theorem modularHamiltonianSurrogate_grade_zero :
    PhysicalReadoutKind.grade .modularHamiltonianSurrogate = WeylFiveGrade.zero := rfl

end WeylFiveGradePhysicalReadoutCarrier

end InfoGeometry.Canonical.WeylFiveGradePhysicalReadoutBridge
