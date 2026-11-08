import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ThermodynamicGenerator
import InfoGeometry.Canonical.RelativePotentialDiscreteBridge
import InfoGeometry.Thermo.FromBregman
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.SouriauSurprisalKLFreeEnergyBridge

Souriau/operatorial bridge from surprisal and relative information energy to a
free-energy operator.

The calibration point is deliberately strict:

* `souriauBeta` is operatorial source data, not a primitive scalar inverse
  temperature;
* scalar inverse temperature appears only after an explicit scalar thermal
  gauge calibration;
* modular-Hamiltonian identification is an external readout predicate, not an
  automatic theorem of this carrier.

This file is a small canonical socket.  It does not construct Araki relative
entropy, KMS flow, Tomita modular operators, or unbounded logarithms.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauSurprisalKLFreeEnergyBridge

open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.Canonical.StateDependentTransport
open InfoGeometry.Canonical.ThermodynamicGenerator
open InfoGeometry.Canonical.RelativePotentialDiscreteBridge

/--
Operatorial Souriau thermodynamic carrier.

`surprisal` and `relativeEnergy` name the information-energy channel.  The
Souriau `beta` is an operator/source channel in `Op`, not a scalar by default.
-/
@[rep_depth thermo]
structure SouriauThermodynamicCarrier
    (State Op : Type*) [Ring Op] [Algebra ℝ Op] where
  /-- Operatorial surprisal/readout channel. -/
  surprisal : State → Op
  /-- KL/relative-entropy-as-information-energy channel. -/
  relativeEnergy : State → State → Op
  /-- Souriau thermodynamic source operator.  Not primitive scalar inverse temperature. -/
  souriauBeta : State → Op
  /-- Operatorial entropy channel. -/
  entropy : State → Op
  /-- Souriau-regularized free-energy operator/readout. -/
  freeEnergy : State → Op

/--
External predicate: the free-energy channel is the Souriau beta-regularized
combination of relative information energy and entropy.

The formula is intentionally operatorial:
`F = E_rel - beta * S`.
-/
@[rep_depth thermo]
def IsSouriauFreeEnergyRegularization
    {State Op : Type*} [Ring Op] [Algebra ℝ Op]
    (C : SouriauThermodynamicCarrier State Op) : Prop :=
  ∀ s ref : State,
    C.freeEnergy s = C.relativeEnergy s ref - C.souriauBeta s * C.entropy s

/--
Scalar thermal gauge carrier.

This carrier only stores the scalar readout.  The calibration law projecting
operatorial Souriau `beta` to a scalar multiple of identity is external.
-/
@[rep_depth thermo]
structure ScalarThermalGauge
    (State Op : Type*) [Ring Op] [Algebra ℝ Op] where
  carrier : SouriauThermodynamicCarrier State Op
  /-- Scalar inverse-temperature readout after gauge choice. -/
  inverseTemperature : State → ℝ

/--
External predicate: scalar-gauge calibration of the operatorial Souriau beta
source.
-/
@[rep_depth thermo]
def IsScalarThermalGaugeCalibration
    {State Op : Type*} [Ring Op] [Algebra ℝ Op]
    (G : ScalarThermalGauge State Op) : Prop :=
  ∀ s : State,
    G.carrier.souriauBeta s = G.inverseTemperature s • (1 : Op)

namespace ScalarThermalGauge

variable {State Op : Type*} [Ring Op] [Algebra ℝ Op]
variable (G : ScalarThermalGauge State Op)

/--
Once a scalar thermal gauge is supplied, the operatorial free-energy relation
reduces to the familiar scalar-weighted entropy term.
-/
@[rep_depth thermo]
theorem scalar_gauged_free_energy
    (hGauge : IsScalarThermalGaugeCalibration G)
    (hFree : IsSouriauFreeEnergyRegularization G.carrier)
    (s ref : State) :
    G.carrier.freeEnergy s =
      G.carrier.relativeEnergy s ref - G.inverseTemperature s • G.carrier.entropy s := by
  rw [hFree s ref, hGauge s]
  simp [Algebra.smul_mul_assoc]

end ScalarThermalGauge

/--
Carrier for an explicit modular-Hamiltonian/free-energy readout.

This names the capstone socket without asserting that every modular Hamiltonian
is automatically the Souriau free-energy operator.
-/
@[rep_depth thermo]
structure ModularFreeEnergyReadout
    (State Op : Type*) [Ring Op] [Algebra ℝ Op] where
  thermodynamics : SouriauThermodynamicCarrier State Op
  /-- Candidate modular-Hamiltonian readout in the same operator carrier. -/
  modularHamiltonian : State → Op

/--
External predicate: the modular-Hamiltonian readout is calibrated as the
Souriau-regularized free-energy operator.
-/
@[rep_depth thermo]
def IsModularFreeEnergyOrigin
    {State Op : Type*} [Ring Op] [Algebra ℝ Op]
    (M : ModularFreeEnergyReadout State Op) : Prop :=
  ∀ s : State,
    M.modularHamiltonian s = M.thermodynamics.freeEnergy s

namespace ModularFreeEnergyReadout

variable {State Op : Type*} [Ring Op] [Algebra ℝ Op]
variable (M : ModularFreeEnergyReadout State Op)

/-- Readback of an explicitly supplied modular/free-energy calibration. -/
@[rep_depth thermo]
theorem modularHamiltonian_eq_freeEnergy
    (h : IsModularFreeEnergyOrigin M)
    (s : State) :
    M.modularHamiltonian s = M.thermodynamics.freeEnergy s :=
  h s

end ModularFreeEnergyReadout

end InfoGeometry.Canonical.SouriauSurprisalKLFreeEnergyBridge
