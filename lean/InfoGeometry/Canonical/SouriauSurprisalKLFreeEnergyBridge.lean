import InfoGeometry.Canonical.SouriauOperatorialLogPotential
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

/-! ## Owner readback dashboard -/

namespace OwnerReadbacks

/-! ### 1. Surprisal and KL / relative information energy -/

variable {State LieAlgebra LieDual Obs : Type*}

/-- KL is expectation of the logarithmic Radon--Nikodym density. -/
@[rep_depth thermo]
theorem KL_eq_expectation_logDensity
    (D : LogRadonNikodymData State) :
    D.KL = D.expectationNu D.logDensity :=
  D.KL_eq_expectation_logDensity

/-- KL is also negative expectation of the relative surprisal density. -/
@[rep_depth thermo]
theorem KL_eq_neg_expectation_surprisalDensity
    (D : LogRadonNikodymData State) :
    D.KL = -D.expectationNu D.surprisalDensity :=
  D.KL_eq_neg_expectation_surprisalDensity

/-- Relative surprisal density is the negative logarithmic density. -/
@[rep_depth thermo]
theorem surprisalDensity_eq_neg_logDensity
    (D : LogRadonNikodymData State) (x : State) :
    D.surprisalDensity x = -D.logDensity x :=
  D.surprisalDensity_eq_neg_logDensity x

/-! ### 2. Souriau beta source and log-potential -/

/-- Souriau source energy is the moment-map pairing with operatorial beta. -/
@[rep_depth thermo]
theorem K_beta_eq_pairing
    (D : SouriauLieThermoData State LieAlgebra LieDual) (x : State) :
    D.K_beta x = D.pairing (D.momentMap x) D.beta :=
  D.K_beta_eq_pairing_apply x

/-- Negative log Gibbs density decomposes as Souriau source energy plus partition potential. -/
@[rep_depth thermo]
theorem negativeLogGibbsDensity_eq_K_beta_add_Phi
    (D : SouriauLieThermoData State LieAlgebra LieDual) (x : State) :
    -Real.log (D.gibbsDensity x) = D.K_beta x + D.partitionPotential :=
  D.negativeLogGibbsDensity_eq_K_beta_add_Phi x

/-- Pairing form of the negative log Gibbs density decomposition. -/
@[rep_depth thermo]
theorem negativeLogGibbsDensity_eq_pairing_add_Phi
    (D : SouriauLieThermoData State LieAlgebra LieDual) (x : State) :
    -Real.log (D.gibbsDensity x) =
      D.pairing (D.momentMap x) D.beta + D.partitionPotential :=
  D.negativeLogGibbsDensity_eq_pairing_add_Phi x

/-! ### 3. Negative-log RN derivative / modular potential -/

/-- The Souriau modular potential is the negative-log density read as `K_beta + Phi`. -/
@[rep_depth thermo]
theorem modularPotential_eq_K_beta_add_Phi
    (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) (x : State) :
    D.modularPotential x = D.souriau.K_beta x + D.souriau.partitionPotential :=
  D.modularPotential_eq_K_beta_add_Phi x

/-- Entropy is the expectation of the modular potential under the supplied readout. -/
@[rep_depth thermo]
theorem entropy_eq_expectation_modularPotential
    (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) :
    D.entropy = D.expectationBeta D.modularPotential :=
  D.entropy_eq_expectation_modularPotential

/-! ### 4. KL as Souriau/Bregman relative information energy -/

/-- KL readout as Bregman divergence of the Souriau potential. -/
@[rep_depth thermo]
theorem KL_eq_souriau_Bregman
    (B : SouriauKLBregmanWitness State LieAlgebra LieDual) :
    B.klValue =
      B.alphaPartitionPotential
        - B.generator.souriau.partitionPotential
        - B.generator.dPhi B.alphaMinusBeta :=
  B.KL_eq_souriau_Bregman

/-! ### 5. Modular Hamiltonian / operatorial Souriau family readbacks -/

/-- Modular Hamiltonian data read back as the negative logarithmic density. -/
@[rep_depth operator]
theorem modularHamiltonian_eq_negativeLogDensity
    (M : ModularHamiltonianData Obs) :
    M.modularHamiltonian = M.negativeLogDensity :=
  M.modularHamiltonian_eq_negativeLogDensity_theorem

/-- Operatorial Souriau modular Hamiltonian as `Khat_beta + Phi(beta) * 1`. -/
@[rep_depth operator]
theorem modularHamiltonian_eq_Khat_add_logZ
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    Q.modularHamiltonian =
      Q.opAdd Q.Khat_beta (Q.opScale Q.partitionPotential Q.opIdentity) :=
  Q.modularHamiltonian_eq_Khat_add_logZ

/-- The operatorial Souriau Hamiltonian source is the representation of beta. -/
@[rep_depth operator]
theorem Khat_beta_eq_Jhat_beta
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    Q.Khat_beta = Q.Jhat Q.beta :=
  Q.Khat_beta_eq_Jhat_beta

end OwnerReadbacks

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
