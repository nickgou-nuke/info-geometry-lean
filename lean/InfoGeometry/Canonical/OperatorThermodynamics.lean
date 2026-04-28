/-
InfoGeometry/Canonical/OperatorThermodynamics.lean

Canonical thermodynamic wrapper in the new modular/supergeometry language.

This file does not introduce a new modular ontology. It packages the existing
relative-modular, Massieu, free-energy, and supervolume shadows under a single
operator-theoretic interface.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebraic.SplitSuperGeometry
import InfoGeometry.Canonical.ModularSurprisalThermoPacket
import InfoGeometry.Canonical.OperatorThermoBridge
import InfoGeometry.Canonical.RelativeModularHamiltonian
import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Thermo.FromLogDet

noncomputable section

namespace InfoGeometry.Canonical.OperatorThermodynamics

open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorThermoBridge
open InfoGeometry.Canonical.ModularSurprisalThermoPacket
open InfoGeometry.Canonical.RelativeModularHamiltonian
open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.Algebraic.SplitSuperGeometry

/--
Canonical operator thermodynamics packet.

The new language is:
- modular operator = negative-log density operator;
- Massieu potential = log partition;
- free energy = negative log partition;
- relative entropy = surprisal / log-density readout;
- supervolume potential = negative log supervolume readout.
-/
structure OperatorThermodynamicsPacket
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op] where
  /-- Modular Hamiltonian / negative-log operator owner. -/
  modular : ModularHamiltonianSurprisalContext (H := Op)

  /-- Partition function readout. -/
  partitionFunction : ℝ

  /-- The partition function is positive where logarithms are read. -/
  partitionFunction_pos : 0 < partitionFunction

  /-- Massieu/log-partition potential. -/
  massieuPotential : ℝ

  /-- Helmholtz free-energy readout. -/
  freeEnergy : ℝ

  /-- Relative entropy / surprisal readout. -/
  relativeEntropy : ℝ

  /-- Supervolume potential, aligned with the split-supergeometry shadow. -/
  supervolumePotential : ℝ

  /-- Massieu potential is the logarithm of the partition function. -/
  massieuPotential_eq_log_partition : massieuPotential = Real.log partitionFunction

  /-- Free energy is the negative logarithm of the partition function. -/
  freeEnergy_eq_neg_log_partition : freeEnergy = - Real.log partitionFunction

  /-- Relative entropy is the negative Massieu potential in this sign convention. -/
  relativeEntropy_eq_neg_massieu : relativeEntropy = - massieuPotential

  /-- The supervolume potential is the same scalar shadow as the free energy. -/
  supervolumePotential_eq_freeEnergy : supervolumePotential = freeEnergy

namespace OperatorThermodynamicsPacket

variable {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]

/-- The modular Hamiltonian readout. -/
def modularHamiltonian (P : OperatorThermodynamicsPacket Op) : Op →L[ℝ] Op :=
  P.modular.modularHamiltonian

/-- The negative-log modular operator readout. -/
def negativeLogModularOperator (P : OperatorThermodynamicsPacket Op) : Op →L[ℝ] Op :=
  P.modular.negativeLogModularOperator

@[simp]
theorem modularHamiltonian_eq_negativeLogModularOperator
    (P : OperatorThermodynamicsPacket Op) :
    P.modularHamiltonian = P.negativeLogModularOperator :=
  P.modular.modularHamiltonian_eq_negativeLog

@[simp]
theorem massieuPotential_eq_log_partition'
    (P : OperatorThermodynamicsPacket Op) :
    P.massieuPotential = Real.log P.partitionFunction :=
  P.massieuPotential_eq_log_partition

@[simp]
theorem freeEnergy_eq_neg_log_partition'
    (P : OperatorThermodynamicsPacket Op) :
    P.freeEnergy = - Real.log P.partitionFunction :=
  P.freeEnergy_eq_neg_log_partition

@[simp]
theorem relativeEntropy_eq_neg_massieu'
    (P : OperatorThermodynamicsPacket Op) :
    P.relativeEntropy = - P.massieuPotential :=
  P.relativeEntropy_eq_neg_massieu

@[simp]
theorem supervolumePotential_eq_freeEnergy'
    (P : OperatorThermodynamicsPacket Op) :
    P.supervolumePotential = P.freeEnergy :=
  P.supervolumePotential_eq_freeEnergy

/-- The negative-log partition readout, in free-energy sign convention. -/
def partitionPotential (P : OperatorThermodynamicsPacket Op) : ℝ :=
  - Real.log P.partitionFunction

@[simp]
theorem partitionPotential_eq_freeEnergy
    (P : OperatorThermodynamicsPacket Op) :
    P.partitionPotential = P.freeEnergy := by
  simp [partitionPotential, P.freeEnergy_eq_neg_log_partition]

/-- The canonical supervolume readout as a negative-log potential. -/
def supervolumeReadout (P : OperatorThermodynamicsPacket Op) : ℝ :=
  P.supervolumePotential

@[simp]
theorem supervolumePotential_eq_partitionPotential
    (P : OperatorThermodynamicsPacket Op) :
    supervolumeReadout P = P.partitionPotential := by
  rw [supervolumeReadout, partitionPotential]
  rw [P.supervolumePotential_eq_freeEnergy, P.freeEnergy_eq_neg_log_partition]

end OperatorThermodynamicsPacket

/--
Compatibility shadow for the first quantization law.

This is a packaging theorem only: the modular operator, Massieu potential,
free energy, and supervolume readout are different names for the same scalar
potential chain.
-/
structure FirstQuantizationLaw (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op] where
  packet : OperatorThermodynamicsPacket Op

namespace FirstQuantizationLaw

variable {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]

def modularHamiltonian (L : FirstQuantizationLaw Op) : Op →L[ℝ] Op :=
  L.packet.modularHamiltonian

def freeEnergy (L : FirstQuantizationLaw Op) : ℝ :=
  L.packet.freeEnergy

def relativeEntropy (L : FirstQuantizationLaw Op) : ℝ :=
  L.packet.relativeEntropy

def supervolumePotential (L : FirstQuantizationLaw Op) : ℝ :=
  L.packet.supervolumePotential

@[simp]
theorem freeEnergy_eq_partitionPotential
    (L : FirstQuantizationLaw Op) :
    L.freeEnergy = L.packet.partitionPotential :=
  L.packet.partitionPotential_eq_freeEnergy.symm

@[simp]
theorem modularHamiltonian_eq_negativeLogModularOperator
    (L : FirstQuantizationLaw Op) :
    L.modularHamiltonian = L.packet.negativeLogModularOperator :=
  L.packet.modularHamiltonian_eq_negativeLogModularOperator

end FirstQuantizationLaw

end InfoGeometry.Canonical.OperatorThermodynamics
