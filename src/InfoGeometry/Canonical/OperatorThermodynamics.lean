/-
InfoGeometry/Canonical/OperatorThermodynamics.lean

Canonical thermodynamic wrapper in the new modular/supergeometry language.

This file does not introduce a new modular ontology. It packages the existing
relative-modular, Massieu, free-energy, and supervolume shadows under a single
operator-theoretic interface.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
Operator-first thermodynamics packet.

This is the noncommutative owner surface:
- the modular operator / negative-log owner lives in `modular`;
- the untraced exponential family and normalized operator state live in `family`;
- scalar thermodynamic names are obtained only by readout on the operator state
  at the chosen reference parameter.

The older `OperatorThermodynamicsPacket` is retained as a derived shadow packet
for downstream compatibility.
-/
structure OperatorFirstThermodynamicsPacket
    (Param Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op] where
  /-- Modular Hamiltonian / negative-log operator owner. -/
  modular : ModularHamiltonianSurprisalContext (H := Op)

  /-- Untraced operatorial exponential family and normalized operator state. -/
  family : OperatorialExponentialFamily Param Op

  /-- Chosen parameter at which thermodynamic readouts are taken. -/
  referenceParam : Param

  /-- Partition function positivity at the chosen parameter. -/
  partitionFunction_pos : 0 < family.partitionFunction referenceParam

namespace OperatorFirstThermodynamicsPacket

variable {Param Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]

/-- The modular Hamiltonian readout. -/
def modularHamiltonian (P : OperatorFirstThermodynamicsPacket Param Op) : Op →L[ℝ] Op :=
  P.modular.modularHamiltonian

/-- The negative-log modular operator readout. -/
def negativeLogModularOperator (P : OperatorFirstThermodynamicsPacket Param Op) : Op →L[ℝ] Op :=
  P.modular.negativeLogModularOperator

/-- Scalar massieu shadow derived from the operatorial partition function. -/
def massieuPotential (P : OperatorFirstThermodynamicsPacket Param Op) : ℝ :=
  Real.log (P.family.partitionFunction P.referenceParam)

/-- Scalar free-energy shadow derived from the operatorial partition function. -/
def freeEnergy (P : OperatorFirstThermodynamicsPacket Param Op) : ℝ :=
  - Real.log (P.family.partitionFunction P.referenceParam)

/--
Historical relative-entropy shadow.

This is only the packet's negative-log-partition sign convention.  It is not
an Araki or Umegaki relative entropy, which requires two states and a genuine
relative modular owner.
-/
def negativeMassieuPotential (P : OperatorFirstThermodynamicsPacket Param Op) : ℝ :=
  - Real.log (P.family.partitionFunction P.referenceParam)

/-- Supervolume potential derived from the same partition potential. -/
def supervolumePotential (P : OperatorFirstThermodynamicsPacket Param Op) : ℝ :=
  - Real.log (P.family.partitionFunction P.referenceParam)

@[simp]
theorem modularHamiltonian_eq_negativeLogModularOperator
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.modularHamiltonian = P.negativeLogModularOperator :=
  P.modular.modularHamiltonian_eq_negativeLog

@[simp]
theorem massieuPotential_eq_log_partition
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.massieuPotential = Real.log (P.family.partitionFunction P.referenceParam) :=
  rfl

@[simp]
theorem freeEnergy_eq_neg_log_partition
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.freeEnergy = - Real.log (P.family.partitionFunction P.referenceParam) :=
  rfl

@[simp]
theorem negativeMassieuPotential_eq_neg_massieu
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.negativeMassieuPotential = - P.massieuPotential :=
  rfl

@[simp]
theorem supervolumePotential_eq_freeEnergy
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.supervolumePotential = P.freeEnergy :=
  rfl

end OperatorFirstThermodynamicsPacket

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
  modular : ModularHamiltonianSurprisalContext (H := Op)
  partitionFunction : ℝ
  partitionFunction_pos : 0 < partitionFunction

namespace OperatorThermodynamicsPacket

variable {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]

/-- The modular Hamiltonian readout. -/
def modularHamiltonian (P : OperatorThermodynamicsPacket Op) : Op →L[ℝ] Op :=
  P.modular.modularHamiltonian

/-- The negative-log modular operator readout. -/
def negativeLogModularOperator (P : OperatorThermodynamicsPacket Op) : Op →L[ℝ] Op :=
  P.modular.negativeLogModularOperator

/-- Massieu/log-partition potential, derived from the partition function. -/
def massieuPotential (P : OperatorThermodynamicsPacket Op) : ℝ :=
  Real.log P.partitionFunction

/-- Helmholtz free-energy shadow in the packet's unit-temperature convention. -/
def freeEnergy (P : OperatorThermodynamicsPacket Op) : ℝ :=
  -Real.log P.partitionFunction

/-- Relative-entropy scalar shadow in the packet's sign convention. -/
def negativeMassieuPotential (P : OperatorThermodynamicsPacket Op) : ℝ :=
  -P.massieuPotential

/-- Supervolume scalar shadow, definitionally the free-energy shadow. -/
def supervolumePotential (P : OperatorThermodynamicsPacket Op) : ℝ :=
  P.freeEnergy

@[simp]
theorem modularHamiltonian_eq_negativeLogModularOperator
    (P : OperatorThermodynamicsPacket Op) :
    P.modularHamiltonian = P.negativeLogModularOperator :=
  P.modular.modularHamiltonian_eq_negativeLog

@[simp]
theorem massieuPotential_eq_log_partition'
    (P : OperatorThermodynamicsPacket Op) :
    P.massieuPotential = Real.log P.partitionFunction :=
  rfl

@[simp]
theorem freeEnergy_eq_neg_log_partition'
    (P : OperatorThermodynamicsPacket Op) :
    P.freeEnergy = - Real.log P.partitionFunction :=
  rfl

@[simp]
theorem negativeMassieuPotential_eq_neg_massieu'
    (P : OperatorThermodynamicsPacket Op) :
    P.negativeMassieuPotential = - P.massieuPotential :=
  rfl

/-! Historical API compatibility: the former `relativeEntropy` readout was
renamed to `negativeMassieuPotential` so it is not confused with a genuine
relative entropy between two states.  Keep the old theorem name as an alias
to the same owner equation. -/
abbrev relativeEntropy (P : OperatorThermodynamicsPacket Op) : ℝ :=
  P.negativeMassieuPotential

@[simp]
theorem relativeEntropy_eq_neg_massieu'
    (P : OperatorThermodynamicsPacket Op) :
    P.relativeEntropy = - P.massieuPotential :=
  P.negativeMassieuPotential_eq_neg_massieu'

@[simp]
theorem supervolumePotential_eq_freeEnergy'
    (P : OperatorThermodynamicsPacket Op) :
    P.supervolumePotential = P.freeEnergy :=
  rfl

/-- The negative-log partition readout, in free-energy sign convention. -/
def partitionPotential (P : OperatorThermodynamicsPacket Op) : ℝ :=
  - Real.log P.partitionFunction

@[simp]
theorem partitionPotential_eq_freeEnergy
    (P : OperatorThermodynamicsPacket Op) :
    P.partitionPotential = P.freeEnergy := by
  simp [partitionPotential]

/-- The canonical supervolume readout as a negative-log potential. -/
def supervolumeReadout (P : OperatorThermodynamicsPacket Op) : ℝ :=
  P.supervolumePotential

@[simp]
theorem supervolumePotential_eq_partitionPotential
    (P : OperatorThermodynamicsPacket Op) :
    supervolumeReadout P = P.partitionPotential := by
  rfl

end OperatorThermodynamicsPacket

namespace OperatorFirstThermodynamicsPacket

variable {Param Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]

/--
Compatibility projection into the older scalar-shadow packet.
-/
def toShadowPacket
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    OperatorThermodynamicsPacket Op :=
  ⟨P.modular, P.family.partitionFunction P.referenceParam, P.partitionFunction_pos⟩

@[simp]
theorem toShadowPacket_partitionFunction
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.toShadowPacket.partitionFunction = P.family.partitionFunction P.referenceParam :=
  rfl

@[simp]
theorem toShadowPacket_freeEnergy
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.toShadowPacket.freeEnergy = P.freeEnergy :=
  rfl

@[simp]
theorem toShadowPacket_negativeMassieuPotential
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.toShadowPacket.negativeMassieuPotential = P.negativeMassieuPotential :=
  rfl

end OperatorFirstThermodynamicsPacket

/--
Compatibility shadow for the first quantization law.

This is a packaging theorem only: the modular operator, Massieu potential,
free energy, and supervolume readout are different names for the same scalar
potential chain.
-/
abbrev FirstQuantizationLaw
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op] :=
  OperatorThermodynamicsPacket Op

namespace FirstQuantizationLaw

variable {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]

/--
Compatibility projection for the former one-field wrapper.  A first-
quantization law is now definitionally its genuine thermodynamic owner.
-/
abbrev packet (L : FirstQuantizationLaw Op) : OperatorThermodynamicsPacket Op :=
  L

def modularHamiltonian (L : FirstQuantizationLaw Op) : Op →L[ℝ] Op :=
  L.packet.modularHamiltonian

def freeEnergy (L : FirstQuantizationLaw Op) : ℝ :=
  L.packet.freeEnergy

def negativeMassieuPotential (L : FirstQuantizationLaw Op) : ℝ :=
  L.packet.negativeMassieuPotential

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
