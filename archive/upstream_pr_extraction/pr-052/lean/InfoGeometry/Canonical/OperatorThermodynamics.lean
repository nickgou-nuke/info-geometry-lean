/-
InfoGeometry/Canonical/OperatorThermodynamics.lean

Operator-first thermodynamics over a modular operator and an operatorial
exponential family.  Scalar Massieu/free-energy values below are derived
readouts of the operatorial family; no independent scalar packet is stored.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebraic.SplitSuperGeometry
import InfoGeometry.Canonical.ModularSurprisalThermoPacket
import InfoGeometry.Canonical.RelativeModularHamiltonian
import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Canonical.NativeOperatorialExponentialFamily
import InfoGeometry.Thermo.FromLogDet

noncomputable section

namespace InfoGeometry.Canonical.OperatorThermodynamics

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ModularSurprisalThermoPacket
open InfoGeometry.Canonical.RelativeModularHamiltonian
open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.Algebraic.SplitSuperGeometry

/-!
The operator-first packet is the sole owner in this module.  The modular
negative-log operator and the untraced exponential family remain separate
native carriers; scalar thermodynamic quantities are readouts at one chosen
parameter.
-/
structure OperatorFirstThermodynamicsPacket
    (Param Op : Type*) [AddMonoid Param]
    [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op] where
  modular : ModularHamiltonianSurprisalContext (H := Op)
  family : NativeOperatorialExponentialFamily.Family Param Op
  referenceParam : Param
  partitionFunction_pos : 0 < family.partitionFunction referenceParam

namespace OperatorFirstThermodynamicsPacket

variable {Param Op : Type*} [AddMonoid Param]
variable [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op]

def modularHamiltonian
    (P : OperatorFirstThermodynamicsPacket Param Op) : Op →L[ℝ] Op :=
  P.modular.modularHamiltonian

def negativeLogModularOperator
    (P : OperatorFirstThermodynamicsPacket Param Op) : Op →L[ℝ] Op :=
  P.modular.negativeLogModularOperator

def partitionFunction
    (P : OperatorFirstThermodynamicsPacket Param Op) : ℝ :=
  P.family.partitionFunction P.referenceParam

def massieuPotential
    (P : OperatorFirstThermodynamicsPacket Param Op) : ℝ :=
  Real.log P.partitionFunction

def freeEnergy
    (P : OperatorFirstThermodynamicsPacket Param Op) : ℝ :=
  -Real.log P.partitionFunction

def negativeMassieuPotential
    (P : OperatorFirstThermodynamicsPacket Param Op) : ℝ :=
  -P.massieuPotential

def supervolumePotential
    (P : OperatorFirstThermodynamicsPacket Param Op) : ℝ :=
  P.freeEnergy

@[simp]
theorem modularHamiltonian_eq_negativeLogModularOperator
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.modularHamiltonian = P.negativeLogModularOperator :=
  P.modular.modularHamiltonian_eq_negativeLog

@[simp]
theorem partitionFunction_eq_family_readout
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.partitionFunction = P.family.partitionFunction P.referenceParam :=
  rfl

@[simp]
theorem massieuPotential_eq_log_partition
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.massieuPotential = Real.log P.partitionFunction :=
  rfl

@[simp]
theorem freeEnergy_eq_neg_log_partition
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.freeEnergy = -Real.log P.partitionFunction :=
  rfl

@[simp]
theorem negativeMassieuPotential_eq_neg_massieu
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.negativeMassieuPotential = -P.massieuPotential :=
  rfl

@[simp]
theorem supervolumePotential_eq_freeEnergy
    (P : OperatorFirstThermodynamicsPacket Param Op) :
    P.supervolumePotential = P.freeEnergy :=
  rfl

end OperatorFirstThermodynamicsPacket

end InfoGeometry.Canonical.OperatorThermodynamics
