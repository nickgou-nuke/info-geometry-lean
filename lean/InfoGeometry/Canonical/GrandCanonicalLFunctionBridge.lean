import Mathlib
import InfoGeometry.Canonical.GrandCanonicalHamiltonianFlowBridge
import InfoGeometry.Canonical.LFunctionHamiltonianFlowBridge
import InfoGeometry.Canonical.GrandCanonicalThermodynamicEngine
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.GrandCanonicalLFunctionBridge

Bridge packet for the grand-canonical character-theoretic corridor.

This file does not re-prove the thermodynamic engine or the twisted Euler product
surface. It packages the existing grand-canonical engine together with the
already-owned dynamical L-function bridge, and records the partition-surface
alignment needed to transfer the temperature readout across the two layers.
-/

noncomputable section

namespace InfoGeometry.Canonical.GrandCanonicalLFunctionFlowBridge

open InfoGeometry.Canonical.LFunctionHamiltonianFlowBridge
open InfoGeometry.Canonical.GrandCanonicalThermodynamicEngine
open InfoGeometry.Arithmetic.LFunctionRepresentationBridge
open InfoGeometry.Arithmetic.LFunctionRepresentationBridge.TwistedSouriauWeylBridge
open InfoGeometry.Thermodynamics.SouriauWeylPartition

variable
    {Orbit G E Op H Finite Alg Symmetry : Type}
    [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

/--
Grand-canonical L-function bridge.

The engine supplies the thermodynamic/Hamiltonian owner surface; the L-function
bridge supplies the twisted character readout on the same partition corridor.
-/
@[rep_depth transport]
structure GrandCanonicalLFunctionBridge
    (Orbit G E Op H Finite Alg Symmetry : Type)
    [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  /-- Grand-canonical thermodynamic engine. -/
  engine : GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry

  /-- Dynamical L-function bridge. -/
  lfunction : LFunctionHamiltonianFlowBridge Orbit G E Op H Finite Alg

  /--
  Partition-surface alignment:
  the L-function corridor and the grand-canonical engine are evaluated on the
  same Souriau-Weyl partition surface.
  -/
  partition_alignment :
    lfunction.coadjointFlow.flow.partition = engine.flow.partition

namespace Bridge

variable
    {Orbit G E Op H Finite Alg Symmetry : Type}
    [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B : GrandCanonicalLFunctionBridge Orbit G E Op H Finite Alg Symmetry)

/-- The partition temperatures agree across the engine and L-function bridge. -/
@[rep_depth transport]
theorem partition_temperature_alignment :
    B.lfunction.coadjointFlow.flow.partition.temperature =
      B.engine.flow.partition.temperature := by
  simpa using congrArg (fun P => P.temperature) B.partition_alignment

/-- The L-function packet beta is the engine partition temperature. -/
@[rep_depth transport]
theorem packet_beta_eq_engine_temperature :
    B.lfunction.packet.beta = B.engine.flow.partition.temperature := by
  calc
    B.lfunction.packet.beta = B.lfunction.coadjointFlow.flow.partition.temperature :=
      B.lfunction.packet_beta_eq_flow
    _ = B.engine.flow.partition.temperature :=
      Bridge.partition_temperature_alignment (B := B)

/-- The engine still identifies the Hamiltonian with the Souriau generator. -/
@[rep_depth transport]
theorem engine_flow_hamiltonian_is_souriau_generator :
    B.engine.flow.selfAdjointHamiltonian =
      B.engine.flow.modularContext.logContext.modularHamiltonian :=
  InfoGeometry.Canonical.GrandCanonicalThermodynamicEngine.hamiltonian_flow_is_souriau_generator
    (Engine := B.engine)

/-- The engine still identifies the KMS inverse temperature with `Re(s)`. -/
@[rep_depth transport]
theorem engine_kms_inverse_temperature_eq_real_part_of_s :
    B.engine.flow.modularContext.beta = B.engine.flow.partition.temperature.s.re :=
  InfoGeometry.Canonical.GrandCanonicalThermodynamicEngine.kms_inverse_temperature_eq_real_part_of_s
    (Engine := B.engine)

/-- The engine still identifies the Riemann-Weil vector field with the force. -/
@[rep_depth transport]
theorem engine_riemann_weil_is_wasserstein_gradient (x : H) :
    B.engine.thermodynamicForce x =
      B.engine.thermodynamicBridge.explicitFormula.wassersteinField x :=
  InfoGeometry.Canonical.GrandCanonicalThermodynamicEngine.riemann_weil_is_wasserstein_gradient
    (Engine := B.engine) x

/-- The L-function bridge still identifies the twisted partition with the twisted Euler product. -/
@[rep_depth transport]
theorem twistedPartitionFunction_eq_twistedEulerProduct :
    B.lfunction.twistedPacket.twistedPartitionFunction =
      twistedEulerProduct
        B.lfunction.twistedPacket.base_bridge.positiveRoots
        B.lfunction.twistedPacket.base_bridge.temperature.s
        B.lfunction.twistedPacket.gauge := by
  exact B.lfunction.twistedPartitionFunction_eq_twistedEulerProduct

/-- The L-function bridge still exposes the character identity for the partition packet. -/
@[rep_depth transport]
theorem packet_partitionFunction_is_souriau_character :
    B.lfunction.packet.representation.partitionFunction B.lfunction.packet.beta =
      B.lfunction.packet.representation.character
        (B.lfunction.packet.representation.thermalElement B.lfunction.packet.beta) :=
  B.lfunction.packet_partitionFunction_is_souriau_character

/-- The L-function bridge still exposes the prime Euler-product denominator readout. -/
@[rep_depth transport]
theorem packet_denominator_is_prime_euler_product :
    B.lfunction.packet.denominatorBridge.weylDenominator =
      B.lfunction.packet.denominatorBridge.primeEulerProduct :=
  B.lfunction.packet_denominator_is_prime_euler_product

end Bridge

end InfoGeometry.Canonical.GrandCanonicalLFunctionFlowBridge
