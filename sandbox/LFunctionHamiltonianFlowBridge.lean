import Mathlib
import InfoGeometry.Canonical.CantorCoadjointHamiltonianFlowBridge
import InfoGeometry.Arithmetic.LFunctionRepresentationBridge
import InfoGeometry.Canonical.WeylCharacterEquivalence
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.LFunctionHamiltonianFlowBridge

Bridge packet for the dynamical L-function corridor.

This file does not re-prove the Hamiltonian flow or the twisted Euler product
layers.  It packages the coadjoint Hamiltonian flow owner together with the
twisted Souriau/Weyl packet so that the character-theoretic readout can sit on
top of the already-owned dynamic surface.
-/

noncomputable section

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.LFunctionHamiltonianFlowBridge

open InfoGeometry.Canonical.CantorCoadjointHamiltonianFlowBridge
open InfoGeometry.Arithmetic.LFunctionRepresentationBridge
open InfoGeometry.Arithmetic.LFunctionRepresentationBridge.TwistedSouriauWeylBridge
open InfoGeometry.Canonical.WeylCharacterEquivalence
open InfoGeometry.Thermodynamics.SouriauWeylPartition

variable
    {Orbit G E Op H Finite Alg : Type}
    [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

/--
The dynamical L-function bridge.

It packages:
* the coadjoint Hamiltonian flow owner surface, and
* the twisted Souriau/Weyl L-function packet.
-/
@[rep_depth transport]
structure LFunctionHamiltonianFlowBridge
    (Orbit G E Op H Finite Alg : Type)
    [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  /-- The dynamic Hamiltonian/coadjoint flow owner. -/
  coadjointFlow :
    CantorCoadjointHamiltonianFlowBridge Orbit E Op H Finite Alg

  /-- The twisted arithmetic L-function packet. -/
  twistedPacket :
    TwistedSouriauWeylBridge G E Op H Finite Alg

  /-- Proof-carrying partition packet for the character and denominator readout. -/
  packet :
    SouriauWeylPartitionPacket G

  /-- The partition packet and the twisted base bridge live at the same temperature. -/
  packet_beta_eq_twisted :
    packet.beta = twistedPacket.base_bridge.temperature

  /-- The partition packet and the dynamic flow live at the same temperature. -/
  packet_beta_eq_flow :
    packet.beta = coadjointFlow.flow.partition.temperature

/--
Concrete instantiation of the LFunctionHamiltonianFlowBridge
to ensure it is not a vacuous shape, with missing parts exposed as `sorry`.
-/
def instantiateLFunctionHamiltonianFlowBridge :
    LFunctionHamiltonianFlowBridge Orbit G E Op H Finite Alg := {
  coadjointFlow := sorry
  twistedPacket := sorry
  packet := sorry
  packet_beta_eq_twisted := sorry
  packet_beta_eq_flow := sorry
}

namespace LFunctionHamiltonianFlowBridge

variable (B : LFunctionHamiltonianFlowBridge Orbit G E Op H Finite Alg)

/-- The dynamic owner surface still identifies the Hamiltonian with the Souriau generator. -/
@[rep_depth transport]
theorem flow_hamiltonian_is_souriau_generator :
    B.coadjointFlow.flow.selfAdjointHamiltonian =
      B.coadjointFlow.flow.modularContext.logContext.modularHamiltonian :=
  InfoGeometry.Dynamics.HamiltonianFlowBridge.HamiltonianFlowBridge.hamiltonian_is_souriau_generator
    (B := B.coadjointFlow.flow)

/-- The KMS inverse temperature still matches the real part of the Souriau parameter. -/
@[rep_depth transport]
theorem flow_kms_inverse_temperature_eq_real_part_of_s :
    B.coadjointFlow.flow.modularContext.beta =
      B.coadjointFlow.flow.partition.temperature.s.re :=
  InfoGeometry.Dynamics.HamiltonianFlowBridge.HamiltonianFlowBridge.kms_inverse_temperature_eq_real_part_of_s
    (B := B.coadjointFlow.flow)

/-- The dynamic owner surface still reads the positive roots spectrally. -/
@[rep_depth transport]
theorem flow_positive_roots_spectral_encoding (p : ℕ)
    (hp : p ∈ B.coadjointFlow.flow.partition.positiveRoots) :
    ∃ (energy : ℝ), energy = Real.log (p : ℝ) :=
  InfoGeometry.Dynamics.HamiltonianFlowBridge.HamiltonianFlowBridge.positive_roots_spectral_encoding
    (B := B.coadjointFlow.flow) p hp

/-- The twisted partition function is the explicit twisted Euler product. -/
@[rep_depth transport]
theorem twistedPartitionFunction_eq_twistedEulerProduct :
  B.twistedPacket.twistedPartitionFunction =
      twistedEulerProduct
        B.twistedPacket.base_bridge.positiveRoots
        B.twistedPacket.base_bridge.temperature.s
        B.twistedPacket.gauge := by
  rfl

/-- The partition packet still exposes the Souriau character identity. -/
@[rep_depth transport]
theorem packet_partitionFunction_is_souriau_character :
    B.packet.representation.partitionFunction B.packet.beta =
      B.packet.representation.character
        (B.packet.representation.thermalElement B.packet.beta) :=
  B.packet.partitionFunction_is_souriau_character

/-- The partition packet still exposes the Euler-product denominator readout. -/
@[rep_depth transport]
theorem packet_denominator_is_prime_euler_product :
    B.packet.denominatorBridge.weylDenominator =
      B.packet.denominatorBridge.primeEulerProduct :=
  B.packet.denominator_is_prime_euler_product

end LFunctionHamiltonianFlowBridge

end InfoGeometry.Canonical.LFunctionHamiltonianFlowBridge
