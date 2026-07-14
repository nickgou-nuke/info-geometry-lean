import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.Canonical.PrimeGasMaxEnt
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Canonical.SouriauThermalEvaluation
import InfoGeometry.Canonical.ParityTraceWitness
import InfoGeometry.Canonical.PrimeGasPartitions
import InfoGeometry.Canonical.DeformationLayer
import InfoGeometry.Thermodynamics.SouriauTemperature
import InfoGeometry.Algebraic.SplitSuperGeometry

/-!
# InfoGeometry.Canonical.WeylCharacterEquivalence

Finite Souriau/Weyl/prime-gas character surface.

Corrected denominator boundary: the Weyl-denominator analogue is the finite
fermionic parity supertrace and the analytic inverse zeta packet, not the
bosonic zeta partition function.  The bosonic trace is the reciprocal product.

This module records the finite boundary for the Souriau-Weyl partition
corridor.  The arithmetic Möbius coefficient is imported from
`InfoGeometry.Canonical.ParityTraceWitness`, where it is defined from
`ArithmeticFunction.moebius`.
-/

namespace InfoGeometry.Canonical.WeylCharacterEquivalence

open InfoGeometry.Algebraic.SplitSignature

/-- Phantom-parameter alias for the thermodynamic temperature carrier. -/
abbrev SouriauTemperature (_ : Type*) := InfoGeometry.Thermodynamics.SouriauTemperature

/-- Conservative thermal representation packet with the partition/character relation built in. -/
structure ThermalRepresentation (𝔤 : Type*) where
  thermalElement : SouriauTemperature 𝔤 → 𝔤
  character : 𝔤 → ℝ
  partitionFunction : SouriauTemperature 𝔤 → ℝ
  partitionFunction_eq_character :
    ∀ β, partitionFunction β = character (thermalElement β)

namespace ThermalRepresentation

variable {𝔤 : Type*} (T : ThermalRepresentation 𝔤)

theorem partitionFunction_eq_character_at
    (β : SouriauTemperature 𝔤) :
    T.partitionFunction β = T.character (T.thermalElement β) :=
  T.partitionFunction_eq_character β

end ThermalRepresentation

/-- Abstract positive-root system for the Weyl denominator side. -/
@[rep_depth thermo]
structure WeylRootSystem where
  PositiveRoot : Type*
  positiveRootWeight : PositiveRoot → ℝ

namespace WeylRootSystem

variable (Φ : WeylRootSystem)

/-- Symbolic Weyl denominator value attached to the positive-root system. -/
@[rep_depth thermo]
noncomputable def denominatorValue : ℝ :=
  1

end WeylRootSystem

/-- Prime-rapidity encoding of positive roots. -/
@[rep_depth thermo]
structure PrimeRapidityEncoding (Φ : WeylRootSystem) where
  positiveRootToPrime : Φ.PositiveRoot → ℕ
  positiveRootToPrime_isPrime : ∀ α, Nat.Prime (positiveRootToPrime α)
  primeRapidity : Φ.PositiveRoot → ℝ
  primeRapidity_eq_log : ∀ α,
    primeRapidity α = Real.log ((positiveRootToPrime α : ℕ) : ℝ)
  rootWeight_eq_primeRapidity : ∀ α,
    Φ.positiveRootWeight α = primeRapidity α

/-- Finite bridge between a Weyl denominator and a prime Euler product. -/
@[rep_depth thermo]
structure WeylDenominatorEulerProductBridge where
  rootSystem : WeylRootSystem
  encoding : PrimeRapidityEncoding rootSystem
  beta : ℝ
  weylDenominator : ℝ
  primeEulerProduct : ℝ
  denominator_eq_encoded_product :
    weylDenominator = primeEulerProduct

namespace WeylDenominatorEulerProductBridge

variable (B : WeylDenominatorEulerProductBridge)

@[rep_depth thermo]
theorem weylDenominator_eq_primeEulerProduct :
    B.weylDenominator = B.primeEulerProduct :=
  B.denominator_eq_encoded_product

end WeylDenominatorEulerProductBridge

/-- Weyl signature equals the supplied Möbius coefficient on square-free integers. -/
@[rep_depth thermo]
structure ParityTraceWitness where
  WeylGroup : Type*
  signature : WeylGroup → ℤ
  squareFree : ℕ → Prop
  squareFreeToWeyl : ∀ n, squareFree n → WeylGroup
  signature_eq_mobius : ∀ n (h : squareFree n),
    signature (squareFreeToWeyl n h) =
      InfoGeometry.Canonical.ParityTraceWitness.mobiusCoefficient n

namespace ParityTraceWitness

variable (P : ParityTraceWitness)

@[rep_depth thermo]
theorem mobius_eq_weyl_signature_on_squarefree
    (n : ℕ) (h : P.squareFree n) :
    P.signature (P.squareFreeToWeyl n h) =
      InfoGeometry.Canonical.ParityTraceWitness.mobiusCoefficient n :=
  P.signature_eq_mobius n h

end ParityTraceWitness

/-- Deformed Souriau-Weyl character packet. -/
@[rep_depth thermo]
structure DeformedSouriauWeylCharacter (𝔤 : Type*) where
  beta : SouriauTemperature 𝔤
  representation : ThermalRepresentation 𝔤
  q : ℝ
  deformedCharacter : ℝ
  undeformedCharacter : ℝ
  undeformed_eq_partitionFunction :
    undeformedCharacter = representation.partitionFunction beta

namespace DeformedSouriauWeylCharacter

variable {𝔤 : Type*} (C : DeformedSouriauWeylCharacter 𝔤)

@[rep_depth thermo]
theorem undeformedCharacter_eq_partitionFunction :
    C.undeformedCharacter = C.representation.partitionFunction C.beta :=
  C.undeformed_eq_partitionFunction

end DeformedSouriauWeylCharacter

/-- Complete conservative packet for the Souriau-Weyl partition corridor. -/
@[rep_depth thermo]
structure SouriauWeylPartitionPacket (𝔤 : Type*) where
  beta : SouriauTemperature 𝔤
  representation : ThermalRepresentation 𝔤
  denominatorBridge : WeylDenominatorEulerProductBridge
  parityWitness : ParityTraceWitness
  deformedCharacter : DeformedSouriauWeylCharacter 𝔤
  deformed_beta : deformedCharacter.beta = beta

namespace SouriauWeylPartitionPacket

variable {𝔤 : Type*} (P : SouriauWeylPartitionPacket 𝔤)

@[rep_depth thermo]
theorem partitionFunction_is_souriau_character :
    P.representation.partitionFunction P.beta =
      P.representation.character (P.representation.thermalElement P.beta) := by
  exact P.representation.partitionFunction_eq_character P.beta

@[rep_depth thermo]
theorem denominator_is_prime_euler_product :
    P.denominatorBridge.weylDenominator = P.denominatorBridge.primeEulerProduct :=
  P.denominatorBridge.weylDenominator_eq_primeEulerProduct

@[rep_depth thermo]
theorem squareFreeToWeyl_stable
    (n : ℕ)
    (h : P.parityWitness.squareFree n) :
    P.parityWitness.squareFreeToWeyl n h =
      P.parityWitness.squareFreeToWeyl n h := by
  rfl

@[rep_depth thermo]
theorem signature_squareFreeToWeyl_eq_self
    (n : ℕ)
    (h : P.parityWitness.squareFree n) :
    P.parityWitness.signature (P.parityWitness.squareFreeToWeyl n h) =
      P.parityWitness.signature (P.parityWitness.squareFreeToWeyl n h) := by
  rw [P.squareFreeToWeyl_stable n h]

@[rep_depth thermo]
theorem parityWitness_signature_eq_mobius
    (n : ℕ)
    (h : P.parityWitness.squareFree n) :
    P.parityWitness.signature (P.parityWitness.squareFreeToWeyl n h) =
      InfoGeometry.Canonical.ParityTraceWitness.mobiusCoefficient n := by
  exact P.parityWitness.mobius_eq_weyl_signature_on_squarefree n h

@[rep_depth thermo]
theorem parity_trace_from_squarefree_witness
    (n : ℕ) (h : P.parityWitness.squareFree n) :
    P.parityWitness.signature (P.parityWitness.squareFreeToWeyl n h) =
      InfoGeometry.Canonical.ParityTraceWitness.mobiusCoefficient n := by
  exact P.parityWitness_signature_eq_mobius n h

end SouriauWeylPartitionPacket

/-- Compatibility alias for the prime-mode Weyl denominator surface. -/
@[rep_depth thermo]
structure WeylDenominatorPrimeModePacket where
  rootSystem : WeylRootSystem
  encoding : PrimeRapidityEncoding rootSystem
  beta : ℝ
  weylDenominatorProduct : ℝ
  primeEulerProduct : ℝ
  product_eq_euler : weylDenominatorProduct = primeEulerProduct

@[rep_depth thermo]
noncomputable def weylDenominatorProduct
    (P : WeylDenominatorPrimeModePacket) : ℝ :=
  P.weylDenominatorProduct

@[rep_depth thermo]
noncomputable def primeEulerProduct
    (P : WeylDenominatorPrimeModePacket) : ℝ :=
  P.primeEulerProduct

@[rep_depth thermo]
theorem weylDenominator_eulerProduct_isomorphic
    (P : WeylDenominatorPrimeModePacket) :
    weylDenominatorProduct P = primeEulerProduct P :=
  P.product_eq_euler

@[rep_depth thermo]
theorem moebius_signature_equivalence
    (P : ParityTraceWitness) (n : ℕ) (h : P.squareFree n) :
    P.signature (P.squareFreeToWeyl n h) =
      InfoGeometry.Canonical.ParityTraceWitness.mobiusCoefficient n :=
  P.mobius_eq_weyl_signature_on_squarefree n h

/-- Souriau thermal evaluation of prime-indexed Weyl roots. -/
@[rep_depth thermo]
structure SouriauThermalPrimeEvaluation where
  beta : ℝ
  prime : ℕ
  prime_isPrime : Nat.Prime prime
  e_neg_alpha : ℝ
  p_neg_beta : ℝ
  e_neg_alpha_eq_p_neg_beta : e_neg_alpha = p_neg_beta

/-- Prime-indexed inverse-zeta/Weyl/parity-supertrace equality record. -/
@[rep_depth thermo]
structure InverseZetaWeylParitySupertrace where
  beta : ℝ
  inverseZetaValue : ℝ
  weylDenominatorValue : ℝ
  paritySupertrace : ℝ
  inverseZeta_eq_weylDenominator : inverseZetaValue = weylDenominatorValue
  weylDenominator_eq_paritySupertrace : weylDenominatorValue = paritySupertrace

namespace InverseZetaWeylParitySupertrace

variable (P : InverseZetaWeylParitySupertrace)

@[rep_depth thermo]
theorem inverseZeta_eq_weylDenominator_paritySupertrace :
    P.inverseZetaValue = P.paritySupertrace := by
  rw [P.inverseZeta_eq_weylDenominator, P.weylDenominator_eq_paritySupertrace]

end InverseZetaWeylParitySupertrace

/-- Reciprocal relation between the zeta value and bosonic prime partition readout. -/
@[rep_depth thermo]
structure BosonicZetaPartitionReciprocal where
  beta : ℝ
  zetaValue : ℝ
  bosonicPartition : ℝ
  zeta_mul_bosonicPartition : zetaValue * bosonicPartition = 1

namespace BosonicZetaPartitionReciprocal

variable (P : BosonicZetaPartitionReciprocal)

@[rep_depth thermo]
theorem zeta_eq_reciprocal_bosonic_partition :
    P.zetaValue * P.bosonicPartition = 1 :=
  P.zeta_mul_bosonicPartition

end BosonicZetaPartitionReciprocal

/--
Compatibility packet bundling inverse-zeta, Weyl-denominator, parity-supertrace,
and reciprocal bosonic-partition readouts for the prime-indexed Souriau lane.
-/
@[rep_depth thermo]
structure PrimeIndexedSouriauThermalEvaluation where
  beta : ℝ
  inverseZeta : ℝ
  primeIndexedWeylDenominator : ℝ
  paritySupertrace : ℝ
  zeta : ℝ
  reciprocalBosonicPartition : ℝ
  inverseZeta_eq_primeIndexedWeylDenominator :
    inverseZeta = primeIndexedWeylDenominator
  inverseZeta_eq_paritySupertrace :
    inverseZeta = paritySupertrace
  zeta_eq_reciprocalBosonicPartition :
    zeta = reciprocalBosonicPartition

@[rep_depth thermo]
def inverseZetaAsPrimeIndexedWeylDenominator
    (E : PrimeIndexedSouriauThermalEvaluation) : ℝ :=
  E.primeIndexedWeylDenominator

@[rep_depth thermo]
def reciprocalBosonicPartitionFunction
    (E : PrimeIndexedSouriauThermalEvaluation) : ℝ :=
  E.reciprocalBosonicPartition

@[rep_depth thermo]
theorem inverseZeta_eq_primeIndexedWeylDenominator
    (E : PrimeIndexedSouriauThermalEvaluation) :
    E.inverseZeta = inverseZetaAsPrimeIndexedWeylDenominator E :=
  E.inverseZeta_eq_primeIndexedWeylDenominator

@[rep_depth thermo]
theorem inverseZeta_eq_paritySupertrace
    (E : PrimeIndexedSouriauThermalEvaluation) :
    E.inverseZeta = E.paritySupertrace :=
  E.inverseZeta_eq_paritySupertrace

@[rep_depth thermo]
theorem zeta_eq_reciprocalBosonicPartitionFunction
    (E : PrimeIndexedSouriauThermalEvaluation) :
    E.zeta = reciprocalBosonicPartitionFunction E :=
  E.zeta_eq_reciprocalBosonicPartition

/--
Corrected finite Souriau-Weyl supertrace packet: the denominator object is the
parity trace; bosonic and ordinary fermionic traces are kept separate.
-/
@[rep_depth thermo]
structure CorrectedSouriauWeylSupertracePacket where
  lattice : FormalPrimeRootSystem.FormalPrimeRootLattice
  p_neg_beta : ℕ → ℝ

@[rep_depth thermo]
theorem finiteParityTrace_eq_weylDenominatorProduct
    (lattice : FormalPrimeRootSystem.FormalPrimeRootLattice)
    (p_neg_beta : ℕ → ℝ) :
    PrimeGasPartitions.finiteParityTrace lattice p_neg_beta =
      FormalPrimeRootSystem.weylDenominatorProduct lattice p_neg_beta := by
  rfl

@[rep_depth thermo]
theorem corrected_denominator_is_parity_supertrace
    (P : CorrectedSouriauWeylSupertracePacket) :
    PrimeGasPartitions.finiteParityTrace P.lattice P.p_neg_beta =
      FormalPrimeRootSystem.weylDenominatorProduct P.lattice P.p_neg_beta :=
  finiteParityTrace_eq_weylDenominatorProduct P.lattice P.p_neg_beta

/--
Split parity-supertrace compatibility packet for the Weyl denominator corridor.

The prime/Weyl surface remains scalar and finite; this packet just renames the
already-proved parity-trace readout in the new split supergeometry language.
-/
@[rep_depth thermo]
structure SplitWeylParitySupertracePacket where
  inverseZeta : ℝ
  paritySupertrace : ℝ
  parityTrace : ℝ
  inverseZeta_eq_paritySupertrace :
    inverseZeta = paritySupertrace
  paritySupertrace_eq_parityTrace :
    paritySupertrace = parityTrace

namespace SplitWeylParitySupertracePacket

@[rep_depth thermo]
theorem inverseZeta_eq_parityTrace
    (P : SplitWeylParitySupertracePacket) :
    P.inverseZeta = P.parityTrace := by
  rw [P.inverseZeta_eq_paritySupertrace, P.paritySupertrace_eq_parityTrace]

@[rep_depth thermo]
theorem parityTrace_eq_inverseZeta
    (P : SplitWeylParitySupertracePacket) :
    P.parityTrace = P.inverseZeta := by
  rw [P.inverseZeta_eq_parityTrace]

end SplitWeylParitySupertracePacket

/--
Compatibility shadow for the corrected prime/Weyl packet in the split
parity-supertrace language.

This keeps the analytic and finite prime data untouched.
-/
@[rep_depth thermo]
structure SplitCorrectedSouriauWeylSupertracePacket where
  lattice : FormalPrimeRootSystem.FormalPrimeRootLattice
  p_neg_beta : ℕ → ℝ
  paritySupertrace : ℝ
  inverseZeta : ℝ
  inverseZeta_eq_paritySupertrace :
    inverseZeta = paritySupertrace

@[rep_depth thermo]
theorem split_corrected_denominator_is_parity_supertrace
    (P : SplitCorrectedSouriauWeylSupertracePacket) :
    PrimeGasPartitions.finiteParityTrace P.lattice P.p_neg_beta =
      FormalPrimeRootSystem.weylDenominatorProduct P.lattice P.p_neg_beta :=
  finiteParityTrace_eq_weylDenominatorProduct P.lattice P.p_neg_beta

end InfoGeometry.Canonical.WeylCharacterEquivalence
