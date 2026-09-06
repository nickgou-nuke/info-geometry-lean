import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.Canonical.PrimeGasMaxEnt
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Canonical.SouriauThermalEvaluation
import InfoGeometry.Canonical.ParityTraceData
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
`InfoGeometry.Canonical.ParityTraceData`, where it is defined from
`ArithmeticFunction.moebius`.
-/

namespace InfoGeometry.Canonical.WeylCharacterEquivalence

open InfoGeometry.Algebraic.SplitSignature
open InfoGeometry.Canonical.ParityTraceData

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
structure ParityTraceData where
  WeylGroup : Type _
  signature : WeylGroup → ℤ
  squareFree : ℕ → Prop
  squareFreeToWeyl : ∀ n, squareFree n → WeylGroup
  signature_eq_mobius :
    ∀ n (h : squareFree n),
      signature (squareFreeToWeyl n h) = mobiusCoefficient n

namespace ParityTraceData

variable (P : ParityTraceData)

@[rep_depth thermo]
theorem mobius_eq_weyl_signature_on_squarefree
    (n : ℕ) (h : P.squareFree n) :
    P.signature (P.squareFreeToWeyl n h) =
      mobiusCoefficient n :=
  P.signature_eq_mobius n h

end ParityTraceData

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
structure SouriauWeylPartitionData (𝔤 : Type*) where
  beta : SouriauTemperature 𝔤
  representation : ThermalRepresentation 𝔤
  denominatorBridge : WeylDenominatorEulerProductBridge
  parityData : ParityTraceData
  deformedCharacter : DeformedSouriauWeylCharacter 𝔤
  deformed_beta : deformedCharacter.beta = beta

namespace SouriauWeylPartitionData

variable {𝔤 : Type*} (P : SouriauWeylPartitionData 𝔤)

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
theorem parityData_signature_eq_mobius
    (n : ℕ)
    (h : P.parityData.squareFree n) :
    P.parityData.signature (P.parityData.squareFreeToWeyl n h) =
      mobiusCoefficient n := by
  exact P.parityData.mobius_eq_weyl_signature_on_squarefree n h

end SouriauWeylPartitionData

@[rep_depth thermo]
theorem moebius_signature_equivalence
    (P : ParityTraceData) (n : ℕ) (h : P.squareFree n) :
    P.signature (P.squareFreeToWeyl n h) =
      mobiusCoefficient n :=
  P.mobius_eq_weyl_signature_on_squarefree n h

@[rep_depth thermo]
theorem finiteParityTrace_eq_weylDenominatorProduct
    (lattice : FormalPrimeRootSystem.FormalPrimeRootLattice)
    (p_neg_beta : ℕ → ℝ) :
    PrimeGasPartitions.finiteParityTrace lattice p_neg_beta =
      FormalPrimeRootSystem.weylDenominatorProduct lattice p_neg_beta := by
  rfl

end InfoGeometry.Canonical.WeylCharacterEquivalence
