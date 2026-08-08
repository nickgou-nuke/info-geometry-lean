import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeSuperalgebra
import InfoGeometry.Arithmetic.KudinoorWittenIndexBridge
import InfoGeometry.Canonical.WeylSupertraceOwner
import InfoGeometry.Canonical.WeylCharacterEquivalence
import InfoGeometry.Canonical.PrimonSupertrace

/-!
# InfoGeometry.Canonical.InverseZetaWeylMasterKey

Finite master-key bridge for the inverse-zeta / Witten / Weyl corridor.

This file stays theorem-safe:

* the prime-bit Mobius parity theorem is the finite squarefree register owner;
* the finite Witten cancellation theorem is the finite prime-register supertrace;
* the finite prime Weyl denominator identity is the prime-root-lattice shadow;
* the finite Weyl-denominator/parity-supertrace identity is carried by the
  existing Weyl-supertrace owner;
* the analytic inverse-zeta statement remains an explicit `GradedPartitionFunction`
  property rather than a global RH theorem.

It does not prove analytic continuation, the full Weyl character formula, or
the continuum Hilbert-Polya conjecture.

#### BUCKET 1: CLOSED FINITE THEOREMS
`master_key_summary` conjoins already-owned finite theorem surfaces.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`wittenIndex_eq_inverseZeta` depends on the explicit
`GradedPartitionFunction` property and the supplied equality between the local
Witten-index readout and its supertrace.

#### BUCKET 3: OPEN CLOSURE DEBT
Analytic `1 / zeta`, McKean-Singer, Weyl-Kac, Hilbert-Polya, and RH remain open
outside this finite packet.
-/

namespace InfoGeometry.Canonical.InverseZetaWeylMasterKey

open scoped BigOperators
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.PrimeSuperalgebra
open InfoGeometry.Canonical.WeylSupertraceOwner
open InfoGeometry.Canonical.WeylCharacterEquivalence
open InfoGeometry.Canonical.PrimonSupertrace

/--
Finite master-key packet for the inverse-zeta / Witten / Weyl corridor.

This packages the source-owned finite identities without claiming the full
analytic limit.
-/
@[rep_depth thermo]
structure MasterKeyPacket where
  primeRegister : PrimeRegister
  hNonempty : primeRegister.primes.Nonempty
  beta : ℝ
  primeRootWeights : ℕ → ℝ
  thermalLattice : InfoGeometry.Canonical.FormalPrimeRootSystem.FormalPrimeRootLattice
  thermalEvaluation :
    InfoGeometry.Canonical.SouriauThermalEvaluation.SouriauThermalEvaluation
      thermalLattice
  gradedPartition : InfoGeometry.Canonical.PrimonSupertrace.GradedPartitionFunction ℝ
  wittenIndex : ℝ
  wittenIndex_eq_supertrace : wittenIndex = gradedPartition.supertrace

namespace MasterKeyPacket

variable (P : MasterKeyPacket)

/-- The Mobius parity of the represented squarefree prime register. -/
@[rep_depth thermo]
theorem mobius_parity_eq_fermionParity :
    ArithmeticFunction.moebius
        (representedNat P.primeRegister) =
      fermionParity P.primeRegister :=
  mobius_representedNat_eq_fermionParity P.primeRegister

/-- The graded partition supertrace recovers the inverse-zeta property. -/
@[rep_depth thermo]
theorem wittenIndex_eq_inverseZeta :
    P.wittenIndex = P.gradedPartition.zeta_inverse := by
  rw [P.wittenIndex_eq_supertrace, P.gradedPartition.mckean_singer]

end MasterKeyPacket

/--
Finite theorem packet for the inverse-zeta / Witten / Weyl master key.

The claims are exactly the already-owned finite theorem surfaces, conjoined so
the boundary between finite proof and analytic property stays explicit.
-/
@[rep_depth thermo]
theorem master_key_summary (P : MasterKeyPacket) :
    ArithmeticFunction.moebius (representedNat P.primeRegister) =
      fermionParity P.primeRegister ∧
    (∑ S ∈ P.primeRegister.primes.powerset, (-1 : ℤ) ^ S.card) = 0 ∧
    InfoGeometry.Arithmetic.PrimeSuperalgebra.finitePrimeSupertrace
        P.primeRegister P.beta =
      InfoGeometry.Arithmetic.PrimeSuperalgebra.finitePrimeDenominator
        P.primeRegister P.beta ∧
    InfoGeometry.Canonical.FormalPrimeRootSystem.weylDenominatorProduct
        (InfoGeometry.Arithmetic.PrimeBitWittenIndex.primeRootLattice P.primeRegister)
        P.primeRootWeights =
      InfoGeometry.Canonical.FormalPrimeRootSystem.weylAlternatingSum
        (InfoGeometry.Arithmetic.PrimeBitWittenIndex.primeRootLattice P.primeRegister)
        P.primeRootWeights ∧
    InfoGeometry.Canonical.SouriauThermalEvaluation.finiteEvaluatedDenominator
        P.thermalEvaluation =
      InfoGeometry.Canonical.SouriauThermalEvaluation.finiteEvaluatedAlternatingSum
        P.thermalEvaluation ∧
    P.wittenIndex = P.gradedPartition.zeta_inverse := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact MasterKeyPacket.mobius_parity_eq_fermionParity P
  · exact InfoGeometry.Arithmetic.PrimeBitWittenIndex.finite_witten_supertrace_cancel
      P.primeRegister P.hNonempty
  · exact InfoGeometry.Arithmetic.PrimeSuperalgebra.finitePrimeSupertrace_eq_denominator
      P.primeRegister P.beta
  · exact InfoGeometry.Arithmetic.PrimeBitWittenIndex.finite_prime_weyl_denominator_identity
      P.primeRegister P.primeRootWeights
  · exact InfoGeometry.Canonical.WeylSupertraceOwner.finiteWeylDenominator_eq_finiteParitySupertrace
      P.thermalLattice P.thermalEvaluation
  · exact MasterKeyPacket.wittenIndex_eq_inverseZeta P

end InfoGeometry.Canonical.InverseZetaWeylMasterKey
