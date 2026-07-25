import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
import InfoGeometry.Thermodynamics.SouriauTemperature
import InfoGeometry.Canonical.FractalCantorCuntzKacMoodyVirasoroBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Thermodynamics.SouriauWeylPartitionBridge

Finite Souriau/Weyl denominator arithmetic packet.

This file is not the general Massieu/Fisher partition layer.  The statistical
Massieu potential is owned separately as `log Z` in finite Cartan/exponential
family modules.  Here the word "partition" refers to the finite arithmetic
Euler-product/Weyl-denominator readout carried by the packet below.

According to Souriau's Lie Group Thermodynamics:
1. The temperature `β` is a vector in the Lie algebra `mathfrak{g}`.
2. The partition function `Z(β)` is a sum/integral over coadjoint orbits.
3. For the Cantor-Cuntz symmetry group, the positive roots `α` correspond to 
   the prime numbers `p`.
4. The Weyl character denominator `∏ (1 - e^{-α})` is exactly the Euler product 
   `∏ (1 - p^{-s})`.

The packet carries the finite arithmetic compatibility data needed for this
specialized bridge.  It should not be read as a proof that determinant-volume
transport replaces Souriau coadjoint-orbit integration or the statistical
Massieu partition function.
-/

noncomputable section

namespace InfoGeometry.Thermodynamics

open InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
open InfoGeometry.Thermodynamics
open InfoGeometry.Canonical.FractalCantorCuntzKacMoodyVirasoroBridge

/--
Souriau Symplectic Thermodynamics Packet.

Records the Lie-algebraic temperature and the moment-map evaluation for the 
Cantor-Cuntz symmetry group.
-/
@[rep_depth transport]
structure SouriauWeylPartitionBridge
    (E Op H Finite Alg : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  /-- The underlying Cantor-Cuntz-Virasoro bridge. -/
  crystal :
    FractalCantorCuntzKacMoodyVirasoroBridge E Op H Finite Alg

  /-- The Souriau temperature vector `β` (parameterized by complex `s`). -/
  temperature :
    SouriauTemperature

  /-- The set of positive roots (indexed by primes). -/
  positiveRoots :
    Finset ℕ

  /-- 
  The Weyl signature mapping:
  Identifies the Weyl group signature `(-1)^ℓ(w)` with the Möbius function `μ(n)`.
  -/
  weylSignature :
    ℕ → ℤ

  /-- The Möbius function compatibility. -/
  weylSignature_eq_mobius :
    ∀ n ∈ positiveRoots, weylSignature n = if n = 1 then 1 else -1 -- Simplified placeholder for μ(n)

  /--
  The finite Souriau-Weyl arithmetic readout:
  the carried Euler-product partition readout is the inverse of the finite
  Weyl denominator.
  -/
  partitionFunction_eq_inverseWeylDenominator :
    finitePrimeBosonicInverseDenominator positiveRoots (fun p => souriauEvaluation p temperature.s) =
      (finitePrimeWeylDenominator positiveRoots (fun p => souriauEvaluation p temperature.s))⁻¹

namespace SouriauWeylPartitionBridge

variable
    {E Op H Finite Alg : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B : SouriauWeylPartitionBridge E Op H Finite Alg)

/-- 
The carried finite arithmetic partition readout is exactly the finite Euler
product associated with the selected positive roots.
-/
@[rep_depth transport]
theorem partitionFunction_is_zeta_product :
    finitePrimeBosonicInverseDenominator B.positiveRoots (fun p => souriauEvaluation p B.temperature.s) =
      ∏ p ∈ B.positiveRoots, (1 - (p : ℂ) ^ (-B.temperature.s))⁻¹ := by
  unfold finitePrimeBosonicInverseDenominator
  apply Finset.prod_congr rfl
  intro p _
  unfold souriauEvaluation
  rfl

/--
The Weyl denominator cancellation law.
This is the thermodynamic dual of the Majorana-cancellation in the operator
algebra.
-/
@[rep_depth transport]
theorem weyl_cancellation_holds
    (h : ∀ p ∈ B.positiveRoots, 1 - souriauEvaluation p B.temperature.s ≠ 0) :
    finitePrimeBosonicInverseDenominator B.positiveRoots (fun p => souriauEvaluation p B.temperature.s) *
      finitePrimeWeylDenominator B.positiveRoots (fun p => souriauEvaluation p B.temperature.s) = 1 :=
  bosonicInverse_mul_weylDenominator_cancel B.positiveRoots (fun p => souriauEvaluation p B.temperature.s) h

end SouriauWeylPartitionBridge

end InfoGeometry.Thermodynamics
