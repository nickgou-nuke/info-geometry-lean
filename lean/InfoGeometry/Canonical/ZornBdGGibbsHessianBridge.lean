/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
import InfoGeometry.Canonical.ZornNativeBdGCompatibility
import InfoGeometry.Canonical.ZornBdGDerivationBridge
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

/-!
# Zorn BdG pairing directions and the Gibbs log-partition Hessian

The carrier is the full noncommutative operator algebra on `FinKetSpace (Fin 4)`.
The existing Zorn Pauli-block readout gives operators in this carrier by the
canonical matrix/operator correspondence.  This module composes that readout
with the proved finite Gibbs Hessian theorem: a compatible Zorn pairing
variation is a self-adjoint Hessian direction, and its log-partition response
is its centered BKM covariance.

This is a finite-stage operator statement.  It identifies a BKM response,
not a spectral gap, and asserts no infinite-dimensional or continuum result.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.ZornBdGGibbsHessianBridge

open SouriauOnsagerBKM
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredFrechetBKMBridge
open InfoGeometry.Canonical.ZornBdGDerivationBridge.ZornVectorMatrixAlgebra
open InfoGeometry.Canonical.ZornBdGDerivationBridge.ZornBdGSolderingReadout
open InfoGeometry.Canonical.ZornNativeBdGCompatibility
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

abbrev ZornC := Zorn ℂ
abbrev GibbsOp := FiniteOperatorAlgebra 4

/-- Matrix/operator realization of the existing four-dimensional Zorn BdG
block readout in the Gibbs operator carrier. -/
noncomputable def zornBdGOperator (Z : ZornC) : GibbsOp :=
  CblinfunMatrix.matrixOp (bdgReadout Z)

/-- The Zorn compatibility and Hermitian-normal-channel hypotheses make the
actual block readout self-adjoint as an operator in the Gibbs carrier. -/
theorem zornBdGOperator_isSelfAdjoint
    (Z : ZornC) (hCompat : IsBdGCompatible Z)
    (hNormal : IsHermitianNormalChannel Z) :
    IsSelfAdjoint (zornBdGOperator Z) := by
  change (starRingEnd ℂ) Z.a = Z.a at hNormal
  have hMatrix : Matrix.conjTranspose (bdgReadout Z) = bdgReadout Z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose, Matrix.transpose, bdgReadout,
        hCompat.1, hCompat.2, hNormal, Complex.conj_I] <;> ring
  apply CblinfunMatrix.matrixOfOp_injective
  change CblinfunMatrix.matrixOfOp
      (ContinuousLinearMap.adjoint
        (CblinfunMatrix.matrixOp (bdgReadout Z))) =
    CblinfunMatrix.matrixOfOp
      (CblinfunMatrix.matrixOp (bdgReadout Z))
  simp only [CblinfunMatrix.matrixOfOp_adjoint,
    CblinfunMatrix.matrixOfOp_matrixOp]
  exact hMatrix

/-- Extract the off-diagonal pairing direction of a Zorn element by retaining
its two Pauli pairing channels and setting the normal channels to zero. -/
def pairingVariationSource (Z : ZornC) : ZornC where
  a := 0
  u := Z.u
  v := Z.v
  b := 0

/-- Compatibility of the source Zorn element makes its off-diagonal pairing
variation compatible with the BdG adjoint-block convention. -/
theorem pairingVariationSource_compatible
    (Z : ZornC) (hCompat : IsBdGCompatible Z) :
    IsBdGCompatible (pairingVariationSource Z) := by
  change (pairingVariationSource Z).b =
      -star (pairingVariationSource Z).a ∧
    ∀ i, (pairingVariationSource Z).v i =
      star ((pairingVariationSource Z).u i)
  constructor
  · simp [pairingVariationSource]
  · exact hCompat.2

/-- The zero-normal pairing variation has a Hermitian normal channel. -/
theorem pairingVariationSource_normal_selfAdjoint (Z : ZornC) :
    IsHermitianNormalChannel (pairingVariationSource Z) := by
  simp [IsHermitianNormalChannel, pairingVariationSource]

/-- The Zorn pairing-sector direction is a self-adjoint operator whenever its
upper and lower Pauli channels satisfy the BdG compatibility law. -/
theorem zornPairingVariation_isSelfAdjoint
    (Z : ZornC) (hCompat : IsBdGCompatible Z) :
    IsSelfAdjoint (zornBdGOperator (pairingVariationSource Z)) :=
  zornBdGOperator_isSelfAdjoint (pairingVariationSource Z)
    (pairingVariationSource_compatible Z hCompat)
    (pairingVariationSource_normal_selfAdjoint Z)

/-- The log-partition Hessian along a Zorn pairing-sector perturbation is the
centered BKM covariance in the faithful Gibbs state of a Zorn-derived BdG
operator.  Positive partition is stated explicitly, as required by the Gibbs
owner; no spectral-gap conclusion is implicit. -/
theorem zornPairing_hessian_eq_centeredBKM
    (Z Hsource : ZornC)
    (hZ : IsBdGCompatible Z)
    (hHcompat : IsBdGCompatible Hsource)
    (hHnormal : IsHermitianNormalChannel Hsource)
    (hPartition : 0 < gibbsPartitionReal (zornBdGOperator Hsource))
    (B : GibbsOp) :
    (secondFDerivLogPartitionReadout
      (zornBdGOperator Hsource)
      (zornBdGOperator (pairingVariationSource Z)) B).re =
      centeredBKMRealCovariance
        (faithfulGibbsDensity (zornBdGOperator Hsource)
          (zornBdGOperator_isSelfAdjoint Hsource hHcompat hHnormal)
          hPartition)
        (continuous_faithfulGibbsDensity_rpow
          (zornBdGOperator Hsource)
          (zornBdGOperator_isSelfAdjoint Hsource hHcompat hHnormal)
          hPartition)
        (zornBdGOperator (pairingVariationSource Z)) B := by
  exact secondFDeriv_logPartition_apply_eq_centeredBKM
    (zornBdGOperator Hsource)
    (zornBdGOperator_isSelfAdjoint Hsource hHcompat hHnormal)
    hPartition
    (zornBdGOperator (pairingVariationSource Z)) B
    (zornPairingVariation_isSelfAdjoint Z hZ)

/-- In particular, the diagonal Hessian response of a Zorn pairing direction
is nonnegative, by positivity of the centered BKM covariance. -/
theorem zornPairing_hessian_self_nonneg
    (Z Hsource : ZornC)
    (hZ : IsBdGCompatible Z)
    (hHcompat : IsBdGCompatible Hsource)
    (hHnormal : IsHermitianNormalChannel Hsource)
    (hPartition : 0 < gibbsPartitionReal (zornBdGOperator Hsource)) :
    0 ≤ (secondFDerivLogPartitionReadout
      (zornBdGOperator Hsource)
      (zornBdGOperator (pairingVariationSource Z))
      (zornBdGOperator (pairingVariationSource Z))).re := by
  rw [zornPairing_hessian_eq_centeredBKM Z Hsource hZ hHcompat hHnormal
    hPartition (zornBdGOperator (pairingVariationSource Z))]
  rw [← centeredFrechetResponse_eq_centeredBKMRealCovariance
    (zornBdGOperator Hsource)
    (zornBdGOperator_isSelfAdjoint Hsource hHcompat hHnormal)
    hPartition
    (zornBdGOperator (pairingVariationSource Z))
    (zornBdGOperator (pairingVariationSource Z))
    (zornPairingVariation_isSelfAdjoint Z hZ)]
  exact centeredFrechetResponse_nonneg_selfAdjoint
    (zornBdGOperator Hsource)
    (zornBdGOperator_isSelfAdjoint Hsource hHcompat hHnormal)
    hPartition
    (zornBdGOperator (pairingVariationSource Z))
    (zornPairingVariation_isSelfAdjoint Z hZ)

end InfoGeometry.Canonical.ZornBdGGibbsHessianBridge
