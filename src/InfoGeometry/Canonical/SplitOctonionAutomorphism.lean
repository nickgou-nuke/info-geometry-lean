/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SplitOctonionAutomorphismCore
import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Lie.RealSplitOctonionG2Classification
import InfoGeometry.Lie.RealSplitOctonionDerivationWitness

/-!
# Real split-octonion automorphisms on the canonical Zorn carrier

This file starts the canonical real automorphism lane for
`Aut(𝕆_s(ℝ))`, using the repository's canonical Zorn carrier
`InfoGeometry.Canonical.ZornMatrix ℝ`.

Closed here:
* the real split-octonion carrier abbreviation;
* the determinant/norm coordinate readout `detZ = a*b - x·y`;
* external predicates for unit, product, and determinant preservation;
* the data-level automorphism group as the subgroup of real linear equivalences
  preserving `1` and the Zorn product;
* real readback theorems showing every group element preserves `1` and product.

Open debt, deliberately not hidden in structure fields:
* derivation/Lie-algebra identification with split real `𝔤₂`;
* future group-level target: identify this automorphism group with the split real
  form `G_{2(2)}` after the Lie/derivation layer is constructed.
-/

noncomputable section

namespace InfoGeometry.Canonical

variable {R : Type} [CommRing R]

/-- Every real split-octonion automorphism preserves the Zorn determinant. -/
@[simp] theorem RealSplitOctonionAut.preserves_detZ
    (φ : RealSplitOctonionAut) (x : SplitOctonionReal) :
    ZornMatrix.detZ ((φ : SplitOctonionAutCandidate ℝ) x) =
      ZornMatrix.detZ x := by
  let ψ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut :=
    ⟨(φ : SplitOctonionAutCandidate ℝ), by
      intro X Y
      simpa [InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.IsRealZornCompositionAut,
        InfoGeometry.Canonical.ZornMatrix.mul]
        using φ.2.2 X Y⟩
  exact InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_det
    (φ := ψ) x

/-- Any real split-octonion automorphism preserves the Zorn null cone. -/
@[simp] theorem RealSplitOctonionAut.preserves_null
    (φ : RealSplitOctonionAut) (x : SplitOctonionReal) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull
      (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3)
      ((φ : SplitOctonionAutCandidate ℝ) x) ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull
        (InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3) x := by
  unfold InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull
  constructor
  · intro h
    calc
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 x =
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
            InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
            ((φ : SplitOctonionAutCandidate ℝ) x) := by
        symm
        exact RealSplitOctonionAut.preserves_detZ φ x
      _ = 0 := h
  · intro h
    calc
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
          ((φ : SplitOctonionAutCandidate ℝ) x) =
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
            InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 x := by
        exact RealSplitOctonionAut.preserves_detZ φ x
      _ = 0 := h

/-- Canonical-chain readback into the exact computer-algebra real Lie packet. -/
theorem realSplitOctonionLiePacket_readback :
    (∀ X Y : InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.SplitOct,
      InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.normZ
          (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.mulZ X Y) =
        InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.normZ X *
          InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.normZ Y) ∧
      Module.finrank ℝ
        InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations = 14 ∧
      InfoGeometry.Lie.SplitOctonionStandardDerivation.standardDerivationSpan = ⊤ ∧
      InfoGeometry.Lie.RealSplitOctonionG2Classification.currentRealClassificationStatus =
        InfoGeometry.Lie.RealSplitOctonionG2Classification.RealClassificationStatus.exactNativeLieAlgebra := by
  exact ⟨
    (fun X Y => InfoGeometry.Lie.RealSplitOctonionG2Classification.split_octonion_norm_composition X Y),
    InfoGeometry.Lie.RealSplitOctonionG2Classification.canonical_split_octonion_derivation_finrank,
    InfoGeometry.Lie.RealSplitOctonionG2Classification.standard_split_octonion_derivations_span,
    InfoGeometry.Lie.RealSplitOctonionG2Classification.current_status_is_exactNativeLieAlgebra⟩

/-- Canonical-chain readback into the native real derivation witness. -/
theorem realSplitOctonionDerivationWitness_readback :
    (∀ X Y : InfoGeometry.Lie.RealSplitOctonionDerivationWitness.SplitOctReal,
      InfoGeometry.Lie.RealSplitOctonionDerivationWitness.rot01Real (X + Y) =
        InfoGeometry.Lie.RealSplitOctonionDerivationWitness.rot01Real X +
          InfoGeometry.Lie.RealSplitOctonionDerivationWitness.rot01Real Y) ∧
      (∀ X : InfoGeometry.Lie.RealSplitOctonionDerivationWitness.SplitOctReal,
        InfoGeometry.Lie.RealSplitOctonionDerivationWitness.rot01Real (-X) =
          -InfoGeometry.Lie.RealSplitOctonionDerivationWitness.rot01Real X) ∧
        ∀ X Y : InfoGeometry.Lie.RealSplitOctonionDerivationWitness.SplitOctReal,
          InfoGeometry.Lie.RealSplitOctonionDerivationWitness.rot01Real (X * Y) =
            InfoGeometry.Lie.RealSplitOctonionDerivationWitness.rot01Real X * Y +
              X * InfoGeometry.Lie.RealSplitOctonionDerivationWitness.rot01Real Y := by
  exact InfoGeometry.Lie.RealSplitOctonionDerivationWitness.realSplitOctonionDerivationPacket_packet

end InfoGeometry.Canonical
