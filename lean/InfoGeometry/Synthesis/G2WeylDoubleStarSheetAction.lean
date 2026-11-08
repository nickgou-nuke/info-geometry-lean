/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter
import InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
import InfoGeometry.Lie.CanonicalZornG2ToMatrixBridge
import InfoGeometry.Synthesis.G2DoubleStarSedenionW24Bridge

/-!
# The order-12 `G₂` Weyl action on the 24-element double-star sheet carrier

The finite `G₂` root carrier is equivalent to the twelve native nonzero-root
indices, hence to the double-star index subtype. Pairing that equivalence with
the identity on `Fin 2` transports the existing Weyl action to the actual
24-element carrier. The action preserves the sheet coordinate. No
cyclotomic endomorphism or split-sedenion multiplication is identified here.
-/

noncomputable section

namespace InfoGeometry.Synthesis.G2WeylDoubleStarSheetAction

open InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
open InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2 (weylMul)
open InfoGeometry.Lie.CanonicalZornRootSystemComparison
open InfoGeometry.Lie.CanonicalZornG2ToMatrixBridge
open InfoGeometry.Synthesis.G2DoubleStarSedenionW24Bridge

/-- The existing finite root carrier identified with the native double-star
root-index subtype through the native nonzero-index readout. -/
def rootToDoubleStar : G2Root ≃
    {i : Fin 14 // i ∈ InfoGeometry.Lie.G2DoubleStarRootDecomposition.doubleStarIndices} :=
  InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment.rootIndexEquiv.trans
    (nativeRootIndexEquiv.trans doubleStarRootIndexEquiv.symm)

/-- The corresponding equivalence after adjoining the two sheet labels. -/
def rootSheetEquiv : G2Root × Fin 2 ≃ DoubleStarSheetCarrier :=
  Equiv.prodCongr rootToDoubleStar (Equiv.refl (Fin 2))

/-- Transport each existing root Weyl equivalence across the double-star
carrier equivalence, acting trivially on the sheet coordinate. -/
def weylActionOnSheets (p : WeylG2) :
    DoubleStarSheetCarrier ≃ DoubleStarSheetCarrier :=
  rootSheetEquiv.symm.trans
    (Equiv.prodCongr (weylRootActionEquiv p) (Equiv.refl (Fin 2))) |>.trans
      rootSheetEquiv

theorem weylActionOnSheets_preserves_sheet (p : WeylG2)
    (x : DoubleStarSheetCarrier) :
    (weylActionOnSheets p x).2 = x.2 := by
  simp [weylActionOnSheets, rootSheetEquiv]

theorem weylActionOnSheets_mul (p q : WeylG2) :
    weylActionOnSheets (weylMul p q) =
      (weylActionOnSheets q).trans (weylActionOnSheets p) := by
  apply Equiv.ext
  intro x
  change (rootToDoubleStar
      (weylRootActionEquiv (weylMul p q) (rootToDoubleStar.symm x.1)), x.2) =
    (rootToDoubleStar
      (weylRootActionEquiv p
        (rootToDoubleStar.symm
          (rootToDoubleStar
            (weylRootActionEquiv q (rootToDoubleStar.symm x.1))))), x.2)
  apply Prod.ext
  · exact congrArg rootToDoubleStar
      (by
        rw [weylRootActionEquiv_apply, weylRootActionEquiv_apply,
          rootToDoubleStar.symm_apply_apply,
          weylRootAction_mul_semidirect]
        rfl)
  · rfl

end InfoGeometry.Synthesis.G2WeylDoubleStarSheetAction

end
