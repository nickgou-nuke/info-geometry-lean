/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CoordinateWordActionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2CoordinateSignedSign

/-!
# Coordinate inversion sets for finite reflection words

This owner keeps the coordinate sign convention explicit.  In particular,
`signedRootCoordinate (false, α)` is the positive coordinate root, while the
signed reflection owner uses `false` for the negative sign.  No identification
with the older `wordInversionRoots` definition is asserted here.
-/

namespace InfoGeometry.Algebra.Zorn.G2CoordinateWordInversion

open InfoGeometry.Algebra.Zorn.G2CoordinateSignedSign
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2CoordinateWordActionBridge
open InfoGeometry.Algebra.Zorn.G2SignedRootReflections

noncomputable def coordinateWordInversionRoots (word : List Bool) :
    Finset G2Combinatorics.G2PositiveRoot := by
  classical
  exact Finset.univ.filter (fun α =>
    isNegative (coordinateWordAction word (positiveRootInFullCarrier α)))

theorem mem_coordinateWordInversionRoots_iff
    (word : List Bool) (α : G2Combinatorics.G2PositiveRoot) :
    α ∈ coordinateWordInversionRoots word ↔
      isNegative (coordinateWordAction word (positiveRootInFullCarrier α)) := by
  simp [coordinateWordInversionRoots]

theorem mem_coordinateWordInversionRoots_iff_signed
    (word : List Bool) (α : G2Combinatorics.G2PositiveRoot) :
    α ∈ coordinateWordInversionRoots word ↔
      (G2SignedRootReflections.simpleWordAction word (false, α)).1 = true := by
  rw [mem_coordinateWordInversionRoots_iff]
  change isNegative (coordinateWordAction word
    (signedRootCoordinate (false, α))) ↔ _
  rw [coordinateWordAction_apply_signed]
  exact isNegative_signedRootCoordinate_iff _

end InfoGeometry.Algebra.Zorn.G2CoordinateWordInversion
