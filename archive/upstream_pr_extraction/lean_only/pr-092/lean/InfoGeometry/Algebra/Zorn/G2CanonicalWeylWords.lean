/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2SignedRootReflections
import InfoGeometry.Algebra.Zorn.G2ChevalleyPoincareCombinatorics
import InfoGeometry.Algebra.Zorn.G2CoordinateWordActionBridge
import InfoGeometry.Algebra.Zorn.G2CoordinateWordInversion

/-!
# Canonical reduced words for the finite `G₂` Weyl carrier

The existing `G2WeylElement` is the combinatorial twelve-element carrier.
This file gives each constructor its canonical alternating simple-reflection
word, without introducing a second Weyl group or a new multiplication law.
`true` denotes the first simple reflection and `false` the second.
-/

namespace InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2SignedRootReflections
open InfoGeometry.Algebra.Zorn.G2CoordinateWordActionBridge
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2CoordinateWordInversion

def canonicalWeylWord : G2WeylElement → List Bool
  | .id => []
  | .s1 => [true]
  | .s2 => [false]
  | .s1s2 => [true, false]
  | .s2s1 => [false, true]
  | .s1s2s1 => [true, false, true]
  | .s2s1s2 => [false, true, false]
  | .s1s2s1s2 => [true, false, true, false]
  | .s2s1s2s1 => [false, true, false, true]
  | .s1s2s1s2s1 => [true, false, true, false, true]
  | .s2s1s2s1s2 => [false, true, false, true, false]
  | .w0 => [true, false, true, false, true, false]

theorem canonicalWeylWord_length (w : G2WeylElement) :
    (canonicalWeylWord w).length = weylLength w := by
  cases w <;> rfl

def canonicalWeylAction (w : G2WeylElement) :
    SignedPositiveRoot → SignedPositiveRoot :=
  simpleWordAction (canonicalWeylWord w)

theorem canonicalWeylAction_apply (w : G2WeylElement)
    (r : SignedPositiveRoot) :
    canonicalWeylAction w r =
      simpleWordAction (canonicalWeylWord w) r := rfl

theorem canonicalCoordinateAction_apply_signed (w : G2WeylElement)
    (r : SignedPositiveRoot) :
    coordinateWordAction (canonicalWeylWord w) (signedRootCoordinate r) =
      signedRootCoordinate (canonicalWeylAction w r) := by
  exact coordinateWordAction_apply_signed (canonicalWeylWord w) r

noncomputable def canonicalInversionRoots (w : G2WeylElement) :
    Finset G2PositiveRoot :=
  coordinateWordInversionRoots (canonicalWeylWord w)

def canonicalSignedInversionRoots (w : G2WeylElement) :
    Finset G2Combinatorics.G2PositiveRoot :=
  G2SignedRootReflections.wordInversionRoots (canonicalWeylWord w)

theorem canonicalSignedInversionRoots_card (w : G2WeylElement) :
    (canonicalSignedInversionRoots w).card = weylLength w := by
  cases w <;> decide

end InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
