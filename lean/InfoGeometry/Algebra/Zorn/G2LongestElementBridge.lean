/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2ReducedWords

/-!
# Canonical longest element for the existing finite `G₂` Weyl carrier

The carrier is the repository-owned `WeylG2 = ZMod 6 × Bool`.  This file
names its order-six alternating representative and records the existing
normal-form projection to `G2WeylElement.w0`.  It does not introduce an Artin
group presentation or identify the Weyl involution with a physical symmetry.
-/

namespace InfoGeometry.Algebra.Zorn.G2LongestElementBridge

open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

def g2LongestNF :
    InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2 :=
  ((3 : ZMod 6), false)

private theorem g2LongestNF_val : (3 : ZMod 6).val = 3 := by
  exact ZMod.val_ofNat_of_lt (by decide)

theorem g2LongestNF_length :
    dihedralLength g2LongestNF = 6 := by
  simp [g2LongestNF, dihedralLength, toReducedWord, reducedRotationWord,
    g2LongestNF_val]

theorem g2LongestNF_word_canonical :
    toReducedWord g2LongestNF = canonicalWeylWord G2WeylElement.w0 := by
  simp [g2LongestNF, toReducedWord, reducedRotationWord, canonicalWeylWord,
    weylElementOfNF, g2LongestNF_val]

theorem g2LongestNF_weyl_length :
    weylLength (weylElementOfNF g2LongestNF) = 6 := by
  rw [weylElementOfNF_length]
  exact g2LongestNF_length

end InfoGeometry.Algebra.Zorn.G2LongestElementBridge
