import InfoGeometry.Algebra.Zorn.G2ReducedWords
import InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers

/-!
# G₂ Bruhat inversion roots

This owner packages the already verified `G₂` Weyl inversion-set machinery as
a Bruhat-facing interface.  It proves the root-side statements needed for
Bruhat cell cardinalities:

* inversion roots are exactly the positive roots sent to negative roots by the
  chosen reduced word;
* the inversion-set cardinality is the Coxeter length;
* the associated Boolean residual exponent has cardinality `2 ^ length`;
* the longest element has all six positive roots as inversions;
* the existing normal-form residual coordinates are equivalent to the
  canonical Weyl residual coordinates.

This file intentionally does **not** identify the Boolean residual exponent
with a concrete ordered product of root subgroups, nor with the subgroup
intersection `B ∩ w B w⁻¹`.  The repository's residual-fiber owner explicitly
keeps that identification separate until ordered root products and injectivity
have been proved.
-/

namespace InfoGeometry.GroupTheory.G2BruhatInversions

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2CoordinateWordInversion
open InfoGeometry.Algebra.Zorn.G2SignedRootReflections
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers

/-- The Bruhat inversion set of an element of the existing 12-element
`WeylG2` normal-form carrier. -/
noncomputable def bruhatInversionRoots (w : WeylG2) : Finset G2PositiveRoot :=
  dihedralInversionRoots w

/-- A positive root lies in the Bruhat inversion set exactly when the signed
root action of the canonical reduced word sends it to the negative sheet. -/
theorem mem_bruhatInversionRoots_iff_signed
    (w : WeylG2) (α : G2PositiveRoot) :
    α ∈ bruhatInversionRoots w ↔
      (simpleWordAction (toReducedWord w) (false, α)).1 = true := by
  exact mem_coordinateWordInversionRoots_iff_signed (toReducedWord w) α

/-- The number of Bruhat inversion roots is the Coxeter length. -/
theorem bruhatInversionRoots_card_eq_length (w : WeylG2) :
    (bruhatInversionRoots w).card = dihedralLength w := by
  exact dihedralInversion_card_eq_length w

/-- Bruhat residual Boolean coordinates, one bit for each inversion root. -/
abbrev BruhatResidualExponent (w : WeylG2) :=
  { α : G2PositiveRoot // α ∈ bruhatInversionRoots w } → Bool

/-- The residual Boolean coordinate fiber has cardinality `2 ^ ℓ(w)`. -/
theorem bruhatResidualExponent_card (w : WeylG2) :
    Fintype.card (BruhatResidualExponent w) = 2 ^ dihedralLength w := by
  classical
  simp [BruhatResidualExponent, bruhatInversionRoots_card_eq_length]

/-- The Bruhat-facing inversion set is the canonical signed inversion set after
transport through the existing finite-carrier bridge. -/
theorem bruhatInversionRoots_eq_canonicalSigned (w : WeylG2) :
    bruhatInversionRoots w =
      canonicalSignedInversionRoots (weylElementOfNF w) := by
  exact dihedralInversionRoots_eq_canonicalSigned w

/-- The Bruhat residual coordinates are equivalent to the canonical residual
coordinates on `G2WeylElement`. -/
noncomputable def bruhatResidualCanonicalEquiv (w : WeylG2) :
    BruhatResidualExponent w ≃
      CanonicalResidualExponent (weylElementOfNF w) := by
  exact residualCoordsCanonicalEquiv w

/-- The normal-form element `(3,false)` is the longest Weyl element and every
positive root is an inversion root. -/
theorem bruhatInversionRoots_longest :
    bruhatInversionRoots ((3 : ZMod 6), false) = Finset.univ := by
  rw [bruhatInversionRoots_eq_canonicalSigned]
  change canonicalSignedInversionRoots G2WeylElement.w0 = Finset.univ
  exact canonicalSignedInversionRoots_w0

/-- The longest element has Coxeter length six. -/
theorem bruhatLongest_length :
    dihedralLength ((3 : ZMod 6), false) = 6 := by
  decide

/-- Consequently the longest Bruhat residual fiber has cardinality `2^6 = 64`. -/
theorem bruhatResidualExponent_longest_card :
    Fintype.card (BruhatResidualExponent ((3 : ZMod 6), false)) = 64 := by
  rw [bruhatResidualExponent_card, bruhatLongest_length]
  norm_num

/-- The identity has no inversion roots. -/
theorem bruhatInversionRoots_identity :
    bruhatInversionRoots ((0 : ZMod 6), false) = ∅ := by
  rw [bruhatInversionRoots_eq_canonicalSigned]
  change canonicalSignedInversionRoots G2WeylElement.id = ∅
  exact canonicalSignedInversionRoots_id

/-- Consequently the identity Bruhat residual fiber has cardinality one. -/
theorem bruhatResidualExponent_identity_card :
    Fintype.card (BruhatResidualExponent ((0 : ZMod 6), false)) = 1 := by
  rw [bruhatResidualExponent_card]
  decide

end InfoGeometry.GroupTheory.G2BruhatInversions
