import InfoGeometry.Algebra.Zorn.G2ReducedWords

/-!
# Bruhat inversion data for the concrete `WeylG2` carrier

This owner only transports the existing signed-root inversion results to the
normal-form carrier.  It deliberately does not identify Boolean coordinates
with a concrete residual subgroup.
-/

namespace InfoGeometry.GroupTheory.G2BruhatInversions

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
open InfoGeometry.Algebra.Zorn.G2ReducedWords

def bruhatInversionRoots
    (w : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    Finset G2PositiveRoot :=
  canonicalSignedInversionRoots (weylElementOfNF w)

theorem bruhatInversionRoots_card
    (w : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    (bruhatInversionRoots w).card = dihedralLength w := by
  rw [bruhatInversionRoots, canonicalSignedInversionRoots_card,
    weylElementOfNF_length]

abbrev BruhatResidualExponent
    (w : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :=
  { α : G2PositiveRoot // α ∈ bruhatInversionRoots w } → Bool

theorem bruhatResidualExponent_card
    (w : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    Fintype.card (BruhatResidualExponent w) = 2 ^ dihedralLength w := by
  simp [BruhatResidualExponent, bruhatInversionRoots_card w]

theorem bruhatInversionRoots_eq_canonicalSigned
    (w : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    bruhatInversionRoots w =
      canonicalSignedInversionRoots (weylElementOfNF w) := rfl

theorem bruhatInversionRoots_longest :
    bruhatInversionRoots (3, false) =
      canonicalSignedInversionRoots G2WeylElement.w0 := by
  rfl

theorem bruhatLongest_length :
    dihedralLength (3, false) = 6 := by
  decide

theorem bruhatResidualExponent_longest_card :
    Fintype.card (BruhatResidualExponent (3, false)) = 64 := by
  rw [bruhatResidualExponent_card]
  decide

theorem bruhatInversionRoots_identity :
    bruhatInversionRoots (0, false) = ∅ := by
  rw [bruhatInversionRoots_eq_canonicalSigned]
  rfl

theorem bruhatResidualExponent_identity_card :
    Fintype.card (BruhatResidualExponent (0, false)) = 1 := by
  rw [bruhatResidualExponent_card]
  decide

end InfoGeometry.GroupTheory.G2BruhatInversions
