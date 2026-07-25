import Mathlib.Tactic

/-!
# Projective Cross Ratio

This file establishes the foundational projective gauge structures required
for the affine/projective lifting of the Delaunay flip representation.
-/

namespace InfoGeometry.Projective

/-- A field-valued label packet with guaranteed separation. -/
structure ProjectiveLabels (K ι : Type*) [Field K] where
  ζ : ι → K
  sep : ∀ {p q : ι}, p ≠ q → ζ p - ζ q ≠ 0

/-- Standard projective cross-ratio convention. -/
def crossRatio {K : Type*} [Field K] (a b c d : K) : K :=
  ((a - b) * (c - d)) / ((a - c) * (b - d))

end InfoGeometry.Projective
