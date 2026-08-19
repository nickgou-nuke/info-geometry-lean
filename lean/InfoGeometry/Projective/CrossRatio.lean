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

theorem ProjectiveLabels.label_ne
    {K ι : Type*} [Field K] (L : ProjectiveLabels K ι)
    {p q : ι} (hpq : p ≠ q) :
    L.ζ p ≠ L.ζ q := by
  exact sub_ne_zero.mp (L.sep hpq)

theorem ProjectiveLabels.injective
    {K ι : Type*} [Field K] (L : ProjectiveLabels K ι) :
    Function.Injective L.ζ := by
  intro p q hpq
  by_contra hne
  exact (L.sep hne) (sub_eq_zero.mpr hpq)

/-- Standard projective cross-ratio convention. -/
def crossRatio {K : Type*} [Field K] (a b c d : K) : K :=
  ((a - b) * (c - d)) / ((a - c) * (b - d))

theorem crossRatio_eq_zero_iff
    {K : Type*} [Field K] {a b c d : K}
    (hden : (a - c) * (b - d) ≠ 0) :
    crossRatio a b c d = 0 ↔
      (a - b) * (c - d) = 0 := by
  simp [crossRatio, hden]

theorem crossRatio_eq_one_iff
    {K : Type*} [Field K] {a b c d : K}
    (hden : (a - c) * (b - d) ≠ 0) :
    crossRatio a b c d = 1 ↔
      (a - b) * (c - d) = (a - c) * (b - d) := by
  unfold crossRatio
  rw [div_eq_iff hden]
  simp

theorem crossRatio_ne_zero_of_separated
    {K : Type*} [Field K] {a b c d : K}
    (hab : a - b ≠ 0) (hcd : c - d ≠ 0)
    (hac : a - c ≠ 0) (hbd : b - d ≠ 0) :
    crossRatio a b c d ≠ 0 := by
  simp [crossRatio, mul_ne_zero hac hbd, mul_ne_zero hab hcd]

end InfoGeometry.Projective
