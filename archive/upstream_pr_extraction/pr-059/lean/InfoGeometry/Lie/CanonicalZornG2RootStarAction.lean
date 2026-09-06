import InfoGeometry.Lie.ExceptionalAutomorphicZetaBridge

/-!
# The finite root-star action supplied by the native G₂ root owner

This file deliberately stops at the root-star level.  The existing
`G2IntegralRootLattice` is a rank witness, not yet a concrete additive lattice
carrier, so no Weyl action on that structure is asserted here.
The Mathlib root reflections do, however, act on the twelve native roots and
preserve the exhaustive root star.  This is the honest finite prerequisite for
an eventual lattice construction.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2RootStarAction

open InfoGeometry.Lie.CanonicalZornRootSystemComparison

abbrev RootIndex :=
  InfoGeometry.Lie.CanonicalZornRootSystemComparison.RootIndex

abbrev P :=
  InfoGeometry.Lie.CanonicalZornRootSystemComparison.P

noncomputable def rootStarReflection
    (α : RootIndex) (S : Finset RootIndex) : Finset RootIndex :=
  by
    classical
    exact S.image (P.reflectionPerm α)

theorem rootStarReflection_univ (α : RootIndex) :
    rootStarReflection α (Finset.univ : Finset RootIndex) = Finset.univ := by
  classical
  ext β
  constructor
  · intro h
    exact Finset.mem_univ β
  · intro h
    obtain ⟨γ, hβ⟩ :=
      (P.reflectionPerm α).surjective β
    change β ∈ (Finset.univ : Finset RootIndex).image (P.reflectionPerm α)
    exact Finset.mem_image.mpr ⟨γ, Finset.mem_univ γ, hβ⟩

noncomputable def canonicalRootStar :
    G2DoubleRootStar :=
  by
    classical
    exact G2DoubleRootStar.mk (Finset.univ : Finset RootIndex) rfl

@[simp] theorem canonicalRootStar_roots :
    canonicalRootStar.roots = (Finset.univ : Finset RootIndex) := rfl

theorem canonicalRootStar_card :
    canonicalRootStar.roots.card = 12 := by
  classical
  rw [canonicalRootStar_roots]
  exact rootIndex_card

theorem canonicalRootStar_reflection_invariant (α : RootIndex) :
    rootStarReflection α canonicalRootStar.roots = canonicalRootStar.roots := by
  classical
  rw [canonicalRootStar_roots, rootStarReflection_univ]

/-- A root reflection transported to the typed exhaustive root-star carrier. -/
noncomputable def reflectRootStar (α : RootIndex) (S : G2DoubleRootStar) :
    G2DoubleRootStar :=
  { roots := rootStarReflection α S.roots
    h_exhaustive := by
      rw [S.h_exhaustive, rootStarReflection_univ] }

@[simp] theorem reflectRootStar_roots (α : RootIndex) (S : G2DoubleRootStar) :
    (reflectRootStar α S).roots = rootStarReflection α S.roots := rfl

theorem reflectRootStar_exhaustive (α : RootIndex) (S : G2DoubleRootStar) :
    (reflectRootStar α S).roots = Finset.univ := by
  rw [reflectRootStar_roots, S.h_exhaustive, rootStarReflection_univ]

end InfoGeometry.Lie.CanonicalZornG2RootStarAction
