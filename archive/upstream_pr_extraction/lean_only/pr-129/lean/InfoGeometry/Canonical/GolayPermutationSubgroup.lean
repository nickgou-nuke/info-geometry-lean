import Mathlib
import InfoGeometry.Canonical.LeechGolayCoordinateAction

/-!
# Golay-preserving coordinate permutations as an actual subgroup

The previous owner proves that every coordinate permutation preserving the
extended binary Golay code preserves the native Leech numerator carrier and the
ambient Euclidean form.  This file packages exactly those permutations as a
subgroup of `Equiv.Perm (Fin 24)`.

This is the canonical pre-`M24` object.  No classification theorem identifying
this subgroup with the Mathieu group `M24` is asserted here, and no extension
to the full Conway group `Co₀` is assumed.
-/

namespace InfoGeometry.Canonical.GolayPermutationSubgroup

open InfoGeometry.Combinatorics.ExtendedBinaryGolay
open InfoGeometry.Combinatorics.LeechLattice
open InfoGeometry.Canonical.LeechGolayCoordinateAction

/-- Predicate that a coordinate permutation preserves the native extended
binary Golay code exactly. -/
def PreservesGolay (σ : Equiv.Perm (Fin 24)) : Prop :=
  ∀ c : Word24,
    c ∈ codeSubmodule ↔ permuteCoords σ c ∈ codeSubmodule

/-- The coordinate permutations preserving the extended binary Golay code form
a subgroup of the full symmetric group on 24 coordinates. -/
def golayPermutationSubgroup : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {σ | PreservesGolay σ}
  one_mem' := by
    intro c
    simp [PreservesGolay]
  mul_mem' := by
    intro σ τ hσ hτ c
    change c ∈ codeSubmodule ↔ permuteCoords (σ * τ) c ∈ codeSubmodule
    rw [permuteCoords_comp]
    exact (hτ c).trans (hσ (permuteCoords τ c))
  inv_mem' := by
    intro σ hσ c
    have h := hσ (permuteCoords σ⁻¹ c)
    have hcancel :
        permuteCoords σ (permuteCoords σ⁻¹ c) = c := by
      rw [← permuteCoords_comp]
      simp
    rw [hcancel] at h
    exact h.symm

/-- Every subgroup element yields the previously defined bundled coordinate
automorphism. -/
def toCoordinateAutomorphism
    (g : golayPermutationSubgroup) :
    InfoGeometry.Canonical.LeechGolayCoordinateAction.GolayCoordinateAutomorphism where
  perm := g.1
  code_mem_iff := g.2

/-- The subgroup action preserves the native Leech numerator carrier. -/
theorem mapsTo_numerator
    (g : golayPermutationSubgroup) :
    Set.MapsTo (toCoordinateAutomorphism g).onInteger numerator numerator :=
  (toCoordinateAutomorphism g).mapsTo_numerator

/-- The subgroup action is orthogonal on the ambient real 24-space. -/
theorem dotProduct_preserved
    (g : golayPermutationSubgroup) (x y : Fin 24 → ℝ) :
    Matrix.dotProduct ((toCoordinateAutomorphism g).onReal x)
        ((toCoordinateAutomorphism g).onReal y) =
      Matrix.dotProduct x y :=
  (toCoordinateAutomorphism g).dotProduct_onReal x y

/-- Hence every subgroup element preserves the Euclidean squared norm. -/
theorem normSq_preserved
    (g : golayPermutationSubgroup) (x : Fin 24 → ℝ) :
    Matrix.dotProduct ((toCoordinateAutomorphism g).onReal x)
        ((toCoordinateAutomorphism g).onReal x) =
      Matrix.dotProduct x x :=
  dotProduct_preserved g x x

/-- The action on the actual scaled Leech realization preserves squared norm. -/
theorem scaledLeechNorm_preserved
    (g : golayPermutationSubgroup) (a : IntegerWord24) :
    (∑ i, scaledRealization ((toCoordinateAutomorphism g).onInteger a) i *
        scaledRealization ((toCoordinateAutomorphism g).onInteger a) i) =
      ∑ i, scaledRealization a i * scaledRealization a i :=
  (toCoordinateAutomorphism g).scaled_normSq_preserved a

/-- Compact subgroup/action packet. -/
theorem golay_permutation_subgroup_packet
    (g : golayPermutationSubgroup) :
    Set.MapsTo (toCoordinateAutomorphism g).onInteger numerator numerator ∧
    (∀ x y : Fin 24 → ℝ,
      Matrix.dotProduct ((toCoordinateAutomorphism g).onReal x)
          ((toCoordinateAutomorphism g).onReal y) =
        Matrix.dotProduct x y) := by
  exact ⟨mapsTo_numerator g, dotProduct_preserved g⟩

end InfoGeometry.Canonical.GolayPermutationSubgroup
