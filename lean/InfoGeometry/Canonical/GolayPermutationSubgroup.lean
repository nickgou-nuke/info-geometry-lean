/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.LeechGolayCoordinateAction

/-! The exact pre-classification subgroup of coordinate symmetries preserving
the extended binary Golay code.  No identification with `M24` is asserted. -/
namespace InfoGeometry.Canonical.GolayPermutationSubgroup

open InfoGeometry.Combinatorics.ExtendedBinaryGolay
open InfoGeometry.Combinatorics.LeechLattice
open InfoGeometry.Canonical.LeechGolayCoordinateAction

def PreservesGolay (σ : Equiv.Perm (Fin 24)) : Prop :=
  ∀ c : Word24, c ∈ codeSubmodule ↔ permuteCoords σ c ∈ codeSubmodule

def golayPermutationSubgroup : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {σ | PreservesGolay σ}
  one_mem' := by intro c; simp [PreservesGolay]
  mul_mem' := by
    intro σ τ hσ hτ c
    change c ∈ codeSubmodule ↔ permuteCoords (σ * τ) c ∈ codeSubmodule
    rw [permuteCoords_comp]
    exact (hτ c).trans (hσ (permuteCoords τ c))
  inv_mem' := by
    intro σ hσ c
    have h := hσ (permuteCoords σ⁻¹ c)
    have hcancel : permuteCoords σ (permuteCoords σ⁻¹ c) = c := by
      rw [← permuteCoords_comp]
      simp
    rw [hcancel] at h
    exact h.symm

def toCoordinateAutomorphism (g : golayPermutationSubgroup) :
    GolayCoordinateAutomorphism where
  perm := g.1
  code_mem_iff := g.2

theorem mapsTo_numerator (g : golayPermutationSubgroup) :
    Set.MapsTo (toCoordinateAutomorphism g).onInteger numerator numerator :=
  (toCoordinateAutomorphism g).mapsTo_numerator

/-- The subgroup action is orthogonal on the ambient real 24-space. -/
theorem dotProduct_preserved
    (g : golayPermutationSubgroup) (x y : Fin 24 → ℝ) :
    dotProduct ((toCoordinateAutomorphism g).onReal x)
        ((toCoordinateAutomorphism g).onReal y) =
      dotProduct x y :=
  (toCoordinateAutomorphism g).dotProduct_onReal x y

/-- Hence every subgroup element preserves the Euclidean squared norm. -/
theorem normSq_preserved
    (g : golayPermutationSubgroup) (x : Fin 24 → ℝ) :
    dotProduct ((toCoordinateAutomorphism g).onReal x)
        ((toCoordinateAutomorphism g).onReal x) =
      dotProduct x x :=
  dotProduct_preserved g x x

/-- The action on the actual scaled Leech realization preserves squared norm. -/
theorem scaledLeechNorm_preserved
    (g : golayPermutationSubgroup) (a : Combinatorics.GolayConstructionA.IntegerWord24) :
    (∑ i, scaledRealization ((toCoordinateAutomorphism g).onInteger a) i *
        scaledRealization ((toCoordinateAutomorphism g).onInteger a) i) =
      ∑ i, scaledRealization a i * scaledRealization a i :=
  (toCoordinateAutomorphism g).scaled_normSq_preserved a

/-- Compact subgroup/action packet. -/
theorem golay_permutation_subgroup_packet
    (g : golayPermutationSubgroup) :
    Set.MapsTo (toCoordinateAutomorphism g).onInteger numerator numerator ∧
    (∀ x y : Fin 24 → ℝ,
      dotProduct ((toCoordinateAutomorphism g).onReal x)
          ((toCoordinateAutomorphism g).onReal y) =
        dotProduct x y) := by
  exact ⟨mapsTo_numerator g, dotProduct_preserved g⟩

end InfoGeometry.Canonical.GolayPermutationSubgroup
