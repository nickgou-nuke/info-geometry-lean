import Mathlib
import InfoGeometry.Combinatorics.LeechLattice

/-!
# Coordinate actions on the native Leech numerator carrier

This file supplies the theorem-safe permutation-action substrate needed before
one can identify the monomial subgroup `2^12 : M24` or the full Conway group
`Co₀`.

The repository already constructs the extended binary Golay code and the
24-coordinate Leech numerator set.  Here a coordinate permutation is bundled
with the exact hypothesis that it preserves the Golay code.  From that premise
we derive preservation of both Leech numerator branches and of the Euclidean
bilinear/quadratic forms.

No identification with `M24`, `Co₀`, an ATLAS matrix representation, or the
196560-vector minimal shell is made in this owner.
-/

namespace InfoGeometry.Canonical.LeechGolayCoordinateAction

open Matrix
open InfoGeometry.Combinatorics.ExtendedBinaryGolay
open InfoGeometry.Combinatorics.GolayConstructionA
open InfoGeometry.Combinatorics.LeechLattice

/-- Pull coordinates along a permutation.  The inverse is used so composition
agrees with the usual left action convention. -/
def permuteCoords {α : Type*}
    (σ : Equiv.Perm (Fin 24)) (x : Fin 24 → α) : Fin 24 → α :=
  fun i => x (σ.symm i)

@[simp]
theorem permuteCoords_id {α : Type*} (x : Fin 24 → α) :
    permuteCoords (1 : Equiv.Perm (Fin 24)) x = x := by
  rfl

@[simp]
theorem permuteCoords_comp {α : Type*}
    (σ τ : Equiv.Perm (Fin 24)) (x : Fin 24 → α) :
    permuteCoords (σ * τ) x = permuteCoords σ (permuteCoords τ x) := by
  funext i
  rfl

/-- Coordinate permutation preserves the integral coordinate sum. -/
theorem coordinateSum_permute
    (σ : Equiv.Perm (Fin 24)) (z : IntegerWord24) :
    coordinateSum (permuteCoords σ z) = coordinateSum z := by
  unfold coordinateSum permuteCoords
  exact Fintype.sum_equiv σ.symm _ _ (fun _ => rfl)

/-- Coordinate permutation commutes with the binary `{0,1}` lift. -/
theorem wordLift_permute
    (σ : Equiv.Perm (Fin 24)) (c : Word24) :
    wordLift (permuteCoords σ c) = permuteCoords σ (wordLift c) := by
  rfl

/-- Coordinate permutation commutes with the even Leech numerator formula. -/
theorem evenNumerator_permute
    (σ : Equiv.Perm (Fin 24)) (c : Word24) (z : IntegerWord24) :
    permuteCoords σ (evenNumerator c z) =
      evenNumerator (permuteCoords σ c) (permuteCoords σ z) := by
  funext i
  rfl

/-- Coordinate permutation commutes with the odd Leech numerator formula. -/
theorem oddNumerator_permute
    (σ : Equiv.Perm (Fin 24)) (c : Word24) (z : IntegerWord24) :
    permuteCoords σ (oddNumerator c z) =
      oddNumerator (permuteCoords σ c) (permuteCoords σ z) := by
  funext i
  rfl

/-- A coordinate permutation equipped with an exact proof that it preserves the
native extended binary Golay code.  This is the correct pre-`M24` carrier: the
classification of all such permutations as `M24` is a separate theorem. -/
structure GolayCoordinateAutomorphism where
  perm : Equiv.Perm (Fin 24)
  code_mem_iff :
    ∀ c : Word24,
      c ∈ codeSubmodule ↔ permuteCoords perm c ∈ codeSubmodule

namespace GolayCoordinateAutomorphism

/-- The underlying coordinate action on binary words. -/
def onBinary (g : GolayCoordinateAutomorphism) (c : Word24) : Word24 :=
  permuteCoords g.perm c

/-- The underlying coordinate action on integral Leech numerator words. -/
def onInteger (g : GolayCoordinateAutomorphism) (z : IntegerWord24) : IntegerWord24 :=
  permuteCoords g.perm z

/-- The corresponding action on the ambient real 24-space. -/
def onReal (g : GolayCoordinateAutomorphism) (x : Fin 24 → ℝ) : Fin 24 → ℝ :=
  permuteCoords g.perm x

/-- A Golay-preserving coordinate permutation maps the actual Leech numerator
carrier to itself. -/
theorem mapsTo_numerator (g : GolayCoordinateAutomorphism) :
    Set.MapsTo g.onInteger numerator numerator := by
  intro a ha
  change a ∈ evenBranch ∪ oddBranch at ha
  change g.onInteger a ∈ evenBranch ∪ oddBranch
  rcases ha with ha | ha
  · left
    rcases ha with ⟨c, hc, z, hz, rfl⟩
    refine ⟨g.onBinary c, (g.code_mem_iff c).1 hc, g.onInteger z, ?_, ?_⟩
    · rw [onInteger, coordinateSum_permute]
      exact hz
    · exact evenNumerator_permute g.perm c z
  · right
    rcases ha with ⟨c, hc, z, hz, rfl⟩
    refine ⟨g.onBinary c, (g.code_mem_iff c).1 hc, g.onInteger z, ?_, ?_⟩
    · rw [onInteger, coordinateSum_permute]
      exact hz
    · exact oddNumerator_permute g.perm c z

/-- The integral quadratic numerator is invariant under every coordinate
permutation, independently of the Golay-preservation premise. -/
theorem normSqNumerator_onInteger
    (g : GolayCoordinateAutomorphism) (a : IntegerWord24) :
    InfoGeometry.Combinatorics.LeechLattice.normSqNumerator (g.onInteger a) =
      InfoGeometry.Combinatorics.LeechLattice.normSqNumerator a := by
  unfold InfoGeometry.Combinatorics.LeechLattice.normSqNumerator onInteger permuteCoords
  exact Fintype.sum_equiv g.perm.symm _ _ (fun _ => rfl)

/-- The ambient real coordinate action preserves the full Euclidean bilinear
form.  This is the exact orthogonality statement for the permutation part of
the eventual monomial/Conway action. -/
theorem dotProduct_onReal
    (g : GolayCoordinateAutomorphism) (x y : Fin 24 → ℝ) :
    dotProduct (g.onReal x) (g.onReal y) = dotProduct x y := by
  unfold dotProduct onReal permuteCoords
  exact Fintype.sum_equiv g.perm.symm _ _ (fun _ => rfl)

/-- In particular, the real coordinate action preserves squared Euclidean norm. -/
theorem normSq_onReal
    (g : GolayCoordinateAutomorphism) (x : Fin 24 → ℝ) :
    dotProduct (g.onReal x) (g.onReal x) = dotProduct x x :=
  g.dotProduct_onReal x x

/-- Coordinate action commutes with the conventional real `1/sqrt 8`
realization. -/
theorem scaledRealization_onInteger
    (g : GolayCoordinateAutomorphism) (a : IntegerWord24) (i : Fin 24) :
    scaledRealization (g.onInteger a) i =
      scaledRealization a (g.perm.symm i) := by
  rfl

/-- Hence the Euclidean squared norm of the scaled Leech realization is
preserved exactly. -/
theorem scaled_normSq_preserved
    (g : GolayCoordinateAutomorphism) (a : IntegerWord24) :
    (∑ i, scaledRealization (g.onInteger a) i *
        scaledRealization (g.onInteger a) i) =
      ∑ i, scaledRealization a i * scaledRealization a i := by
  rw [scaledRealization_normSq, scaledRealization_normSq,
    g.normSqNumerator_onInteger]

/-- The identity coordinate permutation is a Golay-coordinate automorphism. -/
def identity : GolayCoordinateAutomorphism where
  perm := 1
  code_mem_iff := by
    intro c
    rfl

@[simp]
theorem identity_onInteger (a : IntegerWord24) :
    identity.onInteger a = a := by
  rfl

end GolayCoordinateAutomorphism

/-- Compact theorem packet: every Golay-coordinate automorphism acts on the
native Leech numerator and preserves its scaled Euclidean quadratic norm. -/
theorem golay_coordinate_action_packet
    (g : GolayCoordinateAutomorphism) :
    Set.MapsTo g.onInteger numerator numerator ∧
    (∀ x y : Fin 24 → ℝ,
      dotProduct (g.onReal x) (g.onReal y) = dotProduct x y) ∧
    ∀ a : IntegerWord24,
      (∑ i, scaledRealization (g.onInteger a) i *
          scaledRealization (g.onInteger a) i) =
        ∑ i, scaledRealization a i * scaledRealization a i := by
  exact ⟨g.mapsTo_numerator, g.dotProduct_onReal, g.scaled_normSq_preserved⟩

end InfoGeometry.Canonical.LeechGolayCoordinateAction
