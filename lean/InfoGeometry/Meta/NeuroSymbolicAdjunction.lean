import Mathlib.Order.GaloisConnection.Basic
import InfoGeometry.Topology.SymbolicLatentSpace

namespace InfoGeometry.Meta.NeuroSymbolic

/-!
# An abstract order interface for symbolic decoding

This file records only the order-theoretic content of a proposed
continuous-to-discrete interface.  The carriers and the maps are parameters:
no claim is made here that they are implemented by an LLM, a neural network,
or a Python orchestration layer.

A metric or topology may be added by a client, but a Galois connection uses
only the two partial orders.
-/

variable {LatentSpace : Type*} [PartialOrder LatentSpace]
variable {SyntaxSpace : Type*} [PartialOrder SyntaxSpace]

variable (coagula : LatentSpace → SyntaxSpace)
variable (solve : SyntaxSpace → LatentSpace)

/-- The precise order-theoretic assumption on the two maps. -/
def IsJungianAdjunction : Prop :=
  GaloisConnection coagula solve

/-- A lower adjoint is monotone, provided the adjunction law holds. -/
theorem coagula_monotone
    (h_adj : IsJungianAdjunction coagula solve) : Monotone coagula := by
  intro v₁ v₂ hv
  apply (h_adj v₁ (coagula v₂)).2
  exact le_trans hv (h_adj.le_u_l v₂)

/-- An upper adjoint is monotone, provided the adjunction law holds. -/
theorem solve_monotone
    (h_adj : IsJungianAdjunction coagula solve) : Monotone solve := by
  intro T₁ T₂ hT
  apply (h_adj (solve T₁) T₂).1
  exact le_trans (h_adj.l_u_le T₁) hT

/-- The lower map followed by the upper map is deflationary on syntax. -/
theorem coagula_solve_deflation
    (h_adj : IsJungianAdjunction coagula solve) (T : SyntaxSpace) :
    coagula (solve T) ≤ T :=
  h_adj.l_u_le T

/-- The upper map followed by the lower map is inflationary on the latent carrier. -/
theorem solve_coagula_inflationary
    (h_adj : IsJungianAdjunction coagula solve) (v : LatentSpace) :
    v ≤ solve (coagula v) :=
  h_adj.le_u_l v

/-! ## The concrete adjunction already supported by the repository

`SymbolicLatentSpace` supplies a topological latent carrier and its continuous
observation map into a function space.  Its direct-image / inverse-image
adjunction is genuinely available without inventing a decoder into either
epistemic archetype poset.  Thus this result connects the existing latent
observation lane to observable constraints; it does not identify observations
with Lean syntax or assert a property of an LLM workflow.
-/

namespace SymbolicObservation

open InfoGeometry.Topology

/-- Observable values realized by a set of latent points. -/
def observationImage
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) : Set X → Set (ι → ℝ) :=
  fun points => symbolicObservationMap S '' points

/-- Latent points satisfying a set of observable constraints. -/
def observationPreimage
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) : Set (ι → ℝ) → Set X :=
  fun observations => symbolicObservationMap S ⁻¹' observations

/--
The native observation image is left adjoint to constraint preimage, with both
carriers ordered by set inclusion.
-/
theorem image_galoisConnection
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    GaloisConnection (observationImage S) (observationPreimage S) := by
  intro points observations
  change (symbolicObservationMap S '' points ⊆ observations) ↔
    points ⊆ symbolicObservationMap S ⁻¹' observations
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · intro h y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h hx

/-- Every latent point lies in the preimage of the observations it realizes. -/
theorem subset_preimage_image
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (points : Set X) :
    points ⊆ observationPreimage S (observationImage S points) :=
  (image_galoisConnection S).le_u_l points

/-- Every observation satisfying a constraint belongs to the image of its preimage. -/
theorem image_preimage_subset
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (observations : Set (ι → ℝ)) :
    observationImage S (observationPreimage S observations) ⊆ observations :=
  (image_galoisConnection S).l_u_le observations

/-- The latent-side closure of a set consists exactly of points observationally
indistinguishable from one of its members.  This identifies the Galois closure
with the equivalence classes of `symbolicObservationalSetoid`. -/
theorem observation_preimage_image_eq_saturation
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (points : Set X) :
    observationPreimage S (observationImage S points) =
      {x | ∃ y ∈ points,
        symbolicObservationMap S x = symbolicObservationMap S y} := by
  ext x
  change (∃ y, y ∈ points ∧
      symbolicObservationMap S y = symbolicObservationMap S x) ↔
    (∃ y, y ∈ points ∧
      symbolicObservationMap S x = symbolicObservationMap S y)
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, h.symm⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, h.symm⟩

/-- Observational saturation is idempotent: applying the latent-side closure
twice adds no points beyond those indistinguishable from the original set. -/
theorem observation_preimage_image_idempotent
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (points : Set X) :
    observationPreimage S
        (observationImage S (observationPreimage S (observationImage S points))) =
      observationPreimage S (observationImage S points) := by
  rw [observation_preimage_image_eq_saturation,
    observation_preimage_image_eq_saturation]
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    change (∃ z ∈ points,
      symbolicObservationMap S y = symbolicObservationMap S z) at hy
    rcases hy with ⟨z, hz, hyz⟩
    exact ⟨z, hz, hxy.trans hyz⟩
  · rintro ⟨z, hz, hxz⟩
    refine ⟨z, ?_, hxz⟩
    exact ⟨z, hz, rfl⟩

/-- A latent subset is fixed by observational saturation exactly when it is a
union of fibers of the observation map.  Equivalently, membership in the set
is invariant under the repository's observational equivalence relation. -/
theorem observation_preimage_image_eq_self_iff_saturated
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (points : Set X) :
    observationPreimage S (observationImage S points) = points ↔
      ∀ x y : X,
        @Setoid.r X (symbolicObservationalSetoid S) x y →
          (x ∈ points ↔ y ∈ points) := by
  rw [observation_preimage_image_eq_saturation]
  constructor
  · intro h x y hxy
    have hobs := (symbolicObservationalSetoid_iff S x y).1 hxy
    constructor
    · intro hx
      have hySat : y ∈ {z : X | ∃ w ∈ points,
          symbolicObservationMap S y = symbolicObservationMap S w} :=
        ⟨x, hx, hobs.symm⟩
      exact h ▸ hySat
    · intro hy
      have hxSat : x ∈ {z : X | ∃ w ∈ points,
          symbolicObservationMap S x = symbolicObservationMap S w} :=
        ⟨y, hy, hobs⟩
      exact h ▸ hxSat
  · intro hs
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (hs x y hxy).2 hy
    · intro hx
      exact ⟨x, hx, rfl⟩

/-- The observable values realized by latent points satisfying a constraint
are exactly the constraint intersected with the image of the observation map. -/
theorem observation_image_preimage_eq_inter_range
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (observations : Set (ι → ℝ)) :
    observationImage S (observationPreimage S observations) =
      observations ∩ Set.range (symbolicObservationMap S) := by
  ext y
  change (∃ x, symbolicObservationMap S x ∈ observations ∧
      symbolicObservationMap S x = y) ↔
    (y ∈ observations ∧ ∃ x, symbolicObservationMap S x = y)
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, x, rfl⟩
  · rintro ⟨hy, x, hx⟩
    exact ⟨x, hx ▸ hy, hx⟩

/-- A set of observations is fixed by image-after-preimage precisely when all
its elements are realized by some latent point. -/
theorem observation_image_preimage_eq_self_iff_realized
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (observations : Set (ι → ℝ)) :
    observationImage S (observationPreimage S observations) = observations ↔
      observations ⊆ Set.range (symbolicObservationMap S) := by
  constructor
  · intro h y hy
    have hy' : y ∈ observationImage S (observationPreimage S observations) := by
      rw [h]
      exact hy
    rw [observation_image_preimage_eq_inter_range] at hy'
    exact hy'.2
  · intro h
    ext y
    constructor
    · intro hy
      rw [observation_image_preimage_eq_inter_range] at hy
      exact hy.1
    · intro hy
      rcases h hy with ⟨x, hx⟩
      refine ⟨x, ?_, hx⟩
      change symbolicObservationMap S x ∈ observations
      rw [hx]
      exact hy

/-- The observable-side interior operation induced by image/preimage is
idempotent.  It retains precisely those constraints that are realized by some
latent point. -/
theorem observation_image_preimage_idempotent
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (observations : Set (ι → ℝ)) :
    observationImage S
        (observationPreimage S (observationImage S
          (observationPreimage S observations))) =
      observationImage S (observationPreimage S observations) := by
  rw [observation_image_preimage_eq_inter_range,
    observation_image_preimage_eq_inter_range]
  ext y
  simp

end SymbolicObservation

end InfoGeometry.Meta.NeuroSymbolic
