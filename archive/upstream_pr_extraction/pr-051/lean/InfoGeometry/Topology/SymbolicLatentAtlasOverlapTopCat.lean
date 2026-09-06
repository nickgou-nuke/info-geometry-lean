import Mathlib
import InfoGeometry.Topology.SymbolicLatentAtlasTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` overlap squares for symbolic-latent atlases

The atlas owner proves chart compatibility pointwise on overlaps.  This file
packages that statement as a commutative square in `TopCat`, keeping the
overlap as a subtype and introducing no new atlas or geometric assumptions.
-/

abbrev SymbolicLatentAtlasOverlap
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (i j : κ) :=
  {x : X // x ∈ A.overlap i j}

def SymbolicLatentAtlas.overlapObservationTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (k i j : κ) :
    TopCat.of (SymbolicLatentAtlasOverlap A i j) ⟶
      TopCat.of (ι → ℝ) :=
  TopCat.ofHom
    { toFun := fun x => symbolicObservationMap (A.chart k).system x.1
      continuous_toFun :=
        (continuous_symbolicObservationMap (A.chart k).system).comp
          continuous_subtype_val }

@[simp] theorem SymbolicLatentAtlas.overlapObservationTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (k i j : κ)
    (x : SymbolicLatentAtlasOverlap A i j) :
    A.overlapObservationTopCatHom k i j x =
      symbolicObservationMap (A.chart k).system x.1 :=
  rfl

theorem SymbolicLatentAtlas.overlapObservation_transition_commutes
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) {i j : κ}
    (H : SymbolicLatentAtlasCompatibility A i j) :
    A.overlapObservationTopCatHom i i j ≫
        H.featureTransitionTopCatHom =
      A.overlapObservationTopCatHom j i j := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact H.featureTransitionTopCatHom_intertwines (x := x.1) x.property

theorem SymbolicLatentAtlas.overlapObservation_transition_symm_commutes
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) {i j : κ}
    (H : SymbolicLatentAtlasCompatibility A i j) :
    A.overlapObservationTopCatHom j i j ≫
        H.symm.featureTransitionTopCatHom =
      A.overlapObservationTopCatHom i i j := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply H.symm.featureTransitionTopCatHom_intertwines
  change x.1 ∈ A.domain j ∩ A.domain i
  exact ⟨x.property.2, x.property.1⟩

theorem SymbolicLatentAtlas.overlapObservation_transition_comp_commutes
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) {i j k : κ}
    (Hij : SymbolicLatentAtlasCompatibility A i j)
    (Hjk : SymbolicLatentAtlasCompatibility A j k)
    (hmiddle : ∀ x, x ∈ A.overlap i k → x ∈ A.domain j) :
    A.overlapObservationTopCatHom i i k ≫
        Hij.featureTransitionTopCatHom ≫
          Hjk.featureTransitionTopCatHom =
      A.overlapObservationTopCatHom k i k := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  have hxik := x.property
  have hxij : x.1 ∈ A.overlap i j := ⟨hxik.1, hmiddle x.1 hxik⟩
  have hxjk : x.1 ∈ A.overlap j k := ⟨hmiddle x.1 hxik, hxik.2⟩
  calc
    Hjk.featureEquiv (Hij.featureEquiv
        (symbolicObservationMap (A.chart i).system x.1)) =
      Hjk.featureEquiv
        (symbolicObservationMap (A.chart j).system x.1) := by
          rw [Hij.intertwines_on_overlap x.1 hxij]
    _ = symbolicObservationMap (A.chart k).system x.1 :=
      Hjk.intertwines_on_overlap x.1 hxjk

theorem SymbolicLatentAtlas.overlapObservation_transitive_compatibility
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) {i j k : κ}
    (Hij : SymbolicLatentAtlasCompatibility A i j)
    (Hjk : SymbolicLatentAtlasCompatibility A j k)
    (hmiddle : ∀ x, x ∈ A.overlap i k → x ∈ A.domain j) :
    A.overlapObservationTopCatHom i i k ≫
        (Hij.trans Hjk hmiddle).featureTransitionTopCatHom =
      A.overlapObservationTopCatHom k i k := by
  rw [SymbolicLatentAtlasCompatibility.trans_featureTransitionTopCatHom]
  exact A.overlapObservation_transition_comp_commutes Hij Hjk hmiddle

end InfoGeometry.Topology
