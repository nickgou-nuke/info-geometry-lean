import Mathlib
import InfoGeometry.Topology.SymbolicLatentAtlas

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` transition maps for symbolic-latent atlas overlaps

Atlas compatibility already supplies feature-space homeomorphisms and the
triple-overlap intertwining theorem.  This owner exposes those transitions as
categorical morphisms and records inverse and composition laws.
-/

def symbolicLatentFeatureEquivTopCatHom
    {ι : Type} [Fintype ι]
    (e : SymbolicFeatureSpace ι ≃ₜ SymbolicFeatureSpace ι) :
    TopCat.of (SymbolicFeatureSpace ι) ⟶
      TopCat.of (SymbolicFeatureSpace ι) :=
  TopCat.ofHom
    { toFun := e
      continuous_toFun := e.continuous_toFun }

theorem symbolicLatentFeatureEquivTopCatHom_apply
    {ι : Type} [Fintype ι]
    (e : SymbolicFeatureSpace ι ≃ₜ SymbolicFeatureSpace ι)
    (z : SymbolicFeatureSpace ι) :
    symbolicLatentFeatureEquivTopCatHom e z = e z :=
  rfl

def SymbolicLatentAtlasCompatibility.id
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (i : κ) :
    SymbolicLatentAtlasCompatibility A i i where
  featureEquiv := Homeomorph.refl (SymbolicFeatureSpace ι)
  intertwines_on_overlap := by
    intro x hx
    rfl

def SymbolicLatentAtlasCompatibility.trans
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : SymbolicLatentAtlas X ι κ} {i j k : κ}
    (Hij : SymbolicLatentAtlasCompatibility A i j)
    (Hjk : SymbolicLatentAtlasCompatibility A j k)
    (hmiddle : ∀ x, x ∈ A.overlap i k → x ∈ A.domain j) :
    SymbolicLatentAtlasCompatibility A i k where
  featureEquiv := Hij.featureEquiv.trans Hjk.featureEquiv
  intertwines_on_overlap :=
    SymbolicLatentAtlasCompatibility.trans_on_triple_overlap Hij Hjk hmiddle

def SymbolicLatentAtlasCompatibility.featureTransitionTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : SymbolicLatentAtlas X ι κ} {i j : κ}
    (H : SymbolicLatentAtlasCompatibility A i j) :
    TopCat.of (SymbolicFeatureSpace ι) ⟶
      TopCat.of (SymbolicFeatureSpace ι) :=
  symbolicLatentFeatureEquivTopCatHom H.featureEquiv

theorem SymbolicLatentAtlasCompatibility.featureTransitionTopCatHom_symm
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : SymbolicLatentAtlas X ι κ} {i j : κ}
    (H : SymbolicLatentAtlasCompatibility A i j) :
    H.featureTransitionTopCatHom ≫
        H.symm.featureTransitionTopCatHom =
      𝟙 (TopCat.of (SymbolicFeatureSpace ι)) := by
  ext z x
  change (H.symm.featureEquiv (H.featureEquiv z)) x = z x
  exact congrFun (H.featureEquiv.symm_apply_apply z) x

theorem SymbolicLatentAtlasCompatibility.id_featureTransitionTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : SymbolicLatentAtlas X ι κ} (i : κ) :
    (SymbolicLatentAtlasCompatibility.id A i).featureTransitionTopCatHom =
      𝟙 (TopCat.of (SymbolicFeatureSpace ι)) := by
  ext z
  rfl

theorem SymbolicLatentAtlasCompatibility.trans_featureTransitionTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : SymbolicLatentAtlas X ι κ} {i j k : κ}
    (Hij : SymbolicLatentAtlasCompatibility A i j)
    (Hjk : SymbolicLatentAtlasCompatibility A j k)
    (hmiddle : ∀ x, x ∈ A.overlap i k → x ∈ A.domain j) :
    (Hij.trans Hjk hmiddle).featureTransitionTopCatHom =
      Hij.featureTransitionTopCatHom ≫ Hjk.featureTransitionTopCatHom := by
  ext z
  rfl

theorem SymbolicLatentAtlasCompatibility.featureTransitionTopCatHom_comp
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : SymbolicLatentAtlas X ι κ} {i j k : κ}
    (Hij : SymbolicLatentAtlasCompatibility A i j)
    (Hjk : SymbolicLatentAtlasCompatibility A j k) :
    Hij.featureTransitionTopCatHom ≫ Hjk.featureTransitionTopCatHom =
      symbolicLatentFeatureEquivTopCatHom
        (Hij.featureEquiv.trans Hjk.featureEquiv) := by
  ext z
  rfl

theorem SymbolicLatentAtlasCompatibility.featureTransitionTopCatHom_isIso
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : SymbolicLatentAtlas X ι κ} {i j : κ}
    (H : SymbolicLatentAtlasCompatibility A i j) :
    IsIso H.featureTransitionTopCatHom := by
  refine IsIso.mk ⟨H.symm.featureTransitionTopCatHom, ?_, ?_⟩
  · exact H.featureTransitionTopCatHom_symm
  · simpa using H.symm.featureTransitionTopCatHom_symm

theorem SymbolicLatentAtlasCompatibility.featureTransitionTopCatHom_intertwines
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : SymbolicLatentAtlas X ι κ} {i j : κ}
    (H : SymbolicLatentAtlasCompatibility A i j)
    {x : X} (hx : x ∈ A.overlap i j) :
    H.featureTransitionTopCatHom
        (symbolicObservationMap (A.chart i).system x) =
      symbolicObservationMap (A.chart j).system x :=
  H.intertwines_on_overlap x hx

end InfoGeometry.Topology
