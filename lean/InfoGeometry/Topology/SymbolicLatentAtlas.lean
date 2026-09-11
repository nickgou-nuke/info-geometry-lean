import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentChartEquivalence

/-!
# Finite symbolic latent atlases

An atlas here is deliberately minimal: it is a finite open cover together
with a symbolic chart on each member.  Compatibility maps are supplied by
`SymbolicLatentChartEquivalence` when needed; this file only records the
topological cover data.
-/

namespace InfoGeometry.Topology

structure SymbolicLatentAtlas
    (X : Type*) [TopologicalSpace X]
    (ι κ : Type*) [Fintype ι] [Fintype κ] where
  chart : κ → SymbolicLatentChart X ι
  domain : κ → Set X
  isOpen_domain : ∀ k, IsOpen (domain k)
  cover : (⋃ k, domain k) = Set.univ

theorem SymbolicLatentAtlas.mem_some_domain
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (x : X) :
    ∃ k, x ∈ A.domain k := by
  have hx : x ∈ (⋃ k, A.domain k) := by
    rw [A.cover]
    trivial
  exact Set.mem_iUnion.mp hx

def SymbolicLatentAtlas.relativeFeatureRegion
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι)) : Set X :=
  A.domain k ∩ latentFeatureRegion (A.chart k) R

theorem SymbolicLatentAtlas.relativeFeatureRegion_subset_domain
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι)) :
    A.relativeFeatureRegion k R ⊆ A.domain k := by
  intro x hx
  exact hx.1

theorem SymbolicLatentAtlas.isOpen_domain_inter_latentFeatureRegion
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι)) :
    IsOpen (A.domain k ∩ latentFeatureRegion (A.chart k) R) ↔
      IsOpen (A.relativeFeatureRegion k R) :=
  Iff.rfl

theorem SymbolicLatentAtlas.isOpen_relativeFeatureRegion
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    (hR : IsOpen R) :
    IsOpen (A.relativeFeatureRegion k R) := by
  exact (A.isOpen_domain k).inter
    (hR.preimage (continuous_symbolicObservationMap (A.chart k).system))

theorem SymbolicLatentAtlas.relativeFeatureRegion_univ
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (k : κ) :
    A.relativeFeatureRegion k Set.univ = A.domain k := by
  ext x
  simp [SymbolicLatentAtlas.relativeFeatureRegion,
    latentFeatureRegion]

theorem SymbolicLatentAtlas.relativeFeatureRegion_cover_univ
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) :
    (⋃ k, A.relativeFeatureRegion k Set.univ) = Set.univ := by
  rw [show (⋃ k, A.relativeFeatureRegion k Set.univ) =
      ⋃ k, A.domain k by
    congr 1
    funext k
    exact A.relativeFeatureRegion_univ k]
  exact A.cover

abbrev SymbolicLatentAtlasDomain
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (k : κ) :=
  {x : X // x ∈ A.domain k}

def SymbolicLatentAtlas.relativeFeatureRegionInDomain
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι)) :
    Set (SymbolicLatentAtlasDomain A k) :=
  {x | (x : X) ∈ latentFeatureRegion (A.chart k) R}

theorem SymbolicLatentAtlas.isClosed_relativeFeatureRegionInDomain
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    (hR : IsClosed R) :
    IsClosed (A.relativeFeatureRegionInDomain k R) := by
  change IsClosed
    ((symbolicObservationMap (A.chart k).system ∘ Subtype.val) ⁻¹' R)
  exact hR.preimage
    ((continuous_symbolicObservationMap (A.chart k).system).comp
      continuous_subtype_val)

def SymbolicLatentAtlas.overlap
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (i j : κ) : Set X :=
  A.domain i ∩ A.domain j

structure SymbolicLatentAtlasCompatibility
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (i j : κ) where
  featureEquiv : SymbolicFeatureSpace ι ≃ₜ SymbolicFeatureSpace ι
  intertwines_on_overlap : ∀ x,
    x ∈ A.overlap i j →
      featureEquiv (symbolicObservationMap (A.chart i).system x) =
        symbolicObservationMap (A.chart j).system x

def SymbolicLatentAtlasCompatibility.symm
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : SymbolicLatentAtlas X ι κ} {i j : κ}
    (H : SymbolicLatentAtlasCompatibility A i j) :
    SymbolicLatentAtlasCompatibility A j i where
  featureEquiv := H.featureEquiv.symm
  intertwines_on_overlap := by
    intro x hx
    have hx' : x ∈ A.overlap i j := by
      change x ∈ A.domain j ∩ A.domain i at hx
      exact ⟨hx.2, hx.1⟩
    have h := H.intertwines_on_overlap x hx'
    rw [← h]
    simp

theorem SymbolicLatentAtlasCompatibility.trans_on_triple_overlap
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : SymbolicLatentAtlas X ι κ} {i j k : κ}
    (Hij : SymbolicLatentAtlasCompatibility A i j)
    (Hjk : SymbolicLatentAtlasCompatibility A j k)
    (hmiddle : ∀ x, x ∈ A.overlap i k → x ∈ A.domain j) :
    ∀ x, x ∈ A.overlap i k →
      (Hij.featureEquiv.trans Hjk.featureEquiv)
          (symbolicObservationMap (A.chart i).system x) =
        symbolicObservationMap (A.chart k).system x := by
  intro x hx
  have hij := Hij.intertwines_on_overlap x
    ⟨hx.1, hmiddle x hx⟩
  have hjk := Hjk.intertwines_on_overlap x
    ⟨hmiddle x hx, hx.2⟩
  change Hjk.featureEquiv
      (Hij.featureEquiv (symbolicObservationMap (A.chart i).system x)) =
    symbolicObservationMap (A.chart k).system x
  calc
    Hjk.featureEquiv
        (Hij.featureEquiv (symbolicObservationMap (A.chart i).system x)) =
      Hjk.featureEquiv (symbolicObservationMap (A.chart j).system x) :=
        congrArg Hjk.featureEquiv hij
    _ = symbolicObservationMap (A.chart k).system x := hjk

theorem SymbolicLatentAtlas.overlap_comm
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (i j : κ) :
    A.overlap i j = A.overlap j i := by
  ext x
  simp [SymbolicLatentAtlas.overlap, and_comm]

theorem SymbolicLatentAtlas.isOpen_overlap
    {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ) (i j : κ) :
    IsOpen (A.overlap i j) := by
  exact (A.isOpen_domain i).inter (A.isOpen_domain j)

end InfoGeometry.Topology
