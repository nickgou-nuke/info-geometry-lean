import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentSpace

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Feasible symbolic-latent subspaces in `TopCat`

The feasible subtype and its continuous transport are native declarations of
`SymbolicLatentSpace`.  This owner exposes that transport categorically and
records identity and composition for a fixed target family.
-/

def symbolicLatentFeasibleSubspaceTopCatHom
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T)
    (targets : ι → Set ℝ) :
    TopCat.of (feasibleLatentSubspace S targets) ⟶
      TopCat.of (feasibleLatentSubspace T targets) :=
  TopCat.ofHom
    { toFun := F.feasibleSubspaceMap targets
      continuous_toFun := F.continuous_feasibleSubspaceMap targets }

theorem symbolicLatentFeasibleSubspaceTopCatHom_apply
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T)
    (targets : ι → Set ℝ)
    (x : feasibleLatentSubspace S targets) :
    symbolicLatentFeasibleSubspaceTopCatHom F targets x =
      F.feasibleSubspaceMap targets x :=
  rfl

def symbolicLatentFeasibleSubspaceInclusion
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (targets : ι → Set ℝ) :
    TopCat.of (feasibleLatentSubspace S targets) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := (Subtype.val : feasibleLatentSubspace S targets → X)
      continuous_toFun := continuous_subtype_val }

theorem symbolicLatentFeasibleSubspaceInclusion_apply
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (targets : ι → Set ℝ)
    (x : feasibleLatentSubspace S targets) :
    symbolicLatentFeasibleSubspaceInclusion S targets x = x.1 :=
  rfl

theorem symbolicLatentFeasibleSubspace_isClosedEmbedding
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    Topology.IsClosedEmbedding
      (Subtype.val : feasibleLatentSubspace S targets → X) := by
  exact (isClosed_finiteSymbolicLatentSystem_feasibleSet
    S targets hclosed).isClosedEmbedding_subtypeVal

theorem isCompact_symbolicLatentFeasibleSubspace
    {X ι : Type} [TopologicalSpace X] [CompactSpace X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    IsCompact ((Subtype.val : feasibleLatentSubspace S targets → X) ''
      (Set.univ : Set (feasibleLatentSubspace S targets))) := by
  simpa only [Set.image_univ, Subtype.range_val] using
    isCompact_finiteSymbolicLatentSystem_feasibleSet S targets hclosed

def symbolicLatentFeasibleFeatureRegion
    {ι : Type} [Fintype ι] (targets : ι → Set ℝ) : Set (ι → ℝ) :=
  {v | ∀ i, v i ∈ targets i}

theorem isClosed_symbolicLatentFeasibleFeatureRegion
    {ι : Type} [Fintype ι] (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    IsClosed (symbolicLatentFeasibleFeatureRegion targets) := by
  rw [show symbolicLatentFeasibleFeatureRegion targets =
      ⋂ i, (fun v : ι → ℝ => v i) ⁻¹' targets i by
    ext v
    simp [symbolicLatentFeasibleFeatureRegion]]
  exact isClosed_iInter (fun i => (hclosed i).preimage (continuous_apply i))

theorem isCompact_symbolicLatentFeasibleFeatureRegion
    {ι : Type} [Fintype ι] (targets : ι → Set ℝ)
    (hcompact : ∀ i, IsCompact (targets i)) :
    IsCompact (symbolicLatentFeasibleFeatureRegion targets) := by
  change IsCompact {v : ι → ℝ | ∀ i, v i ∈ targets i}
  exact isCompact_pi_infinite hcompact

def symbolicLatentFeasibleObservationTopCatHom
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (targets : ι → Set ℝ) :
    TopCat.of (feasibleLatentSubspace S targets) ⟶ TopCat.of (ι → ℝ) :=
  TopCat.ofHom
    { toFun := fun x => symbolicObservationMap S x
      continuous_toFun :=
        (continuous_symbolicObservationMap S).comp continuous_subtype_val }

theorem symbolicLatentFeasibleObservationTopCatHom_apply
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (targets : ι → Set ℝ)
    (x : feasibleLatentSubspace S targets) :
    symbolicLatentFeasibleObservationTopCatHom S targets x =
      symbolicObservationMap S x :=
  rfl

theorem symbolicLatentFeasibleObservation_mem_region
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (targets : ι → Set ℝ)
    (x : feasibleLatentSubspace S targets) :
    symbolicObservationMap S x ∈
      symbolicLatentFeasibleFeatureRegion targets := by
  intro i
  exact x.property i

def symbolicLatentFeasibleRegionObservationTopCatHom
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (targets : ι → Set ℝ) :
    TopCat.of (feasibleLatentSubspace S targets) ⟶
      TopCat.of (symbolicLatentFeasibleFeatureRegion targets) :=
  TopCat.ofHom
    { toFun := fun x =>
        ⟨symbolicObservationMap S x,
          symbolicLatentFeasibleObservation_mem_region S targets x⟩
      continuous_toFun :=
        ((continuous_symbolicObservationMap S).comp continuous_subtype_val).subtype_mk
          (fun x => symbolicLatentFeasibleObservation_mem_region S targets x) }

theorem symbolicLatentFeasibleRegionObservationTopCatHom_apply
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (targets : ι → Set ℝ)
    (x : feasibleLatentSubspace S targets) :
    symbolicLatentFeasibleRegionObservationTopCatHom S targets x =
      ⟨symbolicObservationMap S x,
        symbolicLatentFeasibleObservation_mem_region S targets x⟩ :=
  rfl

def symbolicLatentFeasibleFeatureRegionInclusionTopCatHom
    {ι : Type} [Fintype ι] (targets : ι → Set ℝ) :
    TopCat.of (symbolicLatentFeasibleFeatureRegion targets) ⟶
      TopCat.of (ι → ℝ) :=
  TopCat.ofHom
    { toFun := (Subtype.val : symbolicLatentFeasibleFeatureRegion targets → (ι → ℝ))
      continuous_toFun := continuous_subtype_val }

theorem symbolicLatentFeasibleFeatureRegion_isClosedEmbedding
    {ι : Type} [Fintype ι] (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    Topology.IsClosedEmbedding
      (Subtype.val : symbolicLatentFeasibleFeatureRegion targets → (ι → ℝ)) := by
  exact (isClosed_symbolicLatentFeasibleFeatureRegion targets hclosed).isClosedEmbedding_subtypeVal

theorem symbolicLatentFeasibleObservationTopCatHom_factorization
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (targets : ι → Set ℝ) :
    symbolicLatentFeasibleRegionObservationTopCatHom S targets ≫
        symbolicLatentFeasibleFeatureRegionInclusionTopCatHom targets =
      symbolicLatentFeasibleObservationTopCatHom S targets := by
  ext x
  rfl

theorem symbolicLatentFeasibleSubspaceTopCatHom_id
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ) :
    symbolicLatentFeasibleSubspaceTopCatHom
        (SymbolicLatentMorphism.id S) targets =
      𝟙 (TopCat.of (feasibleLatentSubspace S targets)) := by
  ext x
  rfl

theorem symbolicLatentFeasibleSubspaceTopCatHom_comp
    {X Y Z ι : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T)
    (targets : ι → Set ℝ) :
    symbolicLatentFeasibleSubspaceTopCatHom
        (SymbolicLatentMorphism.comp g f) targets =
      symbolicLatentFeasibleSubspaceTopCatHom f targets ≫
        symbolicLatentFeasibleSubspaceTopCatHom g targets := by
  ext x
  rfl

theorem symbolicLatentFeasibleSubspaceTopCatHom_comp_apply
    {X Y Z ι : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T)
    (targets : ι → Set ℝ)
    (x : feasibleLatentSubspace S targets) :
    (symbolicLatentFeasibleSubspaceTopCatHom
        (SymbolicLatentMorphism.comp g f) targets) x =
      (symbolicLatentFeasibleSubspaceTopCatHom f targets ≫
        symbolicLatentFeasibleSubspaceTopCatHom g targets) x := by
  rfl

end InfoGeometry.Topology
