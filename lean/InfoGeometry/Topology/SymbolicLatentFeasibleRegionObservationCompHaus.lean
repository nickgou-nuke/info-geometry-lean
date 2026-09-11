import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentFeasibleRegionCompHaus
import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceTopCat

/-!
# Compact-Hausdorff observation into a feasible feature region

The feasible latent subtype and the finite product of closed target sets are
already compact-Hausdorff objects.  This file exposes the native observation
map between those objects as a genuine `CompHaus` morphism and identifies its
forgetful image with the existing `TopCat` morphism.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [Fintype ι]

noncomputable def symbolicLatentFeasibleRegionObservationCompHausHom
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i))
    (hcompact : ∀ i, IsCompact (targets i)) :
    symbolicLatentFeasibleSubspaceCompHaus S targets hclosed ⟶
      symbolicLatentFeasibleFeatureRegionCompHaus targets hcompact := by
  letI : CompactSpace (feasibleLatentSubspace S targets) :=
    (isClosed_finiteSymbolicLatentSystem_feasibleSet S targets hclosed
      ).isClosedEmbedding_subtypeVal.compactSpace
  letI : CompactSpace (symbolicLatentFeasibleFeatureRegion targets) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicLatentFeasibleFeatureRegion targets hcompact)
  change CompHaus.of (feasibleLatentSubspace S targets) ⟶
    CompHaus.of (symbolicLatentFeasibleFeatureRegion targets)
  exact ⟨TopCat.ofHom
    { toFun := fun x =>
        ⟨symbolicObservationMap S x,
          symbolicLatentFeasibleObservation_mem_region S targets x⟩
      continuous_toFun :=
        ((continuous_symbolicObservationMap S).comp continuous_subtype_val).subtype_mk
          (fun x => symbolicLatentFeasibleObservation_mem_region S targets x) }⟩

@[simp] theorem symbolicLatentFeasibleRegionObservationCompHausHom_apply
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i))
    (hcompact : ∀ i, IsCompact (targets i))
    (x : feasibleLatentSubspace S targets) :
    symbolicLatentFeasibleRegionObservationCompHausHom
        S targets hclosed hcompact x =
      ⟨symbolicObservationMap S x,
        symbolicLatentFeasibleObservation_mem_region S targets x⟩ := by
  rfl

theorem symbolicLatentFeasibleRegionObservationCompHausHom_forget
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i))
    (hcompact : ∀ i, IsCompact (targets i)) :
    compHausToTop.map
        (symbolicLatentFeasibleRegionObservationCompHausHom
          S targets hclosed hcompact) =
      symbolicLatentFeasibleRegionObservationCompHausTopCatHom
        S targets hcompact := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

end InfoGeometry.Topology
