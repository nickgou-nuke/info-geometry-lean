import InfoGeometry.Topology.SymbolicLatentVaryingCarrierCategory

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Feasible observations for varying-carrier symbolic-latent systems

The feasible-subspace functor records the varying latent carriers.  This
owner supplies the observation readouts as natural transformations, so the
feature-region factorization is available at the categorical level rather
than being reproved object by object.
-/

noncomputable def varyingCarrierFeasibleObservationAmbient
    (ι : Type) [Fintype ι] (targets : ι → Set ℝ) :
    varyingCarrierFeasibleSubspaceFunctor ι targets ⟶
      (Functor.const (SymbolicLatentSystemObject ι)).obj
        (TopCat.of (ι → ℝ)) where
  app S := symbolicLatentFeasibleObservationTopCatHom S.system targets
  naturality := by
    intro S T F
    apply TopCat.hom_ext
    ext x
    change symbolicObservationMap T.system
        ((F.toNative.feasibleSubspaceMap targets x).1) =
      symbolicObservationMap S.system x.1
    exact funext (fun i => F.toNative.intertwines i x.1)

noncomputable def varyingCarrierFeasibleObservationRegion
    (ι : Type) [Fintype ι] (targets : ι → Set ℝ) :
    varyingCarrierFeasibleSubspaceFunctor ι targets ⟶
      (Functor.const (SymbolicLatentSystemObject ι)).obj
        (TopCat.of (symbolicLatentFeasibleFeatureRegion targets)) where
  app S := symbolicLatentFeasibleRegionObservationTopCatHom S.system targets
  naturality := by
    intro S T F
    apply TopCat.hom_ext
    ext x
    apply Subtype.ext
    change symbolicObservationMap T.system
        ((F.toNative.feasibleSubspaceMap targets x).1) =
      symbolicObservationMap S.system x.1
    exact funext (fun i => F.toNative.intertwines i x.1)

noncomputable def varyingCarrierFeasibleFeatureRegionInclusion
    (ι : Type) [Fintype ι] (targets : ι → Set ℝ) :
    (Functor.const (SymbolicLatentSystemObject ι)).obj
        (TopCat.of (symbolicLatentFeasibleFeatureRegion targets)) ⟶
      (Functor.const (SymbolicLatentSystemObject ι)).obj
        (TopCat.of (ι → ℝ)) where
  app _ := symbolicLatentFeasibleFeatureRegionInclusionTopCatHom targets
  naturality := by
    intro S T F
    rfl

theorem varyingCarrierFeasibleObservation_factorization
    (ι : Type) [Fintype ι] (targets : ι → Set ℝ) :
    varyingCarrierFeasibleObservationRegion ι targets ≫
        varyingCarrierFeasibleFeatureRegionInclusion ι targets =
      varyingCarrierFeasibleObservationAmbient ι targets := by
  ext S x
  rfl

  theorem varyingCarrierFeasibleObservation_region_mem
    (ι : Type) [Fintype ι] (targets : ι → Set ℝ)
    (S : SymbolicLatentSystemObject ι)
    (x : feasibleLatentSubspace S.system targets) :
    symbolicObservationMap S.system x ∈
      symbolicLatentFeasibleFeatureRegion targets :=
  by
    change ∀ i, (S.system.observable i) (x : S.carrier) ∈ targets i
    exact x.property

end InfoGeometry.Topology
