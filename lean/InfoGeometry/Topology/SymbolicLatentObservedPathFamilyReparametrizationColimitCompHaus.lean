import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImageCompHaus
import InfoGeometry.Topology.SymbolicLatentObservedPathFamilyReparametrizationCompHaus
import InfoGeometry.Topology.SymbolicLatentPathFamilyReparametrizationColimit

namespace InfoGeometry.Topology

open CategoryTheory CategoryTheory.Limits
open SymbolicLatentPathFamilyTopCatColimit
open SymbolicLatentPathFamilyTopCatColimitImage
open SymbolicLatentPathFamilyTopCatColimitImageCompHaus

noncomputable section

variable {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
  [CompactSpace P] [T2Space X] [Fintype ι]

/-!
# Colimit naturality of the compact observed-image readout

The corridor colimit carries the parameter reparametrization endomorphism,
while the observed image carries the corresponding compact-Hausdorff map.
This theorem is the resulting universal-property square.
-/

theorem observedSymbolicLatentPathFamilyReparametrizationColimitCompHausReadout_natural
    (S : FiniteSymbolicLatentSystem X ι)
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    symbolicLatentPathFamilyReparametrizationColimitHom R ≫
        observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
          S H h_obs =
      observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
        S (reparametrizeSymbolicLatentPathFamily R H) h_obs ≫
        compHausToTop.map
          (observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
            S R H h_obs) := by
  apply colimit.hom_ext
  intro i
  cases i with
  | initial =>
      rw [← Category.assoc,
        symbolicLatentPathFamilyReparametrizationColimitHom_initial,
        observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout_stage
          S H h_obs .initial]
      rw [← Category.assoc,
        observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout_stage
          S (reparametrizeSymbolicLatentPathFamily R H) h_obs .initial]
      change observedSymbolicLatentPathFamilyStartImageTopCatHom S H h_obs =
        observedSymbolicLatentPathFamilyStartImageTopCatHom S
            (reparametrizeSymbolicLatentPathFamily R H) h_obs ≫
          compHausToTop.map
            (observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
            S R H h_obs)
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro p
      have hR := congrArg
        (fun t : SymbolicPathDomain => symbolicObservationMap S (H (p, t)))
        R.at_zero
      apply Subtype.ext
      simpa [observedSymbolicLatentPathFamilyStartImageTopCatHom,
        observedSymbolicLatentPathFamilyImageEvaluationTopCatHom,
        observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom_forget,
        observedSymbolicLatentPathFamilyReparametrizationImageMap,
        observedSymbolicLatentPathFamily,
        symbolicLatentPathFamilyStartParameterTopCatHom,
        TopCat.comp_app, TopCat.ofHom] using hR.symm
  | extended =>
      rw [← Category.assoc,
        symbolicLatentPathFamilyReparametrizationColimitHom_extended,
        Category.assoc,
        observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout_stage
          S H h_obs .extended]
      rw [← Category.assoc,
        observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout_stage
          S (reparametrizeSymbolicLatentPathFamily R H) h_obs .extended]
      change symbolicLatentPathFamilyParameterReparametrizationTopCatHom R ≫
          observedSymbolicLatentPathFamilyImageEvaluationTopCatHom S H h_obs =
        observedSymbolicLatentPathFamilyImageEvaluationTopCatHom S
          (reparametrizeSymbolicLatentPathFamily R H) h_obs ≫
          compHausToTop.map
            (observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
            S R H h_obs)
      rw [observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom_forget]
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro q
      rfl

end

end InfoGeometry.Topology
