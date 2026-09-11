import InfoGeometry.Topology.SymbolicLatentObservedPathFamilyReparametrizationCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImageCompHausUniversal
import InfoGeometry.Topology.SymbolicLatentPathFamilyReparametrizationColimit

/-!
# Colimit naturality for observed reparametrized images

The observed image changes as a subtype under reparametrization.  The
canonical readout therefore satisfies naturality only after composing with
the identity-on-values map between the two observed image carriers.
-/

namespace InfoGeometry.Topology

open CategoryTheory CategoryTheory.Limits
open SymbolicLatentPathFamilyTopCatColimit
open SymbolicLatentPathFamilyTopCatColimitImage
open SymbolicLatentPathFamilyTopCatColimitImageCompHaus

noncomputable section

variable {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
  [Fintype ι] [CompactSpace P] [T2Space X]

theorem observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout_reparametrization_natural
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
  apply TopCat.hom_ext
  ext z
  apply Subtype.ext
  have hcomp :
      (symbolicLatentPathFamilyReparametrizationColimitHom R ≫
          observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
            S H h_obs) ≫
          observedSymbolicLatentPathFamilyImageInclusionCompHausTopCatHom
            S H h_obs =
        (observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
            S (reparametrizeSymbolicLatentPathFamily R H) h_obs ≫
          compHausToTop.map
            (observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
              S R H h_obs)) ≫
          observedSymbolicLatentPathFamilyImageInclusionCompHausTopCatHom
            S H h_obs := by
    calc
      (symbolicLatentPathFamilyReparametrizationColimitHom R ≫
          observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
            S H h_obs) ≫
          observedSymbolicLatentPathFamilyImageInclusionCompHausTopCatHom
            S H h_obs =
          symbolicLatentPathFamilyReparametrizationColimitHom R ≫
            (observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
              S H h_obs ≫
              observedSymbolicLatentPathFamilyImageInclusionCompHausTopCatHom
                S H h_obs) := by rw [Category.assoc]
      _ = symbolicLatentPathFamilyReparametrizationColimitHom R ≫
          symbolicLatentPathFamilyTopCatColimitReadout S H h_obs := by
            rw [observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout_factorization]
      _ = symbolicLatentPathFamilyTopCatColimitReadout S
          (reparametrizeSymbolicLatentPathFamily R H) h_obs :=
        symbolicLatentPathFamilyReparametrizationColimitReadout_natural R H h_obs
      _ = observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
          S (reparametrizeSymbolicLatentPathFamily R H) h_obs ≫
          observedSymbolicLatentPathFamilyImageInclusionCompHausTopCatHom
            S (reparametrizeSymbolicLatentPathFamily R H) h_obs := by
            rw [observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout_factorization]
      _ = (observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
            S (reparametrizeSymbolicLatentPathFamily R H) h_obs ≫
          compHausToTop.map
            (observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
              S R H h_obs)) ≫
          observedSymbolicLatentPathFamilyImageInclusionCompHausTopCatHom
            S H h_obs := by
            change
              (observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
                  S (reparametrizeSymbolicLatentPathFamily R H) h_obs ≫
                observedSymbolicLatentPathFamilyImageInclusionTopCatHom
                  S (reparametrizeSymbolicLatentPathFamily R H) h_obs) =
                (observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
                    S (reparametrizeSymbolicLatentPathFamily R H) h_obs ≫
                  compHausToTop.map
                    (observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
                      S R H h_obs)) ≫
                  observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs
            rw [Category.assoc]
            rw [observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom_inclusion]
  have hz := congrArg (fun m => m z) hcomp
  change
    ((symbolicLatentPathFamilyReparametrizationColimitHom R ≫
        observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout S H h_obs) z).1 =
      ((observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
          S (reparametrizeSymbolicLatentPathFamily R H) h_obs ≫
        compHausToTop.map
          (observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
            S R H h_obs)) z).1 at hz
  exact hz

end
end InfoGeometry.Topology
