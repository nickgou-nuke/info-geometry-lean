import InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservedFamilyImageTopCat

namespace InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImage

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology
open InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimit
open InfoGeometry.Topology.SpinorSpectrumTopCatColimit

variable {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
variable [Fintype ι]

/-!
The observed path-family colimit readout factors through the native image
subtype.  The initial corridor stage is included by evaluating the image map
at the start parameter, while the extended stage uses the existing image
evaluation map.
-/

def observedSymbolicLatentPathFamilyStartImageTopCatHom
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    TopCat.of P ⟶
      TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs) :=
  symbolicLatentPathFamilyStartParameterTopCatHom P ≫
    observedSymbolicLatentPathFamilyImageEvaluationTopCatHom S H h_obs

def observedSymbolicLatentPathFamilyImageCocone
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    Cocone (symbolicLatentPathFamilyTopCatDiagram (P := P)) where
  pt := TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs)
  ι :=
    { app
        | .initial => observedSymbolicLatentPathFamilyStartImageTopCatHom
            S H h_obs
        | .extended => observedSymbolicLatentPathFamilyImageEvaluationTopCatHom
            S H h_obs
      naturality := by
        intro i j g
        change SpinorSpectrumTopCatColimit.SpinorStage.Hom i j at g
        cases g with
        | idInitial => rfl
        | step =>
            apply TopCat.hom_ext
            ext p
            rfl
        | idExtended => rfl }

noncomputable def observedSymbolicLatentPathFamilyTopCatColimitImageReadout
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    symbolicLatentPathFamilyTopCatColimit (P := P) ⟶
      TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs) :=
  colimit.desc (symbolicLatentPathFamilyTopCatDiagram (P := P))
    (observedSymbolicLatentPathFamilyImageCocone S H h_obs)

theorem observedSymbolicLatentPathFamilyTopCatColimitImageReadout_stage
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (i : SpinorSpectrumTopCatColimit.SpinorStage) :
    colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫
        observedSymbolicLatentPathFamilyTopCatColimitImageReadout S H h_obs =
      (observedSymbolicLatentPathFamilyImageCocone S H h_obs).ι.app i :=
  colimit.ι_desc
    (observedSymbolicLatentPathFamilyImageCocone S H h_obs) i

theorem observedSymbolicLatentPathFamilyTopCatColimitImageReadout_factorization
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    observedSymbolicLatentPathFamilyTopCatColimitImageReadout S H h_obs ≫
        observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs =
      symbolicLatentPathFamilyTopCatColimitReadout S H h_obs := by
  apply colimit.hom_ext
  intro i
  change (colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫
      observedSymbolicLatentPathFamilyTopCatColimitImageReadout S H h_obs) ≫
      observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs =
    colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫
      symbolicLatentPathFamilyTopCatColimitReadout S H h_obs
  rw [observedSymbolicLatentPathFamilyTopCatColimitImageReadout_stage,
    symbolicLatentPathFamilyTopCatColimitReadout_stage]
  cases i with
  | initial =>
      change observedSymbolicLatentPathFamilyStartImageTopCatHom S H h_obs ≫
          observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs =
        observedSymbolicLatentPathFamilyStartTopCatHom S H h_obs
      apply TopCat.hom_ext
      ext p
      rfl
  | extended =>
      change observedSymbolicLatentPathFamilyImageEvaluationTopCatHom S H h_obs ≫
          observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs =
        observedSymbolicLatentPathFamilyTopCatHom S H h_obs
      exact observedSymbolicLatentPathFamilyImage_evaluation_factorization
        S H h_obs

theorem observedSymbolicLatentPathFamilyTopCatColimitImageReadout_unique
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    {u : symbolicLatentPathFamilyTopCatColimit (P := P) ⟶
      TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs)}
    (hu : u ≫ observedSymbolicLatentPathFamilyImageInclusionTopCatHom
        S H h_obs =
      symbolicLatentPathFamilyTopCatColimitReadout S H h_obs) :
    u = observedSymbolicLatentPathFamilyTopCatColimitImageReadout S H h_obs := by
  apply colimit.hom_ext
  intro i
  have hstage := congrArg
    (fun m => colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫ m) hu
  change (colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫ u) ≫
      observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs =
    colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫
      symbolicLatentPathFamilyTopCatColimitReadout S H h_obs at hstage
  have hstage' :
      (colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫ u) ≫
          observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs =
        (symbolicLatentPathFamilyTopCatReadout S H h_obs).app i := by
    exact hstage.trans
      (symbolicLatentPathFamilyTopCatColimitReadout_stage S H h_obs i)
  have hfactorGlobal := congrArg
    (fun m => colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫ m)
    (observedSymbolicLatentPathFamilyTopCatColimitImageReadout_factorization
      S H h_obs)
  change (colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫
      observedSymbolicLatentPathFamilyTopCatColimitImageReadout S H h_obs) ≫
      observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs =
    colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫
      symbolicLatentPathFamilyTopCatColimitReadout S H h_obs at hfactorGlobal
  have hfactor' :
      (colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫
          observedSymbolicLatentPathFamilyTopCatColimitImageReadout S H h_obs) ≫
          observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs =
        (symbolicLatentPathFamilyTopCatReadout S H h_obs).app i := by
    exact hfactorGlobal.trans
      (symbolicLatentPathFamilyTopCatColimitReadout_stage S H h_obs i)
  apply TopCat.ext
  intro x
  apply Subtype.ext
  simpa [TopCat.comp_app, TopCat.ofHom,
    observedSymbolicLatentPathFamilyTopCatColimitImageReadout] using
    congrArg (fun m => m x) (hstage'.trans hfactor'.symm)

end InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImage
