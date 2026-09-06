import Mathlib
import InfoGeometry.Topology.SymbolicLatentObservedFamilyImageTopCat
import InfoGeometry.Topology.SymbolicLatentPathFamilyReparametrizationTopCat

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

variable {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
  [Fintype ι]

/-!
# Reparametrization on observed family images

The observed image is a subtype of the feature space.  Reparametrization
does not change observed values; it only changes the range property.  The map
below therefore keeps the subtype value and transports its property along the
parameter map.
-/

def observedSymbolicLatentPathFamilyReparametrizationImageMap
    (S : FiniteSymbolicLatentSystem X ι)
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    observedSymbolicLatentPathFamilyImage S
        (reparametrizeSymbolicLatentPathFamily R H) h_obs →
      observedSymbolicLatentPathFamilyImage S H h_obs :=
  fun y =>
    ⟨y.1, by
      rcases y.2 with ⟨q, hq⟩
      refine ⟨(q.1, R.parameter q.2), ?_⟩
      simpa [observedSymbolicLatentPathFamily,
        reparametrizeSymbolicLatentPathFamily] using hq⟩

@[simp] theorem observedSymbolicLatentPathFamilyReparametrizationImageMap_apply
    (S : FiniteSymbolicLatentSystem X ι)
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (y : observedSymbolicLatentPathFamilyImage S
        (reparametrizeSymbolicLatentPathFamily R H) h_obs) :
    (observedSymbolicLatentPathFamilyReparametrizationImageMap
      S R H h_obs y).1 = y.1 :=
  rfl

def observedSymbolicLatentPathFamilyReparametrizationImageTopCatHom
    (S : FiniteSymbolicLatentSystem X ι)
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    TopCat.of (observedSymbolicLatentPathFamilyImage S
        (reparametrizeSymbolicLatentPathFamily R H) h_obs) ⟶
      TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs) :=
  TopCat.ofHom
    { toFun := observedSymbolicLatentPathFamilyReparametrizationImageMap
        S R H h_obs
      continuous_toFun :=
        continuous_subtype_val.subtype_mk
          (fun y =>
            (observedSymbolicLatentPathFamilyReparametrizationImageMap
              S R H h_obs y).2) }

@[simp] theorem observedSymbolicLatentPathFamilyReparametrizationImageTopCatHom_apply
    (S : FiniteSymbolicLatentSystem X ι)
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (y : observedSymbolicLatentPathFamilyImage S
        (reparametrizeSymbolicLatentPathFamily R H) h_obs) :
    observedSymbolicLatentPathFamilyReparametrizationImageTopCatHom
      S R H h_obs y =
      observedSymbolicLatentPathFamilyReparametrizationImageMap
        S R H h_obs y :=
  rfl

theorem observedSymbolicLatentPathFamilyImageEvaluation_reparametrization_natural
    (S : FiniteSymbolicLatentSystem X ι)
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    observedSymbolicLatentPathFamilyImageEvaluationTopCatHom
        S (reparametrizeSymbolicLatentPathFamily R H) h_obs ≫
      observedSymbolicLatentPathFamilyReparametrizationImageTopCatHom
        S R H h_obs =
      symbolicLatentPathFamilyParameterReparametrizationTopCatHom R ≫
        observedSymbolicLatentPathFamilyImageEvaluationTopCatHom
          S H h_obs := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  rfl

theorem observedSymbolicLatentPathFamilyReparametrizationImage_inclusion_natural
    (S : FiniteSymbolicLatentSystem X ι)
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    observedSymbolicLatentPathFamilyReparametrizationImageTopCatHom
        S R H h_obs ≫
      observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs =
      observedSymbolicLatentPathFamilyImageInclusionTopCatHom S
        (reparametrizeSymbolicLatentPathFamily R H) h_obs := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  rfl

theorem observedSymbolicLatentPathFamilyReparametrizationImageTopCatHom_identity
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    observedSymbolicLatentPathFamilyReparametrizationImageTopCatHom
        S identitySymbolicLatentPathReparametrization H h_obs =
      𝟙 (TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs)) := by
  have h := reparametrizeSymbolicLatentPathFamily_identity H
  cases h
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  rfl

theorem observedSymbolicLatentPathFamilyReparametrizationImageTopCatHom_comp
    (S : FiniteSymbolicLatentSystem X ι)
    (R T : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    observedSymbolicLatentPathFamilyReparametrizationImageTopCatHom
        S R (reparametrizeSymbolicLatentPathFamily T H) h_obs ≫
      observedSymbolicLatentPathFamilyReparametrizationImageTopCatHom
        S T H h_obs =
      observedSymbolicLatentPathFamilyReparametrizationImageTopCatHom
        S (composeSymbolicLatentPathReparametrization R T) H h_obs := by
  have h := reparametrizeSymbolicLatentPathFamily_comp R T H
  cases h
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  rfl

end

end InfoGeometry.Topology
