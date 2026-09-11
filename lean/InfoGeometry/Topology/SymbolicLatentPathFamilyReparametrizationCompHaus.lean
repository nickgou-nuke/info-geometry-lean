import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathFamilyReparametrizationTopCat
import InfoGeometry.Topology.SymbolicLatentPathFamilyImageEquivCompHaus

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

variable {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
  [CompactSpace P] [T2Space X]

/-!
The image action of a path-family reparametrization is continuous on compact
family images, hence it also has a canonical `CompHaus` packaging.  The
underlying map is the TopCat map from the preceding owner; this file adds no
new algebraic content.
-/

noncomputable def symbolicLatentPathFamilyReparametrizationImageCompHausHom
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageCompHaus
        (reparametrizeSymbolicLatentPathFamily R H) ⟶
      symbolicLatentPathFamilyImageCompHaus H := by
  letI : CompactSpace
      (symbolicLatentPathFamilyImage
        (reparametrizeSymbolicLatentPathFamily R H)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicLatentPathFamilyImage
        (reparametrizeSymbolicLatentPathFamily R H))
  letI : CompactSpace (symbolicLatentPathFamilyImage H) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicLatentPathFamilyImage H)
  change CompHaus.of
      (symbolicLatentPathFamilyImage
        (reparametrizeSymbolicLatentPathFamily R H)) ⟶
    CompHaus.of (symbolicLatentPathFamilyImage H)
  exact ⟨symbolicLatentPathFamilyReparametrizationImageTopCatHom R H⟩

theorem symbolicLatentPathFamilyReparametrizationImageCompHausHom_forget
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X) :
    compHausToTop.map
        (symbolicLatentPathFamilyReparametrizationImageCompHausHom R H) =
      symbolicLatentPathFamilyReparametrizationImageTopCatHom R H := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  rfl

theorem symbolicLatentPathFamilyImageEvaluation_reparametrization_CompHaus_natural
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageEvaluationTopCatHom
        (reparametrizeSymbolicLatentPathFamily R H) ≫
        compHausToTop.map
          (symbolicLatentPathFamilyReparametrizationImageCompHausHom R H) =
      symbolicLatentPathFamilyParameterReparametrizationTopCatHom R ≫
        symbolicLatentPathFamilyImageEvaluationTopCatHom H := by
  change symbolicLatentPathFamilyImageEvaluationTopCatHom
      (reparametrizeSymbolicLatentPathFamily R H) ≫
      symbolicLatentPathFamilyReparametrizationImageTopCatHom R H =
    symbolicLatentPathFamilyParameterReparametrizationTopCatHom R ≫
      symbolicLatentPathFamilyImageEvaluationTopCatHom H
  exact symbolicLatentPathFamilyImageEvaluation_reparametrization_natural R H

theorem symbolicLatentPathFamilyReparametrizationImageCompHausHom_identity
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyReparametrizationImageCompHausHom
        identitySymbolicLatentPathReparametrization H =
      𝟙 (symbolicLatentPathFamilyImageCompHaus H) := by
  have h := reparametrizeSymbolicLatentPathFamily_identity H
  cases h
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem symbolicLatentPathFamilyReparametrizationImageCompHausHom_comp
    (R S : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyReparametrizationImageCompHausHom
        (composeSymbolicLatentPathReparametrization R S) H =
      symbolicLatentPathFamilyReparametrizationImageCompHausHom R
        (reparametrizeSymbolicLatentPathFamily S H) ≫
        symbolicLatentPathFamilyReparametrizationImageCompHausHom S H := by
  have h := reparametrizeSymbolicLatentPathFamily_comp R S H
  cases h
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end

end InfoGeometry.Topology
