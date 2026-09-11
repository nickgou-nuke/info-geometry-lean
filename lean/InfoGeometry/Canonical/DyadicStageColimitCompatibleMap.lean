import InfoGeometry.Canonical.DyadicStageTopCatColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TopCatColimitCompatibleMap

/-!
# Dyadic stage readout as a concrete colimit-compatible map

The existing readout cocone is used as a genuine natural transformation into
the constant `DyadicRational` diagram.  Its induced colimit map is then
identified with the repository's direct stage-colimit readout.
-/

namespace InfoGeometry.Canonical.DyadicStageColimitCompatibleMap

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.DyadicDimensionGroupTopCat
open InfoGeometry.Canonical.DyadicStageTopCatColimit
open InfoGeometry.Canonical.TopCatColimitCompatibleMap

noncomputable section

abbrev dyadicRationalConstantDiagram : ℕ ⥤ TopCat :=
  (Functor.const ℕ).obj dyadicRationalTopCat

noncomputable def dyadicRationalConstantCocone :
    Cocone dyadicRationalConstantDiagram where
  pt := dyadicRationalTopCat
  ι :=
    { app := fun _ => 𝟙 dyadicRationalTopCat
      naturality := by
        intro i j f
        simp }

noncomputable def dyadicStageReadoutColimitMap :
    dyadicStageTopCatColimit ⟶
      colimit dyadicRationalConstantDiagram :=
  inducedMap dyadicStageReadoutCocone.ι

noncomputable def dyadicRationalConstantColimitReadout :
    colimit dyadicRationalConstantDiagram ⟶ dyadicRationalTopCat :=
  colimit.desc dyadicRationalConstantDiagram
    dyadicRationalConstantCocone

theorem dyadicStageReadoutColimitMap_on_stage (n : ℕ) :
    colimit.ι dyadicStageDiagram n ≫
        dyadicStageReadoutColimitMap =
      dyadicStageReadoutCocone.ι.app n ≫
        colimit.ι dyadicRationalConstantDiagram n := by
  exact inducedMap_on_stage dyadicStageReadoutCocone.ι n

theorem dyadicRationalConstantColimitReadout_on_stage (n : ℕ) :
    colimit.ι dyadicRationalConstantDiagram n ≫
        dyadicRationalConstantColimitReadout =
      𝟙 dyadicRationalTopCat := by
  exact colimit.ι_desc dyadicRationalConstantCocone n

theorem dyadicStageReadoutColimitMap_comp_constantReadout :
    dyadicStageReadoutColimitMap ≫
        dyadicRationalConstantColimitReadout =
      dyadicStageColimitReadout := by
  apply colimit.hom_ext
  intro n
  calc
    colimit.ι dyadicStageDiagram n ≫
        dyadicStageReadoutColimitMap ≫
          dyadicRationalConstantColimitReadout =
      (colimit.ι dyadicStageDiagram n ≫
        dyadicStageReadoutColimitMap) ≫
          dyadicRationalConstantColimitReadout :=
      (Category.assoc _ _ _).symm
    _ = (dyadicStageReadoutCocone.ι.app n ≫
        colimit.ι dyadicRationalConstantDiagram n) ≫
          dyadicRationalConstantColimitReadout := by
      rw [dyadicStageReadoutColimitMap_on_stage]
    _ = dyadicStageReadoutCocone.ι.app n ≫
        (colimit.ι dyadicRationalConstantDiagram n ≫
          dyadicRationalConstantColimitReadout) :=
      Category.assoc _ _ _
    _ = dyadicStageReadoutCocone.ι.app n := by
      rw [dyadicRationalConstantColimitReadout_on_stage]
      exact Category.comp_id _
    _ = colimit.ι dyadicStageDiagram n ≫
        dyadicStageColimitReadout := by
      rw [dyadicStageColimitReadout_stage]

end
end InfoGeometry.Canonical.DyadicStageColimitCompatibleMap
