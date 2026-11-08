import InfoGeometry.Topology.SymbolicLatentPathFamilyReparametrizationCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathFamilyImageEvaluationCompHaus

/-!
# CompHaus/TopCat bridge for path-family reparametrization

The reparametrization image map is already a `CompHaus` morphism, while the
parameter reparametrization and the colimit readout remain `TopCat` maps.  This
owner records the mixed categorical naturality square without pretending that
the colimit carrier is compact Hausdorff.
-/

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

variable {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
  [CompactSpace P] [T2Space P] [T2Space X]

theorem symbolicLatentPathFamilyImageEvaluation_reparametrization_CompHaus_map_natural
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X) :
    compHausToTop.map
        (symbolicLatentPathFamilyImageEvaluationCompHausHom
          (reparametrizeSymbolicLatentPathFamily R H)) ≫
        compHausToTop.map
          (symbolicLatentPathFamilyReparametrizationImageCompHausHom R H) =
      symbolicLatentPathFamilyParameterReparametrizationTopCatHom R ≫
        compHausToTop.map
          (symbolicLatentPathFamilyImageEvaluationCompHausHom H) := by
  rw [symbolicLatentPathFamilyImageEvaluationCompHausHom_forget,
    symbolicLatentPathFamilyReparametrizationImageCompHausHom_forget,
    symbolicLatentPathFamilyImageEvaluationCompHausHom_forget]
  exact symbolicLatentPathFamilyImageEvaluation_reparametrization_natural R H

end
end InfoGeometry.Topology
