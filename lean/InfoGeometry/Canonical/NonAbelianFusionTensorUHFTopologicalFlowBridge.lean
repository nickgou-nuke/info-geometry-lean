import InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalFlow
import InfoGeometry.Canonical.NonAbelianFusionTensorUHFTopologicalBridge

/-!
# Intertwining of tensor-fusion and UHF topological flows

This bridge isolates the exact stagewise compatibility needed to transport a
continuous flow from the tensor fusion colimit to the UHF/Cuntz colimit.  The
intertwining equality is then a direct consequence of the colimit universal
property, with no analytic extension asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.NonAbelianFusionTensorUHFTopologicalFlowBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
open InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalColimit
open InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalFlow
open InfoGeometry.Canonical.NonAbelianFusionTensorUHFTopologicalBridge
open FilteredColimit.Native.Topological

variable (D : TensorTopologicalFlowData)
variable (T : CuntzMatrixTraceTower.Data)
variable (targetFlow : ℝ →
  (topologicalColimitObject T ⟶ topologicalColimitObject T))

def StageFlowCompatible : Prop :=
  ∀ t : ℝ,
    fusionTensorStageTwoTopCatHom ≫ topologicalInclusion T 2 ≫
        targetFlow t =
      (D.flow t).hom ≫ fusionTensorStageTwoTopCatHom ≫
        topologicalInclusion T 2

theorem flow_intertwines_tensor_to_UHF
    (hcompat : StageFlowCompatible D T targetFlow) (t : ℝ) :
    fusionTensorToUHFTopologicalColimit T ≫ targetFlow t =
      flowColimitMap D t ≫ fusionTensorToUHFTopologicalColimit T := by
  apply colimit.hom_ext
  intro n
  change topologicalDirectInjection
      (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
      (fusionTensorToUHFTopologicalColimit T ≫ targetFlow t) =
    topologicalDirectInjection
      (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
      (flowColimitMap D t ≫ fusionTensorToUHFTopologicalColimit T)
  calc
    _ = (topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
        fusionTensorToUHFTopologicalColimit T) ≫ targetFlow t := by
          simp only [Category.assoc]
    _ = (fusionTensorStageTwoTopCatHom ≫ topologicalInclusion T 2) ≫
        targetFlow t := by
          rw [fusionTensorToUHFTopologicalColimit_stage]
    _ = ((D.flow t).hom ≫ fusionTensorStageTwoTopCatHom) ≫
        topologicalInclusion T 2 := by
          simpa only [Category.assoc] using hcompat t
    _ = (D.flow t).hom ≫
        (fusionTensorStageTwoTopCatHom ≫ topologicalInclusion T 2) := by
          simp only [Category.assoc]
    _ = (D.flow t).hom ≫
        (topologicalDirectInjection
          (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
          fusionTensorToUHFTopologicalColimit T) := by
          rw [fusionTensorToUHFTopologicalColimit_stage]
    _ = ((D.flow t).hom ≫ topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := ℂ)) n) ≫
        fusionTensorToUHFTopologicalColimit T := by
          simp only [Category.assoc]
    _ = (topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
        flowColimitMap D t) ≫ fusionTensorToUHFTopologicalColimit T := by
          rw [← flowColimitMap_stage]
    _ = topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
        (flowColimitMap D t ≫ fusionTensorToUHFTopologicalColimit T) := by
          simp only [Category.assoc]

end InfoGeometry.Canonical.NonAbelianFusionTensorUHFTopologicalFlowBridge
