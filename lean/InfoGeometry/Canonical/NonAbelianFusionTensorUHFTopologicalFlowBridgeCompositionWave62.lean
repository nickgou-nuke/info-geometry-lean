/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NonAbelianFusionTensorUHFTopologicalFlowBridge
import InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalFlowCompositionWave61

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

theorem flow_intertwines_tensor_to_UHF_comp
    (hcompat : StageFlowCompatible D T targetFlow)
    (htarget : ∀ s t : ℝ,
      targetFlow s ≫ targetFlow t = targetFlow (s + t))
    (s t : ℝ) :
    fusionTensorToUHFTopologicalColimit T ≫ targetFlow s ≫ targetFlow t =
      flowColimitMap D (s + t) ≫ fusionTensorToUHFTopologicalColimit T := by
  calc
    fusionTensorToUHFTopologicalColimit T ≫ targetFlow s ≫ targetFlow t =
        fusionTensorToUHFTopologicalColimit T ≫ targetFlow (s + t) := by
      rw [htarget]
    _ = flowColimitMap D (s + t) ≫
        fusionTensorToUHFTopologicalColimit T :=
      flow_intertwines_tensor_to_UHF D T targetFlow hcompat (s + t)

end InfoGeometry.Canonical.NonAbelianFusionTensorUHFTopologicalFlowBridge
