/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalFlow

noncomputable section

namespace InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalFlow

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalColimit
open FilteredColimit.Native.Topological

variable (D : TensorTopologicalFlowData)

theorem nonAbelianFusionTensorTopologicalFlowMap_comp_forward (s t : ℝ) :
    flowColimitMap D s ≫ flowColimitMap D t =
      flowColimitMap D (s + t) := by
  calc
    flowColimitMap D s ≫ flowColimitMap D t =
        flowColimitMap D (t + s) := by
      exact (flowColimitMap_add D t s).symm
    _ = flowColimitMap D (s + t) := by
      rw [add_comm]

end InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalFlow
