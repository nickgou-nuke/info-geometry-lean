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

theorem nonAbelianFusionTensorTopologicalFlowMap_isIso (t : ℝ) :
    IsIso (flowColimitMap D t) := by
  exact (flowColimitIso D t).isIso_hom

end InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalFlow
