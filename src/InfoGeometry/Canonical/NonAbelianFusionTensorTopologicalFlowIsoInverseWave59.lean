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

theorem nonAbelianFusionTensorTopologicalFlowIso_comp_inverse (t : ℝ) :
    flowColimitIso D t ≪≫ flowColimitIso D (-t) =
      Iso.refl (topologicalDirectColimit
        (fusionTensorTopologicalDiagram (K := ℂ))) := by
  apply CategoryTheory.Iso.ext
  exact flowColimitMap_right_inverse D t

end InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalFlow
