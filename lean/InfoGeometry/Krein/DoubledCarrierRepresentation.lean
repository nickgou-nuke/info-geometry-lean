/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Clifford.Grading

namespace InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem doubledCarrier_projector_decomposition (u : DoubledSpace E) :
    (doubledCarrier (E := E)).Pplus u +
        (doubledCarrier (E := E)).Pminus u = u := by
  change spectralPlusProj (E := E) u + spectralMinusProj (E := E) u = u
  have h := congrArg
    (fun T : DoubledSpace E →L[ℝ] DoubledSpace E => T u)
    (spectralProj_sum (E := E))
  simpa only [add_apply, ContinuousLinearMap.id_apply] using h

end InfoGeometry.Krein
