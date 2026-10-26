/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AlbertCayleyDickson
import Mathlib.Tactic

/-!
# Porter's division-free Riccati/Casimir square completion

Reuses the canonical SplitQuaternion Riccati and traceless flow definitions.
The completed-square identity is a polynomial identity; it does not assert
the existence of a Riccati solution or analytic flow.
-/

namespace InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion

variable {F : Type*} [CommRing F] [StarRing F]

theorem porterRiccati_traceless_square_completion
    (α β γ x : F) :
    (α - (β - γ) * x) ^ 2 +
        (β - γ) * porterRiccati (tracelessFlowGen α β γ) x =
      α ^ 2 + β ^ 2 - γ ^ 2 := by
  have h :=
    (porterRiccati_tracelessFlowGen_and_casimir_discriminant
      α β γ 0 0 x).1
  rw [h]
  ring

end InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
