/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.BeliefDynamics

namespace InfoGeometry.Canonical.ChiralTorsionBridge

open InfoGeometry.Convex
open InfoGeometry.Canonical.BeliefDynamics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Logarithmic form of the Bregman exponential weight. -/
theorem bregmanWeight_log_eq_neg_divergence
    (H : HessianGeometry E) (x y : E) :
    Real.log (bregmanWeight H x y) = -H.divergence x y := by
  simp [bregmanWeight]

end InfoGeometry.Canonical.ChiralTorsionBridge
