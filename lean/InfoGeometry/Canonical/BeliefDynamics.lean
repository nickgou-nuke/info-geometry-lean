/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Convex.HessianGeometry
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Dual-coordinate shifts and Bregman weights

This module records only constructions supported by `HessianGeometry`: the
dual coordinate is its gradient, and exponentiating the negative Bregman
divergence gives a positive scalar weight. A measure, density, connection, or
parallel transport is not part of this interface.
-/

namespace InfoGeometry.Canonical.BeliefDynamics

open InfoGeometry.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Add a displacement in dual coordinates to the dual coordinate of `x₀`.
This returns a dual-coordinate vector; no inverse Legendre map is assumed. -/
noncomputable def dualCoordinateShift (H : HessianGeometry E) (x₀ η : E) : E :=
  H.dualMap x₀ + η

@[simp] theorem dualCoordinateShift_eq (H : HessianGeometry E) (x₀ η : E) :
    dualCoordinateShift H x₀ η = H.dualMap x₀ + η := rfl

/-- The positive exponential weight determined by the oriented Bregman
divergence. It is a scalar function, without an implicit measure claim. -/
noncomputable def bregmanWeight (H : HessianGeometry E) (x y : E) : ℝ :=
  Real.exp (-H.divergence x y)

theorem bregmanWeight_pos (H : HessianGeometry E) (x y : E) :
    0 < bregmanWeight H x y := by
  exact Real.exp_pos _

end InfoGeometry.Canonical.BeliefDynamics
