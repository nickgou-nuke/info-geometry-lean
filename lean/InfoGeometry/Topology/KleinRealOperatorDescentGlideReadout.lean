/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinRealOperatorDescent
import InfoGeometry.Krein.DoubledSpace

/-!
# Real doubled-Krein readout of the Klein glide

This file proves only finite real-linear laws.  The source carrier is the
real function module on the Brillouin torus, its action is the existing glide
pullback, and the target is the native `DoubledSpace ℝ` with its native
`modular_j`.  No quotient or topological equivalence is asserted.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinRealOperatorDescent

open KleinBrillouinBase
open InfoGeometry.Krein

/-- Evaluation at a base point and its glide image, as a native real-linear
map into the canonical doubled real carrier. -/
def glideEvaluationReadout (k0 : BrillouinTorus) :
    (BrillouinTorus → ℝ) →ₗ[ℝ] DoubledSpace ℝ where
  toFun field :=
    to_doubled (field k0) (field (torusGlide k0))
  map_add' field₁ field₂ := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  map_smul' scalar field := by
    apply DoubledSpace.ext <;> simp [to_doubled]

/-- The existing glide pullback is an involution on the real function module. -/
theorem glidePullback_sq :
    glidePullback (V := ℝ) * glidePullback (V := ℝ) =
      LinearMap.id := by
  apply LinearMap.ext
  intro field
  funext point
  change field (torusGlide (torusGlide point)) = field point
  rw [torusGlide_involutive]

/-- The evaluation readout intertwines the existing glide pullback with the
native modular sheet swap, at every chosen base point. -/
theorem glideEvaluationReadout_glidePullback_eq_modular_j_comp
    (k0 : BrillouinTorus) :
    (glideEvaluationReadout k0).comp (glidePullback (V := ℝ)) =
      (modular_j (E := ℝ)).toLinearMap.comp
        (glideEvaluationReadout k0) := by
  apply LinearMap.ext
  intro field
  apply DoubledSpace.ext
  · simp [glideEvaluationReadout, glidePullback, to_doubled]
  · change field (torusGlide (torusGlide k0)) = field k0
    rw [torusGlide_involutive]

end InfoGeometry.Topology.KleinRealOperatorDescent

#print axioms InfoGeometry.Topology.KleinRealOperatorDescent.glidePullback_sq
#print axioms InfoGeometry.Topology.KleinRealOperatorDescent.glideEvaluationReadout_glidePullback_eq_modular_j_comp
