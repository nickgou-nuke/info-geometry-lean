/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.WeylEntropyShiftBridge

/-!
# Zero-scale obstruction for a globally positive homogeneous readout

The existing interface requires a positive readout at every carrier point,
but its homogeneous scale law includes the scale zero. At any explicit point
these two laws force the homogeneous weight to vanish. In particular the
interface cannot model a globally positive readout of positive weight.

This theorem diagnoses the declared interface without changing it. A positive
scale action or an explicit positivity domain is needed for a nonzero-weight
model. No choice of an element of the carrier is made here.
-/

namespace InfoGeometry.Canonical.WeylEntropyScaleObstruction

open WeylEntropyShiftBridge

variable {Op : Type*}

theorem weight_eq_zero_of_global_positivity
    (W : WeylHomogeneousEntropy Op) (x : Op) : W.homogeneous.weight = 0 := by
  by_contra hw
  have hscale := W.homogeneous.readout_scale 0 x
  rw [zero_pow hw, zero_mul] at hscale
  have hpos := W.readout_pos (W.homogeneous.scale 0 x)
  rw [hscale] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- The same interface therefore gives constant logarithmic readout under
every scale, including zero, whenever a carrier point is supplied. -/
theorem entropy_scale_eq_of_global_positivity
    (W : WeylHomogeneousEntropy Op) (x : Op) (c : ℝ) :
    W.entropy (W.homogeneous.scale c x) = W.entropy x := by
  unfold WeylHomogeneousEntropy.entropy
  rw [W.homogeneous.readout_scale, weight_eq_zero_of_global_positivity W x]
  simp

end InfoGeometry.Canonical.WeylEntropyScaleObstruction
