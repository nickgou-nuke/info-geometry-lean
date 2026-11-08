/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Geometry.ProjectiveHessianMetriplecticBridge

namespace InfoGeometry.Geometry.ProjectiveHessianMetriplecticBridge

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The compatible metric is invariant under the complex structure. -/
theorem metric_J_invariant (triple : KahlerCompatibleTriple V) (u v : V) :
    triple.g (triple.J u) (triple.J v) = triple.g u v := by
  have hJ : triple.J (-triple.J v) = v := by
    rw [map_neg, triple.J_sq, neg_neg]
  have hω : triple.omega (triple.J u) v = -triple.omega u (triple.J v) := by
    have h := omega_J_invariant triple u (-triple.J v)
    rw [hJ, map_neg] at h
    exact h
  rw [triple.compatibility (triple.J u) (triple.J v)]
  rw [triple.J_sq, map_neg, hω, neg_neg]
  exact (triple.compatibility u v).symm

end InfoGeometry.Geometry.ProjectiveHessianMetriplecticBridge
