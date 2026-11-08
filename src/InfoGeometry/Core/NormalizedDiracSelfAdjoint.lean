/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DiracPeirceSuperalgebra

namespace InfoGeometry.Core.NormalizedDiracSelfAdjoint
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracPeirceSuperalgebra

variable {R : Type*} [Ring R] [StarRing R] {a m : R}

/-- The normalized MP sum is metric self-adjoint exactly when inverse and adjoint agree. -/
theorem normalizedDirac_isSelfAdjoint_iff (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) : IsSelfAdjoint (normalizedDirac a m) ↔ m = star a := by
  constructor
  · intro hQ
    have hp : star (exactSupport a m) = exactSupport a m := h.ab_adj_eq
    have hs := congrArg star (exactSupport_mul_normalizedDirac h ha)
    rw [star_mul, hQ, hp, normalizedDirac_mul_exactSupport h ha] at hs
    exact hs
  · rintro rfl
    change star (a + star a) = a + star a
    simp [add_comm]

/-- This criterion also states precisely when the normalized and metric Dirac sums coincide. -/
theorem normalizedDirac_eq_metric_iff (a m : R) :
    normalizedDirac a m = a + star a ↔ m = star a := by
  exact add_left_cancel_iff

end InfoGeometry.Core.NormalizedDiracSelfAdjoint
