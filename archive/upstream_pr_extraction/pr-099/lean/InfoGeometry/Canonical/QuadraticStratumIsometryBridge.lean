import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import InfoGeometry.Topology.SpinorOrbitStratum

/-!
# Quadratic strata under quadratic isometries

`OrbitStratum` is the zero/null/generic trichotomy, not an orbit
classification.  This file supplies its generic transport theorem for a
quadratic-form isometry, without introducing any group-action claim.
-/

namespace InfoGeometry.Canonical.QuadraticStratumIsometryBridge

open InfoGeometry.Topology.SpinorOrbitStratum

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

theorem isometryEquiv_preserves_stratum
    {Q : QuadraticForm R M} (e : Q.IsometryEquiv Q) {x : M} :
    OrbitStratum Q x → OrbitStratum Q (e x) := by
  apply map_stratum_of_preserves
  refine ⟨map_zero e, ?_, ?_⟩
  · intro y hy
    exact e.injective (by simpa using hy)
  · intro y
    exact e.map_app y

theorem isometryEquiv_preserves_stratum_iff
    {Q : QuadraticForm R M} (e : Q.IsometryEquiv Q) (x : M) :
    OrbitStratum Q (e x) ↔ OrbitStratum Q x := by
  constructor
  · intro h
    have h' := isometryEquiv_preserves_stratum e.symm h
    have hx : e.symm (e x) = x := e.toLinearEquiv.symm_apply_apply x
    rw [hx] at h'
    exact h'
  · exact isometryEquiv_preserves_stratum e

end InfoGeometry.Canonical.QuadraticStratumIsometryBridge
