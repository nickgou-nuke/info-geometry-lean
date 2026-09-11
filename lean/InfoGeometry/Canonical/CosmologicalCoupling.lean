import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DrazinAnomaly
import InfoGeometry.Canonical.TransportObservable

/-!
# Coupling-parameter algebra

This file proves only elementary algebraic consequences of a supplied relation
`G = 4 * α / Z`.  It does not derive the fine-structure constant, a Majorana
conductance peak, vacuum impedance, a Drazin anomaly, or any cosmological
coupling theorem.
-/

namespace InfoGeometry.Canonical.CosmologicalCoupling

/--
If `R * G = 1` and `G = 4 * α / Z`, then `R * (4 * α) = Z`.
-/
theorem reciprocal_coupling_relation (R_M G_M alpha Z_0 : ℝ)
    (h_G : G_M = 4 * alpha / Z_0)
    (h_R : R_M * G_M = 1) :
    R_M * (4 * alpha) = Z_0 := by
  by_cases hZ : Z_0 = 0
  · subst Z_0
    simp [h_G] at h_R
  · have hmul := congrArg (fun x : ℝ => x * Z_0) h_R
    rw [h_G] at hmul
    field_simp [hZ] at hmul
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-!
No downstream physical interpretation is proved in this file.  Any use of the
parameters as conductance, impedance, or fine-structure constants must be
supplied by a separate owner theorem.
-/

end InfoGeometry.Canonical.CosmologicalCoupling
