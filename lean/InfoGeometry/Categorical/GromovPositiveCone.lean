import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite Gromov positive-cone normalization atoms

This module states the relevant finite real-algebra facts directly with
mathlib's canonical multiplication, division, negation, and polynomial
normalization.  It introduces no local wrappers for weights, normalization maps,
or toy entropy functionals.

No positivity theorem, entropy limit, Stirling asymptotic, maximum-entropy
principle, or analytic completion is asserted.
-/

set_option autoImplicit false

namespace InfoGeometry.Categorical.Gromov

/-- Scale invariance of a secondary normalized real ratio. -/
theorem normalization_scale_invariance
    (w total scale : ℝ) (h_total : total ≠ 0) (h_scale : scale ≠ 0) :
    (w * scale) / (total * scale) = w / total := by
  field_simp [h_total, h_scale]

/-- Exact polynomial expansion of the unnormalized quadratic core. -/
theorem unnormalized_entropy_expansion (x y : ℝ) :
    -((x + y) * (x + y)) = -(x * x) + -(y * y) - 2 * x * y := by
  ring

end InfoGeometry.Categorical.Gromov
