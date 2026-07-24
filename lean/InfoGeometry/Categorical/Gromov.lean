import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Finite positive-cone normalization lemmas in a Gromov-style categorical namespace.
This is theorem-safe algebra on `ℝ`; it does not claim a historical thesis.
-/

set_option autoImplicit false

namespace InfoGeometry.Categorical.Gromov

/-- Primary unnormalized weight in the positive cone. -/
def unnormalized_weight (count : ℝ) (dimension : ℝ) : ℝ :=
  count * dimension

/-- Secondary projection to a normalized ratio. -/
noncomputable def normalize_projection (w total : ℝ) : ℝ :=
  w / total

/-- Unnormalized multiplicity/entropy readout. -/
def unnormalized_multiplicity_entropy (count : ℝ) : ℝ :=
  - (count * count)

/-- Scaling cancels in the normalized projection. -/
theorem normalization_scale_invariance (w total scale : ℝ)
    (h_total : total ≠ 0) (h_scale : scale ≠ 0) :
    normalize_projection (w * scale) (total * scale) = normalize_projection w total := by
  unfold normalize_projection
  field_simp [h_total, h_scale]

/-- Exact algebraic expansion of the unnormalized quadratic entropy. -/
theorem unnormalized_entropy_expansion (x y : ℝ) :
    unnormalized_multiplicity_entropy (x + y) =
      unnormalized_multiplicity_entropy x + unnormalized_multiplicity_entropy y - 2 * x * y := by
  unfold unnormalized_multiplicity_entropy
  ring

end InfoGeometry.Categorical.Gromov
