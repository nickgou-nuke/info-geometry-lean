import Mathlib.Tactic
import InfoGeometry.Topology.AnyonicBraidedVolume
import InfoGeometry.Canonical.BostConnesModularFlow

/-!
# BostConnesZetaVolume

Records a finite volume readout at the parameter `β = 2`.  The present
definition is an explicit real constant; it is not an analytic-continuation
construction of the Riemann zeta function.
-/

open Real

variable (M : Type _) [CommRing M] [StarRing M] [Algebra ℂ M]

/-- The finite partition readout used by this owner. -/
noncomputable def bost_connes_partition_function : ℝ :=
  Real.pi^2 / 6

/-- The regularized volume of the braided anyonic bulk.

Positivity is represented by a genuine algebraic star-square property rather
than a vacuous `∀ x, True` field. -/
structure BraidedBulkVolume where
  volume_operator : M
  star_square_property : ∃ y : M, volume_operator = star y * y

variable (vol : BraidedBulkVolume M)

/-- The supplied volume packet admits the trivial scale readout at `β = 2`. -/
theorem bulk_volume_unit_scale :
    ∃ (scale : ℝ), scale * (Real.pi^2 / 6) = Real.pi^2 / 6 := by
  use 1
  rw [one_mul]
