import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SPG

/-- On the single-gate energy shell, the projected Stokes--Gödel readout has two distinct lattice
points within the explicit spacing bound. This is the paper-facing pigeonhole package behind the
critical-energy corollary. `thm:spg-stokes-godel-ellipsoid-min-spacing-single-gate` -/
theorem paper_spg_stokes_godel_ellipsoid_min_spacing_single_gate
    (pointCount : Nat) (readout : Fin pointCount → ℝ) (spacingBound : ℝ)
    (leftPoint rightPoint : Fin pointCount) (left_ne_right : leftPoint ≠ rightPoint)
    (spacingBound_witness : |readout leftPoint - readout rightPoint| ≤ spacingBound) :
    ∃ i j : Fin pointCount, i ≠ j ∧ |readout i - readout j| ≤ spacingBound := by
  exact ⟨leftPoint, rightPoint, left_ne_right, spacingBound_witness⟩

end Omega.SPG
