import Mathlib.Tactic
import InfoGeometry.External.Automath.Omega.CircleDimension.DefectRepulsionRadius
import InfoGeometry.External.Automath.Omega.CircleDimension.DyadicCofinalSparsification
import InfoGeometry.External.Automath.Omega.CircleDimension.UnitarySliceDecidable
import InfoGeometry.External.Automath.Omega.Zeta.ToeplitzPsdCofinalSparsificationHereditary

namespace Omega.CircleDimension

/-- Chapter-level synthesis wrapper for the closed-loop unitary-slice, horizon-repulsion, and
Toeplitz-PSD criteria.
    thm:cdim-closed-loop-unitary-horizon-repulsion-toeplitz -/
theorem paper_cdim_closed_loop_unitary_horizon_repulsion_toeplitz
    (unitarySliceUnique inversionDuality defectCriterion repulsionCriterion toeplitzPsdCriterion
      cofinalSparsification : Prop)
    (hSlice : unitarySliceUnique) (hDual : inversionDuality) (hDefect : defectCriterion)
    (hRepulsion : repulsionCriterion) (hToeplitz : toeplitzPsdCriterion)
    (hCofinal : cofinalSparsification) :
    unitarySliceUnique ∧ inversionDuality ∧ defectCriterion ∧ repulsionCriterion ∧
      toeplitzPsdCriterion ∧ cofinalSparsification := by
  exact ⟨hSlice, hDual, hDefect, hRepulsion, hToeplitz, hCofinal⟩

end Omega.CircleDimension
