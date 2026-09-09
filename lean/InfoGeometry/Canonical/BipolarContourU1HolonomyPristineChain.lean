import InfoGeometry.Canonical.BipolarU1PeriodHolonomy
import InfoGeometry.Canonical.BipolarContourSpinHolonomy

/-! Compact capstone for the analytic contour-to-U(1) and spin readouts. -/
noncomputable section
namespace InfoGeometry.Canonical.BipolarContourU1HolonomyPristineChain
open InfoGeometry.Canonical.BipolarU1PeriodHolonomy
open InfoGeometry.Canonical.BipolarContourSpinHolonomy
open InfoGeometry.Analysis.BipolarElementaryContourPeriods
open InfoGeometry.Analysis.BipolarWindingPeriodLattice

theorem pristine_scalar_u1_holonomy_core {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (α : ℝ) :
    contourU1Holonomy α 0 r = u1Holonomy α originWinding ∧
    contourU1Holonomy α 1 r = u1Holonomy α oneWinding := by
  exact ⟨contourU1Holonomy_origin (α := α) hr0 hr1,
    contourU1Holonomy_one (α := α) hr0 hr1⟩

theorem pristine_unit_half_spin_distinction {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    contourSpinHolonomy 0 r =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  contourSpinHolonomy_origin hr0 hr1

end InfoGeometry.Canonical.BipolarContourU1HolonomyPristineChain
