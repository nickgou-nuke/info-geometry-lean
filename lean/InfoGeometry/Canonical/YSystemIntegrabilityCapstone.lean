import InfoGeometry.Quantum.YSystemIntegrability
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.YSystemIntegrabilityCapstone

open InfoGeometry.Quantum.YSystemIntegrability

theorem capstone_y_system_integrability_synthesis (ε φ : ℝ) (Y : ℝ) :
    (0 < yFunctionOfEnergy ε) ∧
    (1 < 1 + yFunctionOfEnergy ε) ∧
    (ySystemRhsA1 Y = 1) ∧
    (incMatrixA2 0 1 = 1 ∧ incMatrixA2 1 0 = 1) ∧
    ((Complex.exp (-Complex.I * (φ : ℂ))) *
      (Complex.exp (Complex.I * (φ : ℂ))) = 1) ∧
    (zamolodchikovPeriodUnitsA1 = 4) := by
  exact ⟨y_function_pos ε,
    y_system_term_gt_one ε,
    y_system_a1_rhs_eq_one Y,
    inc_matrix_a2_symmetric,
    y_system_a1_phase_product φ,
    zamolodchikov_period_a1_eval⟩

end InfoGeometry.Canonical.YSystemIntegrabilityCapstone
