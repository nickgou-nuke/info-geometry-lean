import InfoGeometry.Quantum.YSystemIntegrability

namespace InfoGeometry.Canonical.YSystemIntegrabilityCapstone

open InfoGeometry.Quantum.YSystemIntegrability

theorem capstone_y_system_integrability_synthesis (ε φ : ℝ) (Y : ℝ) :
    (0 < yFunctionOfEnergy ε) ∧
    (1 < 1 + yFunctionOfEnergy ε) ∧
    (ySystemRhsA1 Y = 1) ∧
    (incMatrixA2 0 1 = 1 ∧ incMatrixA2 1 0 = 1) ∧
    ((Complex.exp (-Complex.I * (φ : ℂ))) * (Complex.exp (Complex.I * (φ : ℂ))) = 1) ∧
    (zamolodchikovPeriodUnitsA1 = 4) :=
  grand_y_system_integrability_synthesis ε φ Y

end InfoGeometry.Canonical.YSystemIntegrabilityCapstone
