import InfoGeometry.Canonical.RelativePotentialScalarBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Volume.LogPotential

/-!
# Log-potential calibration laws

These theorems connect the existing negative relative-log potential with the
existing additive determinant-volume potential.  The connection is stated as
a calibration equality, because the repository deliberately keeps statistical
Massieu and determinant-volume carriers distinct until such an equality is
proved for a concrete model.
-/

namespace InfoGeometry.Canonical.LogPotentialDeterminantCalibration

open InfoGeometry.Canonical.RelativePotentialScalarBridge
open LogPotential

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A calibrated determinant readout is exactly the negative relative-log
potential of the corresponding positive scalar ratio. -/
theorem scalarModularPotential_eq_neg_LogAbsVolume
    (r : ℝ) (hr : 0 < r)
    (g : V ≃ₗ[ℝ] V)
    (hcal : LogAbsVolume g = Real.log r) :
    scalarModularPotential r hr = -LogAbsVolume g := by
  rw [scalarModularPotential_eq_neg_log, hcal]

/-- The Weyl gauge shift of the calibrated potential is the corresponding
additive shift of the determinant log-volume readout. -/
theorem scalarModularPotential_weylRescale_eq_neg_LogAbsVolume
    (c r : ℝ) (hc : 0 < c) (hr : 0 < r)
    (gc : V ≃ₗ[ℝ] V)
    (hweyl : LogAbsVolume gc = Real.log c) :
    scalarModularPotential (c * r) (mul_pos hc hr) =
      scalarModularPotential r hr - LogAbsVolume gc := by
  rw [scalarModularPotential_weylRescale_eq_sub_log c r hc hr,
    hweyl]

end InfoGeometry.Canonical.LogPotentialDeterminantCalibration
