import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace InfoGeometry.Canonical

/-- Mellin kernel `ω^(Δ - 1)` on positive energy. -/
noncomputable def mellinKernel (omega delta : ℝ) : ℝ :=
  omega ^ (delta - 1)

/-- The unit-dimension Mellin kernel evaluates to `1`. -/
theorem mellinKernel_unit_dimension (omega : ℝ) :
    mellinKernel omega 1 = 1 := by
  simp [mellinKernel]

/-- The Mellin kernel is positive when the energy parameter is positive. -/
theorem mellinKernel_pos (omega delta : ℝ) (h_pos : 0 < omega) :
    0 < mellinKernel omega delta := by
  simpa [mellinKernel] using Real.rpow_pos_of_pos h_pos (delta - 1)

/-- A minimal positive-energy Mellin kernel packet. -/
theorem master_positive_energy_mellin_kernel_synthesis
    (omega : ℝ) (h_pos : 0 < omega) :
    mellinKernel omega 1 = 1 ∧ 0 < mellinKernel omega 2 := by
  constructor
  · exact mellinKernel_unit_dimension omega
  · exact mellinKernel_pos omega 2 h_pos

end InfoGeometry.Canonical
