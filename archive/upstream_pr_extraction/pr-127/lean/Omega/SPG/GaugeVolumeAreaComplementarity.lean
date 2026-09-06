import Mathlib.Tactic

namespace Omega.SPG

/-- Gauge-volume density and area density satisfy the stated complementarity lower bound.
    thm:spg-gauge-volume-area-complementarity -/
theorem paper_spg_gauge_volume_area_complementarity
    (dimension : ℕ) (gaugeDensity areaDensity fiberEntropyGap : ℝ)
    (dimension_pos : 0 < dimension)
    (entropyIdentity :
      gaugeDensity = (dimension : ℝ) * Real.log 2 - fiberEntropyGap)
    (entropyGapBound :
      fiberEntropyGap ≤ (dimension : ℝ) * (Real.log 2 * areaDensity) + 1) :
    gaugeDensity / (dimension : ℝ) + Real.log 2 * areaDensity ≥
      Real.log 2 - 1 / (dimension : ℝ) := by
  have hdim_pos : 0 < (dimension : ℝ) := by
    exact_mod_cast dimension_pos
  have hdim_ne : (dimension : ℝ) ≠ 0 := by linarith
  have hmain :
      gaugeDensity / (dimension : ℝ) + Real.log 2 * areaDensity =
        Real.log 2 - fiberEntropyGap / (dimension : ℝ) + Real.log 2 * areaDensity := by
    rw [entropyIdentity]
    field_simp [hdim_ne]
  rw [hmain]
  have hscaled :
      fiberEntropyGap / (dimension : ℝ) ≤ Real.log 2 * areaDensity + 1 / (dimension : ℝ) :=
    by
      rw [_root_.div_le_iff₀ hdim_pos]
      simpa [add_mul, hdim_ne, mul_add, mul_assoc, mul_left_comm, mul_comm] using
        entropyGapBound
  linarith

end Omega.SPG
