import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace InfoGeometry.Canonical.SourceSinkCrossRatio

noncomputable section

/-! The algebraic source--sink coordinate used by the Apollonius/Para-Kähler layer. -/

def coordinate (s : ℂ) : ℂ := s / (1 - s)

theorem coordinate_source : coordinate 0 = 0 := by
  simp [coordinate]

theorem coordinate_midpoint : coordinate (1 / 2 : ℂ) = 1 := by
  norm_num [coordinate]

theorem coordinate_sink : coordinate 1 = 0 := by
  simp [coordinate]

theorem coordinate_swap (s : ℂ) :
    coordinate (1 - s) = (coordinate s)⁻¹ := by
  unfold coordinate
  by_cases hs : s = 0
  · simp [hs]
  field_simp [hs]
  ring

theorem coordinate_swap_swap (s : ℂ) :
    coordinate (1 - (1 - s)) = coordinate s := by
  ring_nf

theorem coordinate_midline_normSq (y : ℝ) :
    Complex.normSq (coordinate ((1 / 2 : ℝ) + y * Complex.I)) = 1 := by
  unfold coordinate
  rw [Complex.normSq_div]
  have hnum : Complex.normSq ((1 / 2 : ℝ) + y * Complex.I) =
      (1 / 2 : ℝ) ^ 2 + y ^ 2 := by
    simpa using Complex.normSq_add_mul_I (1 / 2 : ℝ) y
  have hden : Complex.normSq (1 - ((1 / 2 : ℝ) + y * Complex.I)) =
      (1 / 2 : ℝ) ^ 2 + y ^ 2 := by
    rw [show (1 : ℂ) - ((1 / 2 : ℝ) + y * Complex.I) =
        (1 / 2 : ℝ) + (-y) * Complex.I by
          apply Complex.ext <;> norm_num]
    simpa [sq] using Complex.normSq_add_mul_I (1 / 2 : ℝ) (-y)
  rw [hnum, hden]
  have hpos : 0 < (1 / 2 : ℝ) ^ 2 + y ^ 2 := by positivity
  exact div_self (ne_of_gt hpos)

theorem coordinate_normSq_eq_ratio (s : ℂ) :
    Complex.normSq (coordinate s) =
      Complex.normSq s / Complex.normSq (1 - s) := by
  unfold coordinate
  rw [Complex.normSq_div]

end
end InfoGeometry.Canonical.SourceSinkCrossRatio
