import InfoGeometry.Arithmetic.AmariZetaDuallyFlatGeometry

noncomputable section

namespace InfoGeometry.Topology.MaassSuperconductingGap

open InfoGeometry.Arithmetic.AmariZeta

def criticalParameter (height : ℝ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * (height : ℂ)

theorem critical_parameter_value (height : ℝ) :
    fisherRaoMetric (criticalParameter height) =
      (((1 / 4 : ℝ) + height ^ 2 : ℝ) : ℂ) := by
  simpa [criticalParameter] using fisherRaoMetric_on_critical_line height

theorem critical_parameter_im (height : ℝ) :
    (fisherRaoMetric (criticalParameter height)).im = 0 := by
  rw [critical_parameter_value]
  exact Complex.ofReal_im _

theorem critical_parameter_re (height : ℝ) :
    (fisherRaoMetric (criticalParameter height)).re = 1 / 4 + height ^ 2 := by
  rw [critical_parameter_value]
  rfl

theorem critical_parameter_lower_bound (height : ℝ) :
    (1 / 4 : ℝ) ≤ (fisherRaoMetric (criticalParameter height)).re := by
  rw [critical_parameter_re]
  exact le_add_of_nonneg_right (sq_nonneg height)

theorem critical_parameter_positive (height : ℝ) :
    0 < (fisherRaoMetric (criticalParameter height)).re := by
  rw [critical_parameter_re]
  exact fisherRaoMetric_on_critical_line_pos height

theorem critical_parameter_minimum_iff (height : ℝ) :
    (fisherRaoMetric (criticalParameter height)).re = 1 / 4 ↔ height = 0 := by
  rw [critical_parameter_re]
  constructor
  · intro heq
    nlinarith [sq_nonneg height]
  · rintro rfl
    norm_num

theorem critical_parameter_strict_bound_iff (height : ℝ) :
    (1 / 4 : ℝ) < (fisherRaoMetric (criticalParameter height)).re ↔ height ≠ 0 := by
  rw [critical_parameter_re]
  constructor
  · intro hstrict hzero
    subst height
    norm_num at hstrict
  · intro hnonzero
    nlinarith [sq_pos_of_ne_zero hnonzero]

theorem off_line_parameter_below_quarter :
    (fisherRaoMetric (1 / 4 : ℂ)).im = 0 ∧
      (fisherRaoMetric (1 / 4 : ℂ)).re = 3 / 16 ∧
      (fisherRaoMetric (1 / 4 : ℂ)).re < 1 / 4 := by
  norm_num [fisherRaoMetric]

end InfoGeometry.Topology.MaassSuperconductingGap
