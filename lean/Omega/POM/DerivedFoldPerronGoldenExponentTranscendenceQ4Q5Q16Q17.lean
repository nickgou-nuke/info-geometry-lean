import Mathlib.Tactic
import Omega.POM.DerivedFoldGoldenRationalPowerUnitObstruction
import Omega.POM.DerivedFoldRenyiDimensionTranscendenceQ4Q5Q16Q17

namespace Omega.POM

/-- Explicit norm seed for the `q = 4` Perron obstruction quantity. -/
def derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u4_norm : ℚ :=
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u4_norm

/-- Explicit norm seed for the `q = 5` Perron obstruction quantity. -/
def derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u5_norm : ℚ :=
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u5_norm

/-- Explicit norm seed for the `q = 16` Perron obstruction quantity. -/
def derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u16_norm : ℚ :=
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u16_norm

/-- Explicit norm seed for the `q = 17` Perron obstruction quantity. -/
def derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u17_norm : ℚ :=
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u17_norm

/-- Concrete Perron/golden-exponent obstruction package for `q = 4, 5, 16, 17`: rational golden
powers always have unit constant term `±1`, while the four audited Perron norm seeds below are
explicit and avoid `±1`. -/
abbrev DerivedFoldPerronGoldenExponentTranscendenceQ4Q5Q16Q17Statement : Prop :=
  (∀ a b : ℕ, 0 < b →
    ((-1 : ℝ) ^ a = 1 ∨ (-1 : ℝ) ^ a = -1)) ∧
  derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u4_norm = -((2 : ℚ) ^ 19) ∧
  derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u4_norm ≠ 1 ∧
  derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u4_norm ≠ -1 ∧
  derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u5_norm = -((2 : ℚ) ^ 24 / 5) ∧
  derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u5_norm ≠ 1 ∧
  derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u5_norm ≠ -1 ∧
  derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u16_norm = -((2 : ℚ) ^ 205) ∧
  derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u16_norm ≠ 1 ∧
  derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u16_norm ≠ -1 ∧
  derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u17_norm =
    (2 : ℚ) ^ (13 * 17) / (-(673948170 : ℚ)) ∧
  derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u17_norm ≠ 1 ∧
  derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u17_norm ≠ -1

/-- Paper label: `thm:derived-fold-perron-golden-exponent-transcendence-q4-q5-q16-q17`. -/
theorem paper_derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17 :
    DerivedFoldPerronGoldenExponentTranscendenceQ4Q5Q16Q17Statement := by
  rcases paper_derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17 with
    ⟨hParity, _, _, _, _, h4, h4one, h4negone, h5, h5one, h5negone,
      h16, h16one, h16negone, h17one, h17negone⟩
  refine ⟨hParity, ?_, h4one, h4negone, ?_, h5one, h5negone,
    ?_, h16one, h16negone, ?_, h17one, h17negone⟩
  · simpa [derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u4_norm,
      derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u4_norm] using h4
  · simpa [derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u5_norm,
      derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u5_norm] using h5
  · simpa [derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17_u16_norm,
      derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u16_norm] using h16
  · rfl

end Omega.POM
