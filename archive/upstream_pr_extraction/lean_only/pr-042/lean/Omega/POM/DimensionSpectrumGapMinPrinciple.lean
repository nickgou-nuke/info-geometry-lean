import Mathlib.Tactic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.POM

/-- The Rényi dimension spectrum formula at golden geometric scale. -/
def dimensionSpectrumFormula
    (q dimension renyiEntropyGap : ℝ) : Prop :=
  dimension = renyiEntropyGap / ((q - 1) * Real.log Real.goldenRatio)

/-- The entropy gap as the relevant infimum. -/
def renyiEntropyGapInfFormula (renyiEntropyGap entropyGapInfimum : ℝ) : Prop :=
  renyiEntropyGap = entropyGapInfimum

/-- The minimum principle after substituting the entropy-gap infimum into the dimension formula. -/
def dimensionGapMinPrinciple
    (q dimension entropyGapInfimum : ℝ) : Prop :=
  dimension = (((q - 1) * Real.log Real.goldenRatio)⁻¹ * entropyGapInfimum)

/-- Paper label: `cor:pom-dimension-spectrum-gap-min-principle`. -/
theorem paper_pom_dimension_spectrum_gap_min_principle
    (q dimension renyiEntropyGap entropyGapInfimum : ℝ)
    (dimension_spectrum_formula_h :
      dimension = renyiEntropyGap / ((q - 1) * Real.log Real.goldenRatio))
    (renyi_entropy_gap_inf_formula_h : renyiEntropyGap = entropyGapInfimum) :
    dimensionSpectrumFormula q dimension renyiEntropyGap ∧
      renyiEntropyGapInfFormula renyiEntropyGap entropyGapInfimum ∧
        dimensionGapMinPrinciple q dimension entropyGapInfimum := by
  refine ⟨dimension_spectrum_formula_h, renyi_entropy_gap_inf_formula_h, ?_⟩
  calc
    dimension = renyiEntropyGap / ((q - 1) * Real.log Real.goldenRatio) :=
      dimension_spectrum_formula_h
    _ = (((q - 1) * Real.log Real.goldenRatio)⁻¹ * renyiEntropyGap) := by
      rw [div_eq_mul_inv, mul_comm]
    _ = (((q - 1) * Real.log Real.goldenRatio)⁻¹ * entropyGapInfimum) := by
      rw [renyi_entropy_gap_inf_formula_h]

end Omega.POM
