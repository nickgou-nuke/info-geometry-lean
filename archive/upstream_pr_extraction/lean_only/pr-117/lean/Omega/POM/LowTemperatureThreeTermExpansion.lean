import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

def pomLeadingPressureExpansion
    (aStar rhoStar : ℝ) (q0 : ℕ) (pressure remainder : ℕ → ℝ) : Prop :=
  ∀ q, q0 ≤ q →
    pressure q = (q : ℝ) * Real.log aStar + Real.log rhoStar + remainder q

def pomExponentialErrorBound
    (aStar rhoStar gap errorConstant : ℝ) (q0 : ℕ)
    (pressure : ℕ → ℝ) : Prop :=
  ∀ q, q0 ≤ q →
    0 ≤
        pressure q - ((q : ℝ) * Real.log aStar + Real.log rhoStar) ∧
      pressure q - ((q : ℝ) * Real.log aStar + Real.log rhoStar) ≤
        errorConstant * Real.exp (-(q : ℝ) * gap)

/-- `thm:pom-low-temperature-three-term-expansion` -/
theorem paper_pom_low_temperature_three_term_expansion
    (aStar rhoStar gap errorConstant : ℝ) (q0 : ℕ)
    (pressure remainder : ℕ → ℝ)
    (hExpansion :
      ∀ q, q0 ≤ q →
        pressure q = (q : ℝ) * Real.log aStar + Real.log rhoStar + remainder q)
    (hRemainderNonneg : ∀ q, q0 ≤ q → 0 ≤ remainder q)
    (hRemainderBound :
      ∀ q, q0 ≤ q → remainder q ≤ errorConstant * Real.exp (-(q : ℝ) * gap)) :
    pomLeadingPressureExpansion aStar rhoStar q0 pressure remainder ∧
      pomExponentialErrorBound aStar rhoStar gap errorConstant q0 pressure := by
  refine ⟨hExpansion, ?_⟩
  intro q hq
  have hExpansion_q := hExpansion q hq
  have hNonneg := hRemainderNonneg q hq
  have hBound := hRemainderBound q hq
  have hDiff :
      pressure q - ((q : ℝ) * Real.log aStar + Real.log rhoStar) = remainder q := by
    linarith [hExpansion_q]
  constructor
  · simpa [hDiff] using hNonneg
  · simpa [hDiff] using hBound

end Omega.POM
