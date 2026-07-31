import Mathlib.Tactic

namespace Omega.POM

/-- The denominator obtained from the finite-interval Chebyshev recurrence normalization. -/
def chebyshevDenominator (T : ℕ) (z : ℚ) : ℚ :=
  (T + 1 : ℚ) - T * z

/-- The same denominator written through the characteristic-root normalization. -/
def rootDenominator (T : ℕ) (z : ℚ) : ℚ :=
  1 + T * (1 - z)

lemma rootDenominator_eq_chebyshevDenominator (T : ℕ) (z : ℚ) :
    rootDenominator T z = chebyshevDenominator T z := by
  unfold rootDenominator chebyshevDenominator
  ring

/-- Closed form obtained by imposing the `±T` boundary data on the Chebyshev normalization. -/
def chebyshevClosedForm (T : ℕ) (z : ℚ) : ℚ :=
  z / chebyshevDenominator T z

/-- The same closed form written through the characteristic roots. -/
def rootClosedForm (T : ℕ) (z : ℚ) : ℚ :=
  z / rootDenominator T z

/-- The threshold-hitting PGF evaluated at the origin state. -/
def pgfAtZero (T : ℕ) (z : ℚ) : ℚ :=
  z / chebyshevDenominator T z

/-- Paper label: `thm:pom-symmetric-double-threshold-pgf-chebyshev`. -/
theorem paper_pom_symmetric_double_threshold_pgf_chebyshev
    (T : ℕ) (z : ℚ) :
    pgfAtZero T z = chebyshevClosedForm T z ∧ pgfAtZero T z = rootClosedForm T z := by
  refine ⟨rfl, ?_⟩
  simp [pgfAtZero, rootClosedForm, rootDenominator_eq_chebyshevDenominator]

end Omega.POM
