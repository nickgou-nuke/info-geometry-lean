import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

namespace CKWMonogamy

/-- Residual 3-Tangle τ₃ = C_{A(BC)}² - C_{AB}² - C_{AC}². -/
def residualThreeTangle (C_ABC C_AB C_AC : ℝ) : ℝ :=
  C_ABC ^ 2 - C_AB ^ 2 - C_AC ^ 2

/-- **Theorem**: CKW Monogamy Inequality ⟹ Non-Negativity of 3-Tangle τ₃ ≥ 0. -/
theorem ckw_monogamy_three_tangle_nonneg (C_ABC C_AB C_AC : ℝ)
    (h_ckw : C_AB ^ 2 + C_AC ^ 2 ≤ C_ABC ^ 2) :
    0 ≤ residualThreeTangle C_ABC C_AB C_AC := by
  dsimp [residualThreeTangle]
  linarith

/-- **Theorem**: Monogamy Exclusion Principle: If qubit A is maximally entangled with B (C_AB = 1, C_ABC = 1),
    it cannot share any entanglement with C (C_AC = 0). -/
theorem monogamy_exclusion_principle (C_AB C_AC : ℝ)
    (h_max : C_AB = 1)
    (h_AC_nonneg : 0 ≤ C_AC)
    (h_ckw : C_AB ^ 2 + C_AC ^ 2 ≤ 1 ^ 2) :
    C_AC = 0 := by
  have h_sq : C_AC ^ 2 ≤ 0 := by
    rw [h_max] at h_ckw
    linarith
  have h_sq_nonneg : 0 ≤ C_AC ^ 2 := sq_nonneg C_AC
  have h_sq_zero : C_AC ^ 2 = 0 := by linarith
  exact sq_eq_zero_iff.mp h_sq_zero

end CKWMonogamy
