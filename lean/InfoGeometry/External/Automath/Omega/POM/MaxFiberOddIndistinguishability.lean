import Mathlib.Tactic
import InfoGeometry.External.Automath.Omega.POM.MaxFiberPhaseHiddenBitMi

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `prop:pom-max-fiber-odd-indistinguishability`. -/
theorem paper_pom_max_fiber_odd_indistinguishability (n : ℕ) (word : Fin n → Bool)
    (p₁ p₂ : ℝ) (hp₁ : p₁ = 1 / 2) (hp₂ : p₂ = 1 / 2) :
    (∏ i, if word i then p₁ else 1 - p₁) =
      (∏ i, if word i then p₂ else 1 - p₂) := by
  subst p₁
  subst p₂
  simp

end Omega.POM
