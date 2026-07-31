import Omega.POM.DeltaqQuadraticObservableMaxExponent
import Mathlib.Tactic

namespace Omega.POM

/-- If the allowed budget dominates the quadratic exponent profile divided by the sample count,
the relative mean-square error stays below that budget. -/
def sampleComplexityThreshold
    (Λ r : ℝ) (sampleCount relativeMSE accuracy : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ m : ℕ,
    C * ((Λ ^ 2 / r) ^ m / sampleCount m) ≤ accuracy m →
      relativeMSE m ≤ accuracy m

/-- Paper label: `cor:pom-deltaq-sample-complexity-threshold`. The quadratic-observable exponent
bound controls the one-sample relative variance at scale `Λ² / r`; dividing by `N` via the
variance-of-the-sample-mean identity yields the required sample-complexity threshold. -/
theorem paper_pom_deltaq_sample_complexity_threshold
    (Λ r : ℝ) (Z1 Z2 Q sampleCount relativeMSE accuracy : ℕ → ℝ)
    (hΛ : 0 ≤ Λ) (hr : 0 < r)
    (hsampleCount_pos : ∀ m : ℕ, 0 < sampleCount m)
    (hZ1 : ∃ C > 0, ∀ m : ℕ, |Z1 m| ≤ C * Λ ^ m)
    (hZ2 : ∃ C > 0, ∀ m : ℕ, |Z2 m| ≤ C * Λ ^ m)
    (hQ : ∀ m : ℕ, Q m = Z1 m * Z2 m)
    (hrelativeMSE :
      ∀ m : ℕ, relativeMSE m = (|Q m| / r ^ m) / sampleCount m) :
    sampleComplexityThreshold Λ r sampleCount relativeMSE accuracy := by
  rcases pom_deltaq_quadratic_observable_max_exponent_nonneg Λ r Z1 Z2 Q hΛ
      (le_of_lt hr) hZ1 hZ2 hQ with
    ⟨C, hCpos, hGrowth⟩
  refine ⟨C, hCpos, ?_⟩
  intro m hThreshold
  have hBound :
      relativeMSE m ≤ C * ((Λ ^ 2 / r) ^ m / sampleCount m) := by
    rw [hrelativeMSE m]
    calc
      (|Q m| / r ^ m) / sampleCount m ≤
          (C * (Λ ^ 2 / r) ^ m) / sampleCount m := by
        exact div_le_div_of_nonneg_right (hGrowth m) (le_of_lt (hsampleCount_pos m))
      _ = C * ((Λ ^ 2 / r) ^ m / sampleCount m) := by ring
  exact le_trans hBound hThreshold

end Omega.POM
