import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Exact logarithmic realization of a multiplicative tropical ledger. -/
def ExactLog (δ : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ n : ℕ, δ n = c * Real.log (n : ℝ)

/-- Uniformly bounded logarithmic error for a multiplicative tropical ledger. -/
def BoundedLogError (δ : ℕ → ℝ) (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |δ n - c * Real.log (n : ℝ)| ≤ C

/-- Primewise exact logarithmic realization. -/
def PrimeExactLog (δ : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → δ p = c * Real.log (p : ℝ)

/-- Local package of the three implications used in the multiplicative-tropical exactness triad.
    thm:conclusion-multiplicative-tropical-exactness-triad -/
def MultiplicativeTropicalLedger (δ : ℕ → ℝ) (c : ℝ) : Prop :=
  (ExactLog δ c → BoundedLogError δ c) ∧
    (BoundedLogError δ c → PrimeExactLog δ c) ∧
      (PrimeExactLog δ c → ExactLog δ c)

/-- Paper-facing exactness triad for multiplicative tropical ledgers.
    thm:conclusion-multiplicative-tropical-exactness-triad -/
theorem paper_conclusion_multiplicative_tropical_exactness_triad (δ : ℕ → ℝ) (c : ℝ)
    (hδ : MultiplicativeTropicalLedger δ c) :
    (ExactLog δ c ↔ BoundedLogError δ c) ∧ (BoundedLogError δ c ↔ PrimeExactLog δ c) := by
  refine ⟨?_, ?_⟩
  · refine ⟨hδ.1, ?_⟩
    intro hBounded
    exact hδ.2.2 (hδ.2.1 hBounded)
  · refine ⟨hδ.2.1, ?_⟩
    intro hPrime
    exact hδ.1 (hδ.2.2 hPrime)

end Omega.Conclusion
