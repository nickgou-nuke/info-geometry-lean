import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-localized-finite-ledger-prime-window-truncation`. -/
theorem paper_conclusion_localized_finite_ledger_prime_window_truncation
    (primeWindow : Finset ℕ) (relationCoeffs : ℕ → ℤ)
    (leftWitness rightWitness : ℚ) (torsionExponent : ℕ)
    (coeffs_supported : ∀ n, n ∉ primeWindow → relationCoeffs n = 0)
    (witnessCollision : leftWitness ^ torsionExponent = rightWitness ^ torsionExponent) :
    ∃ P0 : Finset ℕ, ∃ coeffs : ℕ → ℤ,
      (P0 = primeWindow ∧ coeffs = relationCoeffs ∧
        (∀ n, n ∉ P0 → coeffs n = 0)) ∧
      ∃ u v : ℚ, ∃ N : ℕ,
        P0 = primeWindow ∧ coeffs = relationCoeffs ∧ u = leftWitness ∧
          v = rightWitness ∧ N = torsionExponent ∧ u ^ N = v ^ N := by
  refine ⟨primeWindow, relationCoeffs, ?_, ?_⟩
  · refine ⟨rfl, rfl, ?_⟩
    intro n hn
    exact coeffs_supported n hn
  · refine ⟨leftWitness, rightWitness, torsionExponent, rfl, rfl, rfl, rfl, rfl, ?_⟩
    exact witnessCollision

end Omega.Conclusion
