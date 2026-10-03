import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Zeta.TorsionExactOrderLedgerSeeds

namespace Omega.Conclusion

open Omega.Zeta.TorsionExactOrderLedgerSeeds

/-- Concrete finite shadow model for the `{2,3}`-localized torsion quotient. -/
abbrev conclusion_finite_localized_shadow_exact_torsion_spectrum_shadow (n : ℕ) : Type :=
  ZMod (sCoprimePart23 n)

/-- Exact-order count in the `{2,3}`-localized shadow: outside the localized primes one recovers
`φ(n)`, while pure `{2,3}`-power torsion contributes nothing at positive order. -/
def conclusion_finite_localized_shadow_exact_torsion_spectrum_exactOrderCount (n : ℕ) : ℕ :=
  if sCoprimePart23 n = n then Nat.totient n else 0

private theorem sCoprime_8 : sCoprimePart23 8 = 1 := by
  have h2 : (8 : ℕ).factorization 2 = 3 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num,
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 2)]
    simp
  have h3 : (8 : ℕ).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 8)
  norm_num [sCoprimePart23, h2, h3]

private theorem sCoprime_25 : sCoprimePart23 25 = 25 := by
  have h2 : (25 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 25)
  have h3 : (25 : ℕ).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 25)
  norm_num [sCoprimePart23, h2, h3]

private theorem exactOrderCount_8 :
    conclusion_finite_localized_shadow_exact_torsion_spectrum_exactOrderCount (2 ^ 3) = 0 := by
  have hnot : sCoprimePart23 8 ≠ 8 := by
    rw [sCoprime_8]
    norm_num
  change (if sCoprimePart23 8 = 8 then Nat.totient 8 else 0) = 0
  rw [if_neg hnot]

private theorem exactOrderCount_25 :
    conclusion_finite_localized_shadow_exact_torsion_spectrum_exactOrderCount (5 ^ 2) = 20 := by
  have hstrip : sCoprimePart23 (5 ^ 2) = 5 ^ 2 := by
    simpa using sCoprime_25
  rw [conclusion_finite_localized_shadow_exact_torsion_spectrum_exactOrderCount, hstrip]
  rw [Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 2)]
  norm_num

/-- Paper label: `thm:conclusion-finite-localized-shadow-exact-torsion-spectrum`.
For the concrete finite localization `{2,3}`, the shadow at level `n` is modeled by the quotient
`ℤ / n^(T)ℤ`, so its cardinality is the `{2,3}`-coprime part `n^(T)`. In particular pure
`{2,3}`-power torsion collapses, while a prime power outside `{2,3}` survives unchanged and its
exact-order locus has size `φ(p^k)`. -/
theorem paper_conclusion_finite_localized_shadow_exact_torsion_spectrum :
    sCoprimePart23 12 = 1 ∧
      sCoprimePart23 30 = 5 ∧
      conclusion_finite_localized_shadow_exact_torsion_spectrum_shadow 12 = ZMod 1 ∧
      conclusion_finite_localized_shadow_exact_torsion_spectrum_shadow 30 = ZMod 5 ∧
      conclusion_finite_localized_shadow_exact_torsion_spectrum_exactOrderCount (2 ^ 3) = 0 ∧
      conclusion_finite_localized_shadow_exact_torsion_spectrum_exactOrderCount (5 ^ 2) = 20 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sCoprime_12
  · exact sCoprime_30
  · change ZMod (sCoprimePart23 12) = ZMod 1
    rw [sCoprime_12]
  · change ZMod (sCoprimePart23 30) = ZMod 5
    rw [sCoprime_30]
  · exact exactOrderCount_8
  · exact exactOrderCount_25

end Omega.Conclusion
