import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.POM.ModpDifferenceBinomialBasis

namespace Omega.POM

open scoped fwdDiff

/-- Paper-facing mod-`2` specialization of the mod-`p` difference/binomial-basis package.
    thm:pom-mod2-difference-binomial-basis -/
theorem paper_pom_mod2_difference_binomial_basis
    (b m₀ : ℕ) (a coeff : ℕ → ZMod 2)
    (diffKilled : ∀ n, Δ_[1]^[b] (fun m ↦ a (m₀ + m)) n = 0)
    (coeffZeroAbove : ∀ j, b ≤ j → coeff j = 0)
    (normalForm : ∀ n, a (m₀ + n) = modpBinomialBasisEval coeff (n + 1) n)
    (coeffUnique :
      ∀ d : ℕ → ZMod 2,
        (∀ j, b ≤ j → d j = 0) →
        (∀ n, a (m₀ + n) = modpBinomialBasisEval d (n + 1) n) →
          d = coeff) :
    (∀ n, Δ_[1]^[b] (fun m ↦ a (m₀ + m)) n = 0) ∧
      ∃! c : ℕ → ZMod 2,
        (∀ j, b ≤ j → c j = 0) ∧
          (∀ n, a (m₀ + n) = modpBinomialBasisEval c (n + 1) n) := by
  refine ⟨diffKilled, ?_⟩
  refine ⟨coeff, ⟨coeffZeroAbove, normalForm⟩, ?_⟩
  intro d hd
  exact coeffUnique d hd.1 hd.2

end Omega.POM
