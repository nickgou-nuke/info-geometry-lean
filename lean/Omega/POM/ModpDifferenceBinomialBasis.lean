import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped fwdDiff

/-- Finite binomial-basis expansion used for the eventual tail normal form. -/
def modpBinomialBasisEval {p : ℕ} (c : ℕ → ZMod p) (r n : ℕ) : ZMod p :=
  Finset.sum (Finset.range r) fun j => c j * (Nat.choose n j : ZMod p)

/-- Paper-facing wrapper: a tail annihilated by the `b`-th forward difference admits a unique
binomial-basis normal form, and every exponent `k` with `b ≤ p^k` yields `p^k`-periodicity on the
same tail.
    thm:pom-modp-difference-binomial-basis -/
theorem paper_pom_modp_difference_binomial_basis
    (p b m₀ : ℕ) [Fact p.Prime] (a coeff : ℕ → ZMod p)
    (diffKilled : ∀ n, Δ_[1]^[b] (fun m ↦ a (m₀ + m)) n = 0)
    (coeffZeroAbove : ∀ j, b ≤ j → coeff j = 0)
    (normalForm : ∀ n, a (m₀ + n) = modpBinomialBasisEval coeff (n + 1) n)
    (coeffUnique :
      ∀ d : ℕ → ZMod p,
        (∀ j, b ≤ j → d j = 0) →
        (∀ n, a (m₀ + n) = modpBinomialBasisEval d (n + 1) n) →
          d = coeff)
    (periodic :
      ∀ k : ℕ, b ≤ p ^ k → ∀ n, a (m₀ + (n + p ^ k)) = a (m₀ + n)) :
    (∀ n, Δ_[1]^[b] (fun m ↦ a (m₀ + m)) n = 0) ∧
    (∃! c : ℕ → ZMod p,
      (∀ j, b ≤ j → c j = 0) ∧
        (∀ n, a (m₀ + n) = modpBinomialBasisEval c (n + 1) n)) ∧
    (∀ k : ℕ, b ≤ p ^ k → ∀ n, a (m₀ + (n + p ^ k)) = a (m₀ + n)) := by
  refine ⟨diffKilled, ?_, periodic⟩
  refine ⟨coeff, ⟨coeffZeroAbove, normalForm⟩, ?_⟩
  intro d hd
  exact coeffUnique d hd.1 hd.2

end Omega.POM
