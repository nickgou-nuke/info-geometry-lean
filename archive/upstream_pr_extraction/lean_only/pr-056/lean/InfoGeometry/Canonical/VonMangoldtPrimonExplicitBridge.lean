import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.DirichletConvolutionUnityBridge

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Real ArithmeticFunction

namespace InfoGeometry.Canonical.VonMangoldtPrimonExplicitBridge

open InfoGeometry.Canonical.DirichletConvolutionUnityBridge

/-- 🏆 THEOREM 1: Non-negativity of the von Mangoldt Primon Energy Function:
    0 ≤ Λ(n) for all n ∈ ℕ -/
theorem vonMangoldt_is_nonneg (n : ℕ) :
    0 ≤ vonMangoldt n :=
  ArithmeticFunction.vonMangoldt_nonneg

/-- 🏆 THEOREM 2: von Mangoldt Energy Value on Primes:
    For a prime p, Λ(p) = ln p -/
theorem vonMangoldt_prime {p : ℕ} (hp : p.Prime) :
    vonMangoldt p = Real.log p :=
  ArithmeticFunction.vonMangoldt_apply_prime hp

/-- 🏆 THEOREM 3: von Mangoldt Energy Vanishing on Non-Prime-Powers:
    If n is not a prime power, Λ(n) = 0 -/
theorem vonMangoldt_non_prime_pow {n : ℕ} (hn : ¬ IsPrimePow n) :
    vonMangoldt n = 0 :=
  ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn

/-- 🏆 THEOREM 4: The von Mangoldt Dirichlet Convolution Identity Λ * ζ = log:
    Convolving the von Mangoldt operator Λ with the constant function ζ
    strictly yields the logarithmic energy operator log. -/
theorem vonMangoldt_conv_one_eq_log :
    (vonMangoldt * ArithmeticFunction.zeta : ArithmeticFunction ℝ) = ArithmeticFunction.log :=
  vonMangoldt_mul_zeta

end InfoGeometry.Canonical.VonMangoldtPrimonExplicitBridge
