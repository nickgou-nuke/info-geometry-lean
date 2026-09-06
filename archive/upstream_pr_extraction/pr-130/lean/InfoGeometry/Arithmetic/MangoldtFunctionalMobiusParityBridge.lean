import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open scoped BigOperators

noncomputable section

namespace InfoGeometry.Arithmetic.MangoldtFunctionalMobiusParityBridge

/-- Real-valued von Mangoldt arithmetic readout. -/
def mangoldtFunctional (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

/-- Integer-valued Möbius arithmetic readout. -/
def moebiusParity (n : ℕ) : ℤ :=
  ArithmeticFunction.moebius n

/-- The von Mangoldt readout is nonnegative. -/
theorem mangoldt_functional_nonneg (n : ℕ) : 0 ≤ mangoldtFunctional n :=
  ArithmeticFunction.vonMangoldt_nonneg

/-- At a prime index, the von Mangoldt readout is `log p`. -/
theorem mangoldt_functional_prime {p : ℕ} (hp : Nat.Prime p) :
    mangoldtFunctional p = Real.log (p : ℝ) := by
  dsimp [mangoldtFunctional]
  exact ArithmeticFunction.vonMangoldt_apply_prime hp

/-- The von Mangoldt readout vanishes away from prime powers. -/
theorem mangoldt_functional_zero_of_not_isPrimePow {n : ℕ} (hn : ¬ IsPrimePow n) :
    mangoldtFunctional n = 0 := by
  dsimp [mangoldtFunctional]
  rw [ArithmeticFunction.vonMangoldt_apply]
  rw [if_neg hn]

/-- At a nontrivial prime power, the readout is `log p`. -/
theorem mangoldt_functional_prime_pow {p k : ℕ} (hp : Nat.Prime p) (hk : k ≠ 0) :
    mangoldtFunctional (p ^ k) = Real.log (p : ℝ) := by
  dsimp [mangoldtFunctional]
  rw [ArithmeticFunction.vonMangoldt_apply_pow (n := p) (k := k) hk]
  exact ArithmeticFunction.vonMangoldt_apply_prime hp

/-- Pointwise divisor-sum form of the native Dirichlet-convolution identity
`log * μ = Λ`.  The sum is over the divisors antidiagonal, so this is the
finite arithmetic readout rather than an analytic Dirichlet-series claim. -/
theorem mangoldt_functional_eq_log_moebius_divisors (n : ℕ) :
    ∑ x ∈ n.divisorsAntidiagonal,
      Real.log (x.1 : ℝ) * (ArithmeticFunction.moebius x.2 : ℝ) =
      mangoldtFunctional n := by
  change (∑ x ∈ n.divisorsAntidiagonal,
      ArithmeticFunction.log x.1 *
        ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) x.2)) =
    ArithmeticFunction.vonMangoldt n
  rw [← ArithmeticFunction.mul_apply]
  rw [ArithmeticFunction.log_mul_moebius_eq_vonMangoldt]

/- The complementary native divisor-sum readout: summing the von Mangoldt
function over the divisors of `n` recovers the logarithmic arithmetic weight.
This is a finite identity and makes no Dirichlet-series or asymptotic claim. -/
theorem mangoldt_functional_divisor_sum_eq_log (n : ℕ) :
    ∑ d ∈ n.divisors, mangoldtFunctional d = Real.log (n : ℝ) := by
  change ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d = Real.log (n : ℝ)
  exact ArithmeticFunction.vonMangoldt_sum

/-- Pointwise form of the native convolution identity `Λ * ζ = log`.
The zeta factor is kept explicit here so the Dirichlet-convolution structure
is visible at each finite index. -/
theorem mangoldt_functional_zeta_convolution_eq_log (n : ℕ) :
    ∑ x ∈ n.divisorsAntidiagonal,
      mangoldtFunctional x.1 * (ArithmeticFunction.zeta x.2 : ℝ) =
        Real.log (n : ℝ) := by
  change (∑ x ∈ n.divisorsAntidiagonal,
      ArithmeticFunction.vonMangoldt x.1 *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) x.2)) =
    Real.log (n : ℝ)
  rw [← ArithmeticFunction.mul_apply]
  rw [ArithmeticFunction.vonMangoldt_mul_zeta]
  exact ArithmeticFunction.log_apply

/-- The Möbius readout vanishes at nonsquarefree indices. -/
theorem moebius_parity_zero_of_not_squarefree {n : ℕ} (hn : ¬ Squarefree n) :
    moebiusParity n = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn

/-- Bundles the preceding von Mangoldt and Möbius identities. -/
theorem mangoldt_moebius_master_duality
    {p k n : ℕ} (hp : Nat.Prime p) (hk : k ≠ 0) (h_not_pp : ¬ IsPrimePow n) (h_not_sq : ¬ Squarefree n) :
    (0 ≤ mangoldtFunctional n) ∧
    (mangoldtFunctional p = Real.log (p : ℝ)) ∧
    (mangoldtFunctional (p ^ k) = Real.log (p : ℝ)) ∧
    (mangoldtFunctional n = 0) ∧
    (moebiusParity n = 0) := ⟨
  mangoldt_functional_nonneg n,
  mangoldt_functional_prime hp,
  mangoldt_functional_prime_pow hp hk,
  mangoldt_functional_zero_of_not_isPrimePow h_not_pp,
  moebius_parity_zero_of_not_squarefree h_not_sq
⟩

end InfoGeometry.Arithmetic.MangoldtFunctionalMobiusParityBridge
