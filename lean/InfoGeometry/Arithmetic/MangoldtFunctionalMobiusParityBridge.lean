import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open scoped BigOperators

noncomputable section

namespace InfoGeometry.Arithmetic.MangoldtFunctionalMobiusParityBridge

/-- Real-valued von Mangoldt functional Λ(n). -/
def mangoldtFunctional (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

/-- Integer-valued Möbius parity operator μ(n) = (-1)^F. -/
def moebiusParity (n : ℕ) : ℤ :=
  ArithmeticFunction.moebius n

/-- **Theorem 1**: The von Mangoldt functional is nonnegative for all n. -/
theorem mangoldt_functional_nonneg (n : ℕ) : 0 ≤ mangoldtFunctional n :=
  ArithmeticFunction.vonMangoldt_nonneg

/-- **Theorem 2**: At a prime p, the von Mangoldt functional evaluates to log p. -/
theorem mangoldt_functional_prime {p : ℕ} (hp : Nat.Prime p) :
    mangoldtFunctional p = Real.log (p : ℝ) := by
  dsimp [mangoldtFunctional]
  exact ArithmeticFunction.vonMangoldt_apply_prime hp

/-- **Theorem 3**: For non-prime-powers (n with ≥2 distinct prime factors or n=0,1), Λ(n) = 0. -/
theorem mangoldt_functional_zero_of_not_isPrimePow {n : ℕ} (hn : ¬ IsPrimePow n) :
    mangoldtFunctional n = 0 := by
  dsimp [mangoldtFunctional]
  rw [ArithmeticFunction.vonMangoldt_apply]
  rw [if_neg hn]

/-- **Theorem 4**: For prime powers p^k (k ≠ 0), the von Mangoldt functional evaluates to log p. -/
theorem mangoldt_functional_prime_pow {p k : ℕ} (hp : Nat.Prime p) (hk : k ≠ 0) :
    mangoldtFunctional (p ^ k) = Real.log (p : ℝ) := by
  dsimp [mangoldtFunctional]
  rw [ArithmeticFunction.vonMangoldt_apply_pow (n := p) (k := k) hk]
  exact ArithmeticFunction.vonMangoldt_apply_prime hp

/-- **Theorem 5**: Möbius parity is 0 on any non-squarefree integer n. -/
theorem moebius_parity_zero_of_not_squarefree {n : ℕ} (hn : ¬ Squarefree n) :
    moebiusParity n = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn

/-- **Theorem 6**: Combined von Mangoldt and Möbius arithmetic readout. -/
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
