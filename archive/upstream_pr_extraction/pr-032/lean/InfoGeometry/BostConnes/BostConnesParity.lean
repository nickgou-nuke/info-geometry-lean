import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

noncomputable section

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.BostConnes

/-- Squarefree projector: `1` on squarefree integers, `0` otherwise. -/
def squarefreeProj (n : ℕ) : ℤ :=
  if Squarefree n then 1 else 0

/-- Raw Liouville-style parity on `ℕ`, expressed through `cardFactors`. -/
def liouvilleParity (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ ArithmeticFunction.cardFactors n

/-- On squarefree integers, Möbius equals the raw parity. -/
theorem moebius_eq_liouvilleParity_of_squarefree {n : ℕ} (hn : Squarefree n) :
    ArithmeticFunction.moebius n = liouvilleParity n := by
  simp [liouvilleParity, hn]

/-- Off the squarefree sector, Möbius vanishes. -/
theorem moebius_eq_zero_of_not_squarefree {n : ℕ} (hn : ¬Squarefree n) :
    ArithmeticFunction.moebius n = 0 := by
  simpa using ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn

/-- Möbius is the squarefree projection of the raw Liouville parity. -/
theorem moebius_eq_squarefreeProj_mul_liouvilleParity (n : ℕ) :
    ArithmeticFunction.moebius n = squarefreeProj n * liouvilleParity n := by
  by_cases hn : Squarefree n
  · simp [squarefreeProj, liouvilleParity, hn]
  · simp [squarefreeProj, liouvilleParity, hn]

/-- Equivalent projector form with the parity factor on the left. -/
theorem moebius_eq_liouvilleParity_mul_squarefreeProj (n : ℕ) :
    ArithmeticFunction.moebius n = liouvilleParity n * squarefreeProj n := by
  rw [moebius_eq_squarefreeProj_mul_liouvilleParity, mul_comm]

/-- The squarefree projector is idempotent. -/
theorem squarefreeProj_idempotent (n : ℕ) :
    squarefreeProj n * squarefreeProj n = squarefreeProj n := by
  by_cases hn : Squarefree n <;> simp [squarefreeProj, hn]

theorem squarefreeProj_eq_one_iff (n : ℕ) :
    squarefreeProj n = 1 ↔ Squarefree n := by
  by_cases hn : Squarefree n <;> simp [squarefreeProj, hn]

theorem squarefreeProj_eq_zero_iff (n : ℕ) :
    squarefreeProj n = 0 ↔ ¬ Squarefree n := by
  by_cases hn : Squarefree n <;> simp [squarefreeProj, hn]

theorem moebius_eq_zero_iff_not_squarefree (n : ℕ) :
    ArithmeticFunction.moebius n = 0 ↔ ¬ Squarefree n := by
  constructor
  · intro h
    by_contra hn
    have hsq := moebius_eq_liouvilleParity_of_squarefree hn
    have hparity : liouvilleParity n ≠ 0 := by
      simp [liouvilleParity]
    exact hparity (by rw [← hsq, h])
  · exact moebius_eq_zero_of_not_squarefree

theorem moebius_eq_one_or_neg_one_of_squarefree
    {n : ℕ} (hn : Squarefree n) :
    ArithmeticFunction.moebius n = 1 ∨
      ArithmeticFunction.moebius n = -1 := by
  rw [moebius_eq_liouvilleParity_of_squarefree hn]
  have hsq : liouvilleParity n ^ 2 = 1 := by
    unfold liouvilleParity
    rw [← pow_mul]
    norm_num
  exact sq_eq_one_iff.mp hsq

end InfoGeometry.BostConnes
