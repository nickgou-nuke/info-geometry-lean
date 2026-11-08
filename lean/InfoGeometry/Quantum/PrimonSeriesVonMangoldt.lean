/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

namespace InfoGeometry.Quantum.PrimonSeries

open Real Filter Topology BigOperators Nat

noncomputable section

/-- The type of prime numbers. -/
def PrimeNat := { p : ℕ // Nat.Prime p }

instance : Coe PrimeNat ℕ where
  coe p := p.val

/-- General term of the double sum over prime p and mode k: p^(-(k+1)β) / (k+1). -/
def primonDoubleTerm (beta : ℝ) (pair : PrimeNat × ℕ) : ℝ :=
  let p : ℝ := (pair.1 : ℕ)
  let k : ℝ := (pair.2 : ℝ) + 1
  (p ^ (-k * beta)) / k

/-- Von Mangoldt log-weighted Dirichlet series term: Λ(n) / (ln n · n^β). -/
def vonMangoldtDirichletTerm (beta : ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then
    (ArithmeticFunction.vonMangoldt n : ℝ) / (Real.log (n : ℝ) * (n : ℝ) ^ beta)
  else
    0

/-!
### 1. Mode Power Law Identity
-/

/-- 🏆 THEOREM 1: Algebraic power law: (p^(-β))^(k+1) = p^(-(k+1)β). -/
theorem primon_power_law (p : ℕ) (hp : 2 ≤ p) (beta : ℝ) (k : ℕ) :
    ((p : ℝ) ^ (-beta)) ^ (k + 1) = (p : ℝ) ^ (-(k + 1 : ℝ) * beta) := by
  have hp_pos : 0 < (p : ℝ) := by
    have : 2 ≤ (p : ℝ) := Nat.cast_le.mpr hp
    linarith
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-beta)) (k + 1)]
  rw [← Real.rpow_mul (le_of_lt hp_pos)]
  congr 1
  push_cast
  ring

/-!
### 2. Double Sum Fubini Rearrangement (Primes × Modes ≃ Prime Powers)
-/

/-- Injection from (PrimeNat × ℕ) to positive integers mapping (p, k) ↦ p^(k+1). -/
def primePowerEquiv (pair : PrimeNat × ℕ) : ℕ :=
  (pair.1 : ℕ) ^ (pair.2 + 1)

/-- 🏆 THEOREM 2: Prime powers p^(k+1) are strictly greater than or equal to 2. -/
theorem primePower_ge_two (pair : PrimeNat × ℕ) :
    2 ≤ primePowerEquiv pair := by
  unfold primePowerEquiv
  have hp : 2 ≤ (pair.1 : ℕ) := pair.1.2.two_le
  have h_pow := Nat.le_self_pow (Nat.succ_ne_zero pair.2) (pair.1 : ℕ)
  exact le_trans hp h_pow

/-- 🏆 THEOREM 3: The double term evaluates precisely to the von Mangoldt term on prime powers. -/
theorem primon_term_eq_vonMangoldt_term (beta : ℝ) (pair : PrimeNat × ℕ) :
    primonDoubleTerm beta pair = vonMangoldtDirichletTerm beta (primePowerEquiv pair) := by
  dsimp [primonDoubleTerm, vonMangoldtDirichletTerm, primePowerEquiv]
  have h_ge2 : 2 ≤ (pair.1 : ℕ) ^ (pair.2 + 1) := primePower_ge_two pair
  have hp_prime : (pair.1 : ℕ).Prime := pair.1.2
  have hp_pos : 0 < (pair.1 : ℝ) := by
    have : 2 ≤ (pair.1 : ℝ) := Nat.cast_le.mpr hp_prime.two_le
    linarith
  have h_lambda : (ArithmeticFunction.vonMangoldt ((pair.1 : ℕ) ^ (pair.2 + 1)) : ℝ) = Real.log (pair.1 : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _), ArithmeticFunction.vonMangoldt_apply_prime hp_prime]
  have h_cast : (((pair.1 : ℕ) ^ (pair.2 + 1) : ℕ) : ℝ) = (pair.1 : ℝ) ^ (pair.2 + 1) := by
    push_cast
    rfl
  have h_log_pow : Real.log (((pair.1 : ℕ) ^ (pair.2 + 1) : ℕ) : ℝ) = ((pair.2 : ℝ) + 1) * Real.log (pair.1 : ℝ) := by
    rw [h_cast, Real.log_pow]
    push_cast
    ring
  have h_rpow_pow : ((((pair.1 : ℕ) ^ (pair.2 + 1) : ℕ) : ℝ) ^ beta) = (pair.1 : ℝ) ^ (((pair.2 : ℝ) + 1) * beta) := by
    rw [h_cast, ← Real.rpow_natCast, Real.rpow_mul (le_of_lt hp_pos)]
    push_cast
    ring_nf
  have h_rpow_neg : (pair.1 : ℝ) ^ (-(((pair.2 : ℝ) + 1) * beta)) = 1 / ((pair.1 : ℝ) ^ (((pair.2 : ℝ) + 1) * beta)) := by
    rw [Real.rpow_neg (le_of_lt hp_pos) (((pair.2 : ℝ) + 1) * beta), one_div]
  have h_rpow_neg' : (pair.1 : ℝ) ^ (-(pair.2 + 1 : ℝ) * beta) = 1 / ((pair.1 : ℝ) ^ (((pair.2 : ℝ) + 1) * beta)) := by
    have h_eq : -(pair.2 + 1 : ℝ) * beta = -(((pair.2 : ℝ) + 1) * beta) := by ring
    rw [h_eq, h_rpow_neg]
  have h_log_ne : Real.log (pair.1 : ℝ) ≠ 0 := by
    have : 1 < (pair.1 : ℝ) := by
      have : 2 ≤ (pair.1 : ℝ) := Nat.cast_le.mpr hp_prime.two_le
      linarith
    exact ne_of_gt (Real.log_pos this)
  have h_k_ne : (pair.2 : ℝ) + 1 ≠ 0 := by positivity
  rw [if_pos h_ge2, h_lambda, h_log_pow, h_rpow_pow, h_rpow_neg']
  field_simp

end

end InfoGeometry.Quantum.PrimonSeries
