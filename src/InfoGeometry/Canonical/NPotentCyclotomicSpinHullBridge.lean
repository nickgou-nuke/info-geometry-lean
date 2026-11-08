import Mathlib.Analysis.Complex.Exponential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import InfoGeometry.Canonical.YangBaxterProof

/-!
# N-potent polynomial and the Fibonacci cyclotomic twist

This owner isolates the finite algebraic content of the proposed spin-hull
readout.  It proves the factorization of `z^n - z` for a nonzero complex
number, then specializes to the fifth-root twist used by the Fibonacci braid
owner.  No conformal-field realization or parafermion operator is inferred.
-/

noncomputable section

namespace InfoGeometry.Canonical.NPotentCyclotomicSpinHullBridge

open InfoGeometry.Canonical.YangBaxterProof

def nPotentPolynomial (n : ℕ) (z : ℂ) : ℂ := z ^ n - z

def cyclotomicRootCarrier (m : ℕ) : Set ℂ := {z | z ^ m = 1}

theorem n_potent_root_iff {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    nPotentPolynomial n z = 0 ↔ z ^ (n - 1) = 1 := by
  have hpow : z * z ^ (n - 1) = z ^ n := by
    calc
      z * z ^ (n - 1) = z ^ (n - 1) * z := by rw [mul_comm]
      _ = z ^ ((n - 1) + 1) := by rw [pow_succ]
      _ = z ^ n := by congr 1; omega
  constructor
  · intro h
    dsimp [nPotentPolynomial] at h
    have hfactor : z * (z ^ (n - 1) - 1) = 0 := by
      rw [mul_sub, hpow]
      simpa using h
    rcases mul_eq_zero.mp hfactor with hzero | hzero
    · exact False.elim (hz hzero)
    · exact sub_eq_zero.mp hzero
  · intro h
    dsimp [nPotentPolynomial] at h ⊢
    calc
      z ^ n - z = z * z ^ (n - 1) - z := by rw [hpow]
      _ = z * 1 - z := by rw [h]
      _ = 0 := by ring

theorem n_potent_root_mem_iff {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    nPotentPolynomial n z = 0 ↔ z ∈ cyclotomicRootCarrier (n - 1) := by
  simpa [cyclotomicRootCarrier] using n_potent_root_iff hn hz

/-- The Fibonacci twist `e^(4πi/5)` written in the existing tenth-root carrier. -/
noncomputable def fibonacciTwist : ℂ := q ^ 4

theorem fibonacciTwist_pow_five : fibonacciTwist ^ 5 = 1 := by
  dsimp [fibonacciTwist]
  calc
    (q ^ 4) ^ 5 = q ^ (4 * 5) := by rw [pow_mul]
    _ = q ^ (5 * 4) := by norm_num
    _ = (q ^ 5) ^ 4 := by rw [pow_mul]
    _ = 1 := by rw [q_pow_five]; norm_num

theorem fibonacciTwist_isPrimitiveRoot_five :
    IsPrimitiveRoot fibonacciTwist 5 := by
  have hq10 : IsPrimitiveRoot q 10 := by
    change IsPrimitiveRoot (Complex.exp (Real.pi * Complex.I / 5)) 10
    convert
      (Complex.isPrimitiveRoot_exp 10 (by norm_num : (10 : ℕ) ≠ 0)) using 1
    congr 1
    ring
  have hq2 : IsPrimitiveRoot (q ^ 2) 5 :=
    hq10.pow_of_dvd (by norm_num) (by norm_num)
  have hq4 : IsPrimitiveRoot ((q ^ 2) ^ 2) 5 :=
    hq2.pow_of_coprime 2 (by norm_num)
  have heq : (q ^ 2) ^ 2 = q ^ 4 := by ring
  rw [heq] at hq4
  simpa [fibonacciTwist] using hq4

/-- The sixth-potent polynomial splits into the zero factor and the named
primitive-fifth-root cyclotomic factor. -/
theorem six_potent_polynomial_factorization :
    (Polynomial.X ^ 6 - Polynomial.X : Polynomial ℂ) =
      Polynomial.X * Polynomial.cyclotomic 1 ℂ * Polynomial.cyclotomic 5 ℂ := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [Polynomial.cyclotomic_one, Polynomial.cyclotomic_prime]
  simp [Finset.sum_range_succ]
  ring

/-- The Fibonacci twist is a root of the named fifth cyclotomic polynomial. -/
theorem fibonacciTwist_is_cyclotomic_five_root :
    (Polynomial.cyclotomic 5 ℂ).IsRoot fibonacciTwist :=
  fibonacciTwist_isPrimitiveRoot_five.isRoot_cyclotomic (by norm_num)

theorem fibonacciTwist_ne_one : fibonacciTwist ≠ 1 :=
  fibonacciTwist_isPrimitiveRoot_five.ne_one (by norm_num)

theorem fibonacciTwist_pow_ne_one_of_pos_of_lt {k : ℕ}
    (hk0 : k ≠ 0) (hk5 : k < 5) : fibonacciTwist ^ k ≠ 1 :=
  fibonacciTwist_isPrimitiveRoot_five.pow_ne_one_of_pos_of_lt hk0 hk5

theorem fibonacciTwist_mem_fifth_roots :
    fibonacciTwist ∈ cyclotomicRootCarrier 5 := by
  simpa [cyclotomicRootCarrier] using fibonacciTwist_pow_five

theorem fibonacciTwist_six_potent :
    nPotentPolynomial 6 fibonacciTwist = 0 := by
  calc
    nPotentPolynomial 6 fibonacciTwist =
        fibonacciTwist ^ 6 - fibonacciTwist := rfl
    _ = fibonacciTwist ^ 5 * fibonacciTwist - fibonacciTwist := by ring
    _ = 1 * fibonacciTwist - fibonacciTwist := by rw [fibonacciTwist_pow_five]
    _ = 0 := by ring

theorem fibonacciTwist_mem_six_potent_hull :
    fibonacciTwist ^ 6 = fibonacciTwist := by
  have h := fibonacciTwist_six_potent
  dsimp [nPotentPolynomial] at h
  exact sub_eq_zero.mp h

theorem fibonacciTwist_minimal_nPotency :
    fibonacciTwist ^ 6 = fibonacciTwist ∧
      ∀ n : ℕ, 1 < n → n < 6 → fibonacciTwist ^ n ≠ fibonacciTwist := by
  refine ⟨fibonacciTwist_mem_six_potent_hull, ?_⟩
  intro n hn1 hn6 hpow
  have hpoly : nPotentPolynomial n fibonacciTwist = 0 := by
    dsimp [nPotentPolynomial]
    exact sub_eq_zero.mpr hpow
  have hroot : fibonacciTwist ^ (n - 1) = 1 :=
    (n_potent_root_iff (Nat.le_of_lt hn1)
      (fibonacciTwist_isPrimitiveRoot_five.ne_zero (by norm_num))).mp hpoly
  exact fibonacciTwist_pow_ne_one_of_pos_of_lt (by omega) (by omega) hroot

end InfoGeometry.Canonical.NPotentCyclotomicSpinHullBridge
