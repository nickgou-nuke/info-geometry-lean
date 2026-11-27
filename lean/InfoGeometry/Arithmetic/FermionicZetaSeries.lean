/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Fermionic Zeta Series `Z_f(s) = ζ(s) / ζ(2s)` (Castro 2006 §2, Eq. 1)

Formalizes the fermionic zeta function on the absolute convergence half-plane `1 < s.re`:
`Z_f(s) = ∑' n, |μ(n)| / n^s = ∏_p (1 + p^{-s}) = ζ(s) / ζ(2s)`.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.FermionicZetaSeries

open Complex Filter
open scoped BigOperators Topology LSeries.notation

/-- Coefficient sequence `|μ(n)|` for the fermionic zeta series:
`1` if `n` is squarefree and `0` otherwise. -/
def fermionicZetaCoeff (n : ℕ) : ℂ :=
  if Squarefree n then 1 else 0

/-- The fermionic zeta function `Z_f(s) = ∑' n, |μ(n)| / n^s` on `1 < s.re`. -/
def fermionicZeta (s : ℂ) : ℂ :=
  LSeries fermionicZetaCoeff s

@[simp]
theorem fermionicZetaCoeff_zero : fermionicZetaCoeff 0 = 0 := by
  simp [fermionicZetaCoeff, not_squarefree_zero]

@[simp]
theorem fermionicZetaCoeff_one : fermionicZetaCoeff 1 = 1 := by
  simp [fermionicZetaCoeff]

theorem abs_moebius_eq_indicator_squarefree (n : ℕ) :
    ((|ArithmeticFunction.moebius n| : ℤ) : ℂ) = if Squarefree n then (1 : ℂ) else 0 := by
  rw [ArithmeticFunction.abs_moebius]
  split_ifs <;> simp

theorem fermionicZetaCoeff_eq_abs_moebius (n : ℕ) :
    fermionicZetaCoeff n = ((|ArithmeticFunction.moebius n| : ℤ) : ℂ) :=
  (abs_moebius_eq_indicator_squarefree n).symm

theorem fermionicZetaCoeff_norm_le_one (n : ℕ) : ‖fermionicZetaCoeff n‖ ≤ 1 := by
  unfold fermionicZetaCoeff
  split_ifs <;> simp

theorem fermionicZetaCoeff_coprime_mul {m n : ℕ} (hmn : Nat.Coprime m n) :
    fermionicZetaCoeff (m * n) = fermionicZetaCoeff m * fermionicZetaCoeff n := by
  by_cases hm : Squarefree m <;> by_cases hn : Squarefree n <;>
    simp [fermionicZetaCoeff, Nat.squarefree_mul hmn, hm, hn]

theorem fermionicZetaCoeff_two : fermionicZetaCoeff 2 = 1 := by
  simp [fermionicZetaCoeff, Nat.prime_two.prime.squarefree]

theorem fermionicZetaCoeff_four : fermionicZetaCoeff 4 = 0 := by
  have hnsq : ¬ Squarefree (4 : ℕ) := by
    intro h
    exact absurd (h 2 (by norm_num)) (by decide)
  simp [fermionicZetaCoeff, hnsq]

theorem fermionicZetaCoeff_six : fermionicZetaCoeff 6 = 1 := by
  have hsq : Squarefree (6 : ℕ) := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.squarefree_mul (by decide)]
    exact ⟨Nat.prime_two.prime.squarefree, Nat.prime_three.prime.squarefree⟩
  simp [fermionicZetaCoeff, hsq]

theorem fermionicZeta_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable fermionicZetaCoeff s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => fermionicZetaCoeff_norm_le_one n) hs

theorem fermionicZeta_eq_tsum_div (s : ℂ) :
    fermionicZeta s = ∑' n : ℕ, fermionicZetaCoeff n / (n : ℂ) ^ s :=
  LSeries_def₀ fermionicZetaCoeff_zero s

theorem fermionicZeta_eq_LSeries_abs_moebius (s : ℂ) :
    fermionicZeta s =
      LSeries (fun n : ℕ => ((|ArithmeticFunction.moebius n| : ℤ) : ℂ)) s :=
  LSeries_congr (fun {n} _ => fermionicZetaCoeff_eq_abs_moebius n) s

private theorem fermionicZetaTerm_zero (s : ℂ) :
    LSeries.term fermionicZetaCoeff s 0 = 0 :=
  LSeries.term_zero _ _

private theorem fermionicZetaTerm_one (s : ℂ) :
    LSeries.term fermionicZetaCoeff s 1 = 1 := by
  rw [LSeries.term_of_ne_zero one_ne_zero, fermionicZetaCoeff_one]
  simp

private theorem fermionicZetaTerm_coprime_mul (s : ℂ) {m n : ℕ} (hmn : Nat.Coprime m n) :
    LSeries.term fermionicZetaCoeff s (m * n) =
      LSeries.term fermionicZetaCoeff s m * LSeries.term fermionicZetaCoeff s n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  rw [LSeries.term_of_ne_zero hmn0, LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn,
    fermionicZetaCoeff_coprime_mul hmn, Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
    div_mul_div_comm]

private theorem fermionicZetaTerm_prime_pow (s : ℂ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    LSeries.term fermionicZetaCoeff s (p ^ e) =
      if e = 0 then 1 else if e = 1 then (p : ℂ) ^ (-s) else 0 := by
  rcases e with _ | _ | k
  · simp [fermionicZetaCoeff]
  · rw [pow_one, LSeries.term_of_ne_zero hp.ne_zero]
    simp [fermionicZetaCoeff, hp.prime.squarefree, Complex.cpow_neg, div_eq_mul_inv]
  · have hnsq : ¬ Squarefree (p ^ (k + 2)) := by
      rw [Nat.squarefree_pow_iff hp.ne_one (Nat.succ_ne_zero _)]
      omega
    rw [LSeries.term_of_ne_zero (pow_ne_zero _ hp.ne_zero)]
    simp [fermionicZetaCoeff, hnsq]

private theorem tsum_fermionicZetaTerm_prime_pow {s : ℂ} (hs : 1 < s.re) {p : ℕ}
    (hp : p.Prime) :
    (∑' e : ℕ, LSeries.term fermionicZetaCoeff s (p ^ e)) = 1 + (p : ℂ) ^ (-s) := by
  have hsum : Summable (fun e : ℕ => LSeries.term fermionicZetaCoeff s (p ^ e)) :=
    (fermionicZeta_summable hs).comp_injective (Nat.pow_right_injective hp.one_lt)
  have hsum1 : Summable (fun e : ℕ => LSeries.term fermionicZetaCoeff s (p ^ (e + 1))) :=
    hsum.comp_injective (add_left_injective 1)
  have hzero : (fun e : ℕ => LSeries.term fermionicZetaCoeff s (p ^ (e + 2))) = fun _ => 0 :=
    funext fun e => by simp [fermionicZetaTerm_prime_pow s hp (e + 2)]
  rw [hsum.tsum_eq_zero_add, hsum1.tsum_eq_zero_add,
    show (fun e : ℕ => LSeries.term fermionicZetaCoeff s (p ^ (e + 1 + 1))) = fun _ => 0 from
      hzero,
    tsum_zero, add_zero, fermionicZetaTerm_prime_pow s hp 0, fermionicZetaTerm_prime_pow s hp 1]
  simp

/-- Euler product `HasProd` form for the fermionic zeta function on `1 < s.re`. -/
theorem fermionicZeta_eulerProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1 + (p : ℂ) ^ (-s)) (fermionicZeta s) := by
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term fermionicZetaCoeff s n‖) :=
    (fermionicZeta_summable hs).norm
  have heul := EulerProduct.eulerProduct_hasProd (fermionicZetaTerm_one s)
    (fun hmn => fermionicZetaTerm_coprime_mul s hmn) hnorm (fermionicZetaTerm_zero s)
  have heul' :
      HasProd (fun p : Nat.Primes => ∑' e : ℕ, LSeries.term fermionicZetaCoeff s ((p : ℕ) ^ e))
        (fermionicZeta s) := heul
  have hfun :
      (fun p : Nat.Primes => ∑' e : ℕ, LSeries.term fermionicZetaCoeff s ((p : ℕ) ^ e)) =
        fun p : Nat.Primes => 1 + (p : ℂ) ^ (-s) :=
    funext fun p => tsum_fermionicZetaTerm_prime_pow hs p.prop
  rwa [hfun] at heul'

/-- Euler product `tprod` form for the fermionic zeta function on `1 < s.re`. -/
theorem fermionicZeta_eulerProduct_tprod {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 + (p : ℂ) ^ (-s))) = fermionicZeta s :=
  (fermionicZeta_eulerProduct_hasProd hs).tprod_eq

/-- Partial Euler product convergence `∏_{p < n} (1 + p^{-s}) → Z_f(s)` on `1 < s.re`. -/
theorem fermionicZeta_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (fun n : ℕ => ∏ p ∈ Nat.primesBelow n, (1 + (p : ℂ) ^ (-s)))
      Filter.atTop (𝓝 (fermionicZeta s)) := by
  have heul := EulerProduct.eulerProduct (fermionicZetaTerm_one s)
    (fun hmn => fermionicZetaTerm_coprime_mul s hmn) (fermionicZeta_summable hs).norm
    (fermionicZetaTerm_zero s)
  refine heul.congr fun n => ?_
  exact Finset.prod_congr rfl fun p hp =>
    tsum_fermionicZetaTerm_prime_pow hs (Nat.prime_of_mem_primesBelow hp)

private theorem prime_eulerFactor_ratio {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    (1 - (p : ℂ) ^ (-s))⁻¹ / (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ = 1 + (p : ℂ) ^ (-s) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
  have h2 : (p : ℂ) ^ (-(2 * s)) = (p : ℂ) ^ (-s) * (p : ℂ) ^ (-s) := by
    rw [← Complex.cpow_add _ _ hp0]
    ring_nf
  have hne : 1 - (p : ℂ) ^ (-s) ≠ 0 := Complex.one_sub_prime_cpow_ne_zero p.prop hs
  rw [h2, div_inv_eq_mul,
    show 1 - (p : ℂ) ^ (-s) * (p : ℂ) ^ (-s) = (1 - (p : ℂ) ^ (-s)) * (1 + (p : ℂ) ^ (-s)) by
      ring,
    ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- Castro (2006) §2, Eq. (1): for `1 < s.re`, `Z_f(s) = ζ(s) / ζ(2s)`. -/
theorem fermionicZeta_eq_riemannZeta_div {s : ℂ} (hs : 1 < s.re) :
    fermionicZeta s = riemannZeta s / riemannZeta (2 * s) := by
  have hs2 : 1 < (2 * s).re := by
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have h1 := riemannZeta_eulerProduct_hasProd hs
  have h2 := riemannZeta_eulerProduct_hasProd hs2
  have hne2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs2
  have hdiv :
      HasProd (fun p : Nat.Primes => 1 + (p : ℂ) ^ (-s))
        (riemannZeta s / riemannZeta (2 * s)) := by
    simpa only [prime_eulerFactor_ratio hs] using h1.div₀ h2 hne2
  exact (fermionicZeta_eulerProduct_hasProd hs).unique hdiv

theorem LSeries_squarefree_eq_riemannZeta_div {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => if Squarefree n then (1 : ℂ) else 0) s =
      riemannZeta s / riemannZeta (2 * s) :=
  fermionicZeta_eq_riemannZeta_div hs

theorem LSeries_abs_moebius_eq_riemannZeta_div {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => ((|ArithmeticFunction.moebius n| : ℤ) : ℂ)) s =
      riemannZeta s / riemannZeta (2 * s) := by
  rw [← fermionicZeta_eq_LSeries_abs_moebius, fermionicZeta_eq_riemannZeta_div hs]

theorem fermionicZeta_mul_riemannZeta_two_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    fermionicZeta s * riemannZeta (2 * s) = riemannZeta s := by
  have hs2 : 1 < (2 * s).re := by
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  rw [fermionicZeta_eq_riemannZeta_div hs,
    div_mul_cancel₀ _ (riemannZeta_ne_zero_of_one_lt_re hs2)]

theorem fermionicZeta_eq_riemannZeta_mul_mobius_LSeries {s : ℂ} (hs : 1 < s.re) :
    fermionicZeta s =
      riemannZeta s * L ↗(ArithmeticFunction.moebius : ArithmeticFunction ℂ) (2 * s) := by
  have hs2 : 1 < (2 * s).re := by
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have hmul :
      riemannZeta (2 * s) * L ↗(ArithmeticFunction.moebius : ArithmeticFunction ℂ) (2 * s) = 1 := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs2]
    exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs2
  have h1div :
      1 / riemannZeta (2 * s) = L ↗(ArithmeticFunction.moebius : ArithmeticFunction ℂ) (2 * s) := by
    simpa [one_div] using (eq_inv_of_mul_eq_one_right hmul).symm
  rw [fermionicZeta_eq_riemannZeta_div hs, div_eq_mul_one_div, h1div]

theorem fermionicZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    fermionicZeta s ≠ 0 := by
  have hs2 : 1 < (2 * s).re := by
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  rw [fermionicZeta_eq_riemannZeta_div hs]
  exact div_ne_zero (riemannZeta_ne_zero_of_one_lt_re hs)
    (riemannZeta_ne_zero_of_one_lt_re hs2)

end InfoGeometry.Arithmetic.FermionicZetaSeries
