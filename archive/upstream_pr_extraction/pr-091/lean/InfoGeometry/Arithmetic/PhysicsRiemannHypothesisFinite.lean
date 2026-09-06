import Mathlib.Tactic

/-!
# Finite arithmetic packet for `Physics of the Riemann Hypothesis`

This module formalizes theorem-safe finite arithmetic shadows from
Schumayer--Hutchinson, arXiv:1101.3116v1.  It is intentionally conservative:

* finite Euler-factor distributivity for the first two primes at `k = 2`,
* concrete nonzero Euler factors in the original half-plane example,
* finite Mobius divisor-sum and square-obstruction readouts,
* finite prime-counting data.

It does **not** assert RH, Hilbert--Polya, analytic continuation, quantum chaos,
Riemann--von Mangoldt asymptotics, or any physical spectral operator theorem.
Those remain outside this finite packet unless closed by existing
Hestenes--Krein/categorical colimit owner surfaces.
-/

namespace InfoGeometry.Arithmetic.PhysicsRiemannHypothesisFinite

/-- Paper-local finite Mobius table, enough for the checked divisor-sum examples. -/
def muPaper : ℕ → ℤ
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => 0
  | 5 => -1
  | 6 => 1
  | 7 => -1
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => -1
  | 12 => 0
  | _ => 0

/-- Divisor-sum cancellation for `n = 6`: `μ(1)+μ(2)+μ(3)+μ(6)=0`. -/
theorem muPaper_divisor_sum_six :
    muPaper 1 + muPaper 2 + muPaper 3 + muPaper 6 = 0 := by
  decide

/-- Divisor-sum cancellation for `n = 12`, including the square-obstruction divisors. -/
theorem muPaper_divisor_sum_twelve :
    muPaper 1 + muPaper 2 + muPaper 3 + muPaper 4 + muPaper 6 + muPaper 12 = 0 := by
  decide

/-- Concrete nonzero Euler factor for the first prime at exponent `k = 2`. -/
theorem euler_factor_two_k2_nonzero : (1 - (1 : ℚ) / 2 ^ 2) ≠ 0 := by
  norm_num

/-- Concrete nonzero Euler factor for the second prime at exponent `k = 2`. -/
theorem euler_factor_three_k2_nonzero : (1 - (1 : ℚ) / 3 ^ 2) ≠ 0 := by
  norm_num

/-- Finite signed fermionic/Mobius Euler factor for primes `2` and `3` at `k = 2`. -/
theorem finite_signed_mobius_factor_two_three_k2 :
    (1 - (1 : ℚ) / 2 ^ 2) * (1 - (1 : ℚ) / 3 ^ 2) = 2 / 3 := by
  norm_num

/-- Finite bosonic primon partition for primes `2` and `3` at `k = 2`. -/
theorem finite_boson_factor_two_three_k2 :
    ((1 - (1 : ℚ) / 2 ^ 2)⁻¹) * ((1 - (1 : ℚ) / 3 ^ 2)⁻¹) = 3 / 2 := by
  norm_num

/-- Finite boson/fermion cancellation: `ζ_S(2) · ζ_S(2)⁻¹ = 1` for `{2,3}`. -/
theorem finite_boson_signed_mobius_cancel_two_three_k2 :
    (((1 - (1 : ℚ) / 2 ^ 2)⁻¹) * ((1 - (1 : ℚ) / 3 ^ 2)⁻¹)) *
      ((1 - (1 : ℚ) / 2 ^ 2) * (1 - (1 : ℚ) / 3 ^ 2)) = 1 := by
  norm_num

/--
Finite fermionic primon partition factor from paper equation (58), at primes `{2,3}`
and `s = 2`: local occupations are `0` or `1`, so the factor is
`∏ₚ (1 + p⁻²)`.  This is a finite Euler-factor identity only.
-/
theorem finite_fermion_primon_two_three_k2 :
    (1 + (1 : ℚ) / 2 ^ 2) * (1 + (1 : ℚ) / 3 ^ 2) = 25 / 18 := by
  norm_num

/-- The same finite fermionic factor as the quotient `∏ₚ (1-p⁻⁴)/(1-p⁻²)`. -/
theorem finite_fermion_primon_quotient_two_three_k2 :
    ((1 - (1 : ℚ) / 2 ^ 4) / (1 - (1 : ℚ) / 2 ^ 2)) *
      ((1 - (1 : ℚ) / 3 ^ 4) / (1 - (1 : ℚ) / 3 ^ 2)) = 25 / 18 := by
  norm_num

/--
Finite `κ = 3` parafermion primon partition factor from paper equation (59),
restricted to primes `{2,3}` and `s = 2`: occupations are `0,1,2`.
-/
theorem finite_parafermion3_primon_two_three_k2 :
    (1 + (1 : ℚ) / 2 ^ 2 + (1 : ℚ) / 2 ^ 4) *
      (1 + (1 : ℚ) / 3 ^ 2 + (1 : ℚ) / 3 ^ 4) = 637 / 432 := by
  norm_num

/-- The same finite `κ = 3` parafermion factor as `∏ₚ (1-p⁻⁶)/(1-p⁻²)`. -/
theorem finite_parafermion3_primon_quotient_two_three_k2 :
    ((1 - (1 : ℚ) / 2 ^ 6) / (1 - (1 : ℚ) / 2 ^ 2)) *
      ((1 - (1 : ℚ) / 3 ^ 6) / (1 - (1 : ℚ) / 3 ^ 2)) = 637 / 432 := by
  norm_num

/-- Exact finite geometric factor for powers of `2` through exponent bound `3`. -/
theorem finite_geometric_two_k2_bound3 :
    (∑ a ∈ Finset.range 4, (1 : ℚ) / 2 ^ (2 * a)) = 85 / 64 := by
  norm_num [Finset.sum_range_succ]

/-- Exact finite geometric factor for powers of `3` through exponent bound `3`. -/
theorem finite_geometric_three_k2_bound3 :
    (∑ a ∈ Finset.range 4, (1 : ℚ) / 3 ^ (2 * a)) = 820 / 729 := by
  norm_num [Finset.sum_range_succ]

/--
Finite Euler-product distributivity for the first two primes with `k = 2` and
exponent bound `3`.  This is the finite algebraic shadow of the paper's Euler
product discussion, not an infinite product theorem.
-/
theorem finite_euler_product_two_three_k2_bound3 :
    (∑ a ∈ Finset.range 4, (1 : ℚ) / 2 ^ (2 * a)) *
      (∑ b ∈ Finset.range 4, (1 : ℚ) / 3 ^ (2 * b)) =
        17425 / 11664 := by
  norm_num [Finset.sum_range_succ]

/-- Prime-counting finite datum: there are four primes at most ten. -/
theorem prime_count_le_ten :
    ((Finset.Icc 1 10).filter Nat.Prime).card = 4 := by
  decide

/-- Prime-counting finite datum: there are ten primes at most thirty. -/
theorem prime_count_le_thirty :
    ((Finset.Icc 1 30).filter Nat.Prime).card = 10 := by
  decide

/-- Explicit finite prime list through thirty, matching the sieve count. -/
theorem primes_le_thirty_list :
    (Finset.Icc 1 30).filter Nat.Prime =
      ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by
  decide

/-- Mertens finite datum through ten: `∑_{n≤10} μ(n) = -1` for the table above. -/
theorem mertens_muPaper_ten :
    muPaper 1 + muPaper 2 + muPaper 3 + muPaper 4 + muPaper 5 +
      muPaper 6 + muPaper 7 + muPaper 8 + muPaper 9 + muPaper 10 = -1 := by
  decide

end InfoGeometry.Arithmetic.PhysicsRiemannHypothesisFinite
