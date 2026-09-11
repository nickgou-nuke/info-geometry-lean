import Mathlib.LinearAlgebra.Vandermonde
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.FieldTheory.Finite.Extension

/-!
# Vandermonde form of the BCH minimum-distance lemma

This file contains the algebraic core of the BCH argument.  A codeword with
fewer than `t` nonzero coefficients cannot vanish at `t` consecutive powers
of an element when the corresponding powers are distinct.  The proof is the
native Mathlib Vandermonde nonsingularity theorem, not finite enumeration.
-/

namespace InfoGeometry.Combinatorics.BinaryBCHMinimumDistance

theorem coefficients_eq_zero_of_consecutive_power_sums
    {K : Type*} [Field K] {t : ℕ}
    (α : K) (exponent : Fin t → ℕ)
    (hexponent : Function.Injective (fun i : Fin t => α ^ exponent i))
    (coeff : Fin t → K)
    (hvanish : ∀ j : Fin t,
      ∑ i : Fin t, coeff i * (α ^ exponent i) ^ (j : ℕ) = 0) :
    coeff = 0 := by
  exact Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    hexponent hvanish

theorem bch_no_sparse_vanishing_polynomial
    {K : Type*} [Field K] {t : ℕ}
    (α : K) (exponent : Fin t → ℕ)
    (hexponent : Function.Injective (fun i : Fin t => α ^ exponent i))
    (coeff : Fin t → K)
    (hvanish : ∀ j : Fin t,
      ∑ i : Fin t, coeff i * (α ^ exponent i) ^ (j : ℕ) = 0) :
    coeff = 0 :=
  coefficients_eq_zero_of_consecutive_power_sums α exponent hexponent coeff hvanish

theorem mapped_polynomial_splits_of_dvd_card_sub_X
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod p) K]
    (f : Polynomial (ZMod p))
    (hdiv : f ∣ Polynomial.X ^ Fintype.card K - Polynomial.X) :
    (Polynomial.map (algebraMap (ZMod p) K) f).Splits := by
  apply Polynomial.Splits.of_dvd
    (FiniteField.splits_X_pow_card_sub_X p (K := K))
  · intro hzero
    have hcard1 : Fintype.card K ≠ 1 := by
      intro hc
      rcases (Fintype.card_eq_one_iff.mp hc) with ⟨x, hx⟩
      exact zero_ne_one ((hx 0).trans (hx 1).symm)
    have hcoeff := congrArg
      (fun q => q.coeff (Fintype.card K)) hzero
    have hcard1' : 1 ≠ Fintype.card K := Ne.symm hcard1
    simpa [Polynomial.coeff_X, hcard1, hcard1'] using hcoeff
  · exact Polynomial.map_dvd (algebraMap (ZMod p) K) hdiv

end InfoGeometry.Combinatorics.BinaryBCHMinimumDistance
