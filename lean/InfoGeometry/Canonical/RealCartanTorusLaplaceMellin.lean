import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open scoped BigOperators

noncomputable section

def cartanPlane : Type :=
  {t : Fin 3 → ℝ // ∑ i, t i = 0}

def positiveCartanTorus : Type :=
  {z : Fin 3 → ℝ // (∀ i, 0 < z i) ∧ ∏ i, z i = 1}

def cartanExponential (t : cartanPlane) : positiveCartanTorus :=
    ⟨fun i => Real.exp (2 * t.1 i),
    ⟨fun i => Real.exp_pos _, by
      rw [← Real.exp_sum]
      have hsum : (∑ i, 2 * t.1 i) = 2 * ∑ i, t.1 i := by
        rw [Finset.mul_sum]
      rw [hsum, t.2, mul_zero, Real.exp_zero]⟩⟩

def cartanLogarithm (z : positiveCartanTorus) : cartanPlane :=
  ⟨fun i => Real.log (z.1 i) / 2, by
    have hlog : ∑ i, Real.log (z.1 i) = 0 := by
      rw [← Real.log_prod]
      · rw [z.2.2, Real.log_one]
      · intro i hi
        exact (ne_of_gt (z.2.1 i))
    rw [← Finset.sum_div, hlog, zero_div]⟩

theorem cartanLogarithm_exponential (t : cartanPlane) :
    cartanLogarithm (cartanExponential t) = t := by
  apply Subtype.ext
  funext i
  simp [cartanLogarithm, cartanExponential]

theorem cartanExponential_logarithm (z : positiveCartanTorus) :
    cartanExponential (cartanLogarithm z) = z := by
  apply Subtype.ext
  funext i
  change Real.exp (2 * (Real.log (z.1 i) / 2)) = z.1 i
  have h : 2 * (Real.log (z.1 i) / 2) = Real.log (z.1 i) := by ring
  rw [h, Real.exp_log (z.2.1 i)]

theorem cartanExponential_coordinate_product (t : cartanPlane) :
    ∏ i, (cartanExponential t).1 i = 1 :=
  (cartanExponential t).2.2

theorem cartanExponential_coordinate_positive (t : cartanPlane) (i : Fin 3) :
    0 < (cartanExponential t).1 i :=
  (cartanExponential t).2.1 i

theorem cartanLaplace_character_mellin (t : cartanPlane) (s : Fin 3 → ℝ) :
    Real.exp (-(∑ i, s i * t.1 i)) =
    ∏ i, ((cartanExponential t).1 i) ^ (-(s i) / 2) := by
  calc
    Real.exp (-(∑ i, s i * t.1 i)) =
        Real.exp (∑ i, t.1 i * (-(s i))) := by
          congr 1
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∏ i, Real.exp (t.1 i * (-(s i))) := by
          rw [Real.exp_sum]
    _ = ∏ i, ((cartanExponential t).1 i) ^ (-(s i) / 2) := by
          apply Finset.prod_congr rfl
          intro i hi
          change Real.exp (t.1 i * (-(s i))) =
            Real.exp (2 * t.1 i) ^ (-(s i) / 2)
          rw [Real.rpow_def_of_pos (Real.exp_pos _)]
          rw [Real.log_exp]
          congr 1
          ring

theorem cartanLogarithm_double_exponential (t : ℝ) :
    Real.log (Real.exp (2 * t)) = 2 * t := by
  rw [Real.log_exp]

end

end InfoGeometry.Canonical
