import Mathlib.Analysis.Convex.Jensen
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Convexity Lemmas for Information Geometry

Provides the rigorous mathematical foundation for Jensen's inequality 
and the non-negativity of entropy-like functionals.
-/

namespace InfoGeometry.Math.Convexity

open Set Real

/-- 
The function f(x) = -log x is convex on (0, ∞).
-/
theorem convexOn_neg_log : 
    ConvexOn ℝ (Ioi 0) (fun x => -log x) := by
  exact
    (neg_convexOn_iff (𝕜 := ℝ) (s := Ioi 0) (f := Real.log)).2
      strictConcaveOn_log_Ioi.concaveOn

/-- 
Jensen's inequality for the negative logarithm (finite sum form).
-/
theorem neg_log_jensen_sum
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (x : ι → ℝ) (hx_pos : ∀ i, 0 < x i) :
    -log (∑ i, w i * x i) ≤ ∑ i, w i * (-log (x i)) :=
by
  simpa using
    (convexOn_neg_log.map_sum_le
      (t := Finset.univ)
      (w := w)
      (p := x)
      (h₀ := fun i _ => hw_nonneg i)
      (h₁ := by simpa using hw_sum)
      (hmem := fun i _ => hx_pos i))

/-- 
Convexity of KL divergence in its second argument (Jensen's inequality for measures).
∑ p log(p/q_mix) ≤ ∑ w ∑ p log(p/q)
where q_mix = ∑ w q.
-/
theorem kl_convexity_finite
    {ι Y : Type*} [Fintype ι] [Fintype Y]
    (p : Y → ℝ) (hp_nonneg : ∀ y, 0 ≤ p y)
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (q : ι → Y → ℝ) (hq_pos : ∀ i y, 0 < q i y) :
    let q_mix : Y → ℝ := fun y => ∑ i, w i * (q i y)
    ∑ y, p y * log (p y / q_mix y) ≤ ∑ i, w i * (∑ y, p y * log (p y / (q i y))) := by
  let q_mix : Y → ℝ := fun y => ∑ i, w i * (q i y)
  change ∑ y, p y * log (p y / q_mix y) ≤ ∑ i, w i * (∑ y, p y * log (p y / (q i y)))
  have hw_exists_pos : ∃ i : ι, 0 < w i := by
    by_contra hnone
    have hw_zero : ∀ i : ι, w i = 0 := by
      intro i
      exact le_antisymm (le_of_not_gt (not_exists.mp hnone i)) (hw_nonneg i)
    have hsum0 : (∑ i, w i) = 0 := by simp [hw_zero]
    linarith [hw_sum, hsum0]
  have hq_mix_pos : ∀ y : Y, 0 < q_mix y := by
    intro y
    rcases hw_exists_pos with ⟨i0, hi0⟩
    have hterm_pos : 0 < w i0 * q i0 y := mul_pos hi0 (hq_pos i0 y)
    have hterm_le : w i0 * q i0 y ≤ q_mix y := by
      unfold q_mix
      exact Finset.single_le_sum
        (fun i _ => mul_nonneg (hw_nonneg i) (le_of_lt (hq_pos i y)))
        (by simp)
    exact lt_of_lt_of_le hterm_pos hterm_le

  have h_jensen : ∀ y, log (q_mix y) ≥ ∑ i, w i * log (q i y) := by
    intro y
    unfold q_mix
    have hneg :
        -log (∑ i, w i * q i y) ≤ ∑ i, w i * (-log (q i y)) :=
      neg_log_jensen_sum w hw_nonneg hw_sum (fun i => q i y) (fun i => hq_pos i y)
    have hneg' : -log (∑ i, w i * q i y) ≤ -(∑ i, w i * log (q i y)) := by
      simpa [Finset.sum_neg_distrib, mul_comm, mul_left_comm, mul_assoc] using hneg
    exact (neg_le_neg_iff.mp hneg')

  have h_sum :
      ∑ y, p y * (∑ i, w i * log (q i y))
        ≤ ∑ y, p y * log (q_mix y) := by
    refine Finset.sum_le_sum ?_
    intro y hy
    exact mul_le_mul_of_nonneg_left (h_jensen y) (hp_nonneg y)

  have h_swap :
      (∑ i, w i * (∑ y, p y * log (q i y)))
        = (∑ y, p y * (∑ i, w i * log (q i y))) := by
    calc
      (∑ i, w i * (∑ y, p y * log (q i y)))
          = ∑ i, ∑ y, w i * (p y * log (q i y)) := by
              simp [Finset.mul_sum]
      _ = ∑ y, ∑ i, w i * (p y * log (q i y)) := by
            rw [Finset.sum_comm]
      _ = ∑ y, p y * (∑ i, w i * log (q i y)) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring

  have hlog_div_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
      a * log (a / b) = a * log a - a * log b := by
    by_cases h0 : a = 0
    · simp [h0]
    · rw [log_div (by exact h0) (by exact hb.ne')]
      ring

  have h_split_lhs :
      ∑ y, p y * log (p y / q_mix y)
        = (∑ y, p y * log (p y)) - (∑ y, p y * log (q_mix y)) := by
    calc
      ∑ y, p y * log (p y / q_mix y)
          = ∑ y, (p y * log (p y) - p y * log (q_mix y)) := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              exact hlog_div_mul (p y) (q_mix y) (hp_nonneg y) (hq_mix_pos y)
      _ = (∑ y, p y * log (p y)) - (∑ y, p y * log (q_mix y)) := by
            rw [Finset.sum_sub_distrib]

  have h_split_rhs :
      (∑ i, w i * (∑ y, p y * log (p y / (q i y))))
        = (∑ y, p y * log (p y)) - (∑ i, w i * (∑ y, p y * log (q i y))) := by
    calc
      (∑ i, w i * (∑ y, p y * log (p y / (q i y))))
          = ∑ i, w i * (∑ y, (p y * log (p y) - p y * log (q i y))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine congrArg (fun z => w i * z) ?_
              refine Finset.sum_congr rfl ?_
              intro y hy
              exact hlog_div_mul (p y) (q i y) (hp_nonneg y) (hq_pos i y)
      _ = ∑ i, ((w i * (∑ y, p y * log (p y))) - (w i * (∑ y, p y * log (q i y)))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              w i * (∑ y, (p y * log (p y) - p y * log (q i y)))
                  = ∑ y, w i * (p y * log (p y) - p y * log (q i y)) := by
                      rw [Finset.mul_sum]
              _ 
                  = ∑ y, (w i * (p y * log (p y)) - w i * (p y * log (q i y))) := by
                      refine Finset.sum_congr rfl ?_
                      intro y hy
                      ring
              _ = (∑ y, w i * (p y * log (p y))) - (∑ y, w i * (p y * log (q i y))) := by
                    rw [Finset.sum_sub_distrib]
              _ = (w i * (∑ y, p y * log (p y))) - (w i * (∑ y, p y * log (q i y))) := by
                    rw [Finset.mul_sum, Finset.mul_sum]
      _ = (∑ i, w i * (∑ y, p y * log (p y)))
            - (∑ i, w i * (∑ y, p y * log (q i y))) := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ y, p y * log (p y)) - (∑ i, w i * (∑ y, p y * log (q i y))) := by
            rw [← Finset.sum_mul, hw_sum, one_mul]

  have hmain :
      (∑ i, w i * (∑ y, p y * log (q i y)))
        ≤ ∑ y, p y * log (q_mix y) := by
    rw [h_swap]
    exact h_sum

  rw [h_split_lhs, h_split_rhs]
  linarith

end InfoGeometry.Math.Convexity
