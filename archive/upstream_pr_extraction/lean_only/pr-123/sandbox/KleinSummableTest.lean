import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import InfoGeometry.Physics.KleinBottleSpectrum

noncomputable section

open scoped BigOperators
open InfoGeometry.Physics.KleinBottleSpectrum
#check Summable.subtype
#check summable_subtype_iff_indicator
#check Summable.of_nonneg_of_le

example {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℤ => Real.exp (-r * (2 * (n : ℝ) + 1) ^ 2)) := by
  have hbase := summable_exp_neg_mul_sq_int hr
  apply hbase.of_nonneg_of_le (fun n => Real.exp_nonneg _)
  intro n
  apply Real.exp_le_exp.mpr
  have hsq : (n : ℝ) ^ 2 ≤ (2 * (n : ℝ) + 1) ^ 2 := by
    by_cases hn : 0 ≤ n
    · have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [sq_nonneg (n : ℝ)]
    · have hn' : n ≤ -1 := by omega
      have hnR : (n : ℝ) ≤ -1 := by exact_mod_cast hn'
      have hp : 0 ≤ (3 * (-(n : ℝ)) - 1) * (-(n : ℝ) - 1) := by
        apply mul_nonneg <;> nlinarith
      nlinarith
  nlinarith

example {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℕ => Real.exp (-r * (n : ℝ) ^ 2)) := by
  apply Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hr) ?_
  intro n
  exact_mod_cast Nat.le_pow (by norm_num : 0 < 2)

example {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℤ => Real.exp (-r * (n : ℝ) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · exact Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hr) (by
      intro n
      exact_mod_cast Nat.le_pow (by norm_num : 0 < 2))
  · simpa [Int.cast_neg, Int.cast_natCast, neg_sq] using
      (Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hr) (by
        intro n
        exact_mod_cast Nat.le_pow (by norm_num : 0 < 2)))

example {t a b : ℝ} (ht : 0 < t) (ha : a ≠ 0) (hb : b ≠ 0) :
    Summable (InfoGeometry.Physics.KleinBottleSpectrum.evenHeatTerm t a b) := by
  let r : ℝ := t * (4 * Real.pi / a) ^ 2
  let s : ℝ := t * (2 * Real.pi / b) ^ 2
  have hr : 0 < r := by
    dsimp [r]
    exact mul_pos ht (sq_pos_of_ne_zero (by
      intro h
      apply ha
      field_simp at h
      linarith [Real.pi_pos]))
  have hs : 0 < s := by
    dsimp [s]
    exact mul_pos ht (sq_pos_of_ne_zero (by
      intro h
      apply hb
      field_simp at h
      linarith [Real.pi_pos]))
  have h := InfoGeometry.Physics.KleinBottleSpectrum.summable_exp_neg_add_sq_int_nat hr hs
  apply h.congr
  intro q
  unfold InfoGeometry.Physics.KleinBottleSpectrum.evenHeatTerm
  unfold InfoGeometry.Physics.KleinBottleSpectrum.evenBranchEigenvalue
  unfold InfoGeometry.Physics.KleinBottleSpectrum.evenLongitudinalWaveNumber
  unfold InfoGeometry.Physics.KleinBottleSpectrum.transverseWaveNumber
  dsimp [r, s]
  congr 1
  ring

example {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Summable (fun q : ℤ × ℕ =>
      Real.exp (-r * (q.1 : ℝ) ^ 2 - s * (q.2 : ℝ) ^ 2)) := by
  apply (summable_prod_of_nonneg (fun q => Real.exp_nonneg _)).2
  constructor
  · intro n
    have hm := summable_exp_neg_mul_sq_nat hs
    have hmul := hm.mul_left (Real.exp (-r * (n : ℝ) ^ 2))
    convert hmul using 1
    ext m
    rw [← Real.exp_add]
    congr 1
    ring
  · have hn := summable_exp_neg_mul_sq_int hr
    have hconst : Summable (fun n : ℤ =>
        Real.exp (-r * (n : ℝ) ^ 2) *
          (∑' m : ℕ, Real.exp (-s * (m : ℝ) ^ 2))) :=
      hn.mul_right _
    apply hconst.congr
    intro n
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [← Real.exp_add]
    congr 1
    ring

end
