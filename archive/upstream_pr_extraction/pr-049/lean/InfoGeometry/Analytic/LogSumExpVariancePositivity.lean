import InfoGeometry.Analytic.LogSumExp

noncomputable section
open scoped BigOperators

namespace InfoGeometry.Analytic

theorem logSumExpVariance_nonneg
    {ι : Type _} [Fintype ι] [Nonempty ι]
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    0 ≤ logSumExpVariance w a θ := by
  rw [logSumExpVariance,
    logSumExpSecondMoment_eq_weighted_sum w a hw θ,
    logSumExpMean_eq_weighted_sum w a hw θ]
  have hsum : ∑ i, logSumExpWeight w a θ i = 1 :=
    logSumExpWeight_sum_one w a hw θ
  let m : ℝ := ∑ i, logSumExpWeight w a θ i * a i
  have hcenter :
      (∑ i, logSumExpWeight w a θ i * a i ^ (2 : ℕ)) - m ^ (2 : ℕ) =
        ∑ i, logSumExpWeight w a θ i * (a i - m) ^ (2 : ℕ) := by
    calc
      (∑ i, logSumExpWeight w a θ i * a i ^ (2 : ℕ)) - m ^ (2 : ℕ) =
          (∑ i, logSumExpWeight w a θ i * a i ^ (2 : ℕ)) -
            (∑ i, logSumExpWeight w a θ i) * m ^ (2 : ℕ) := by
              rw [hsum]
              ring
      _ = ∑ i, (logSumExpWeight w a θ i * a i ^ (2 : ℕ) -
            2 * m * (logSumExpWeight w a θ i * a i) +
            m ^ (2 : ℕ) * logSumExpWeight w a θ i) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              rw [← Finset.mul_sum, ← Finset.mul_sum]
              dsimp [m]
              rw [hsum]
              ring
      _ = ∑ i, logSumExpWeight w a θ i * (a i - m) ^ (2 : ℕ) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
  rw [hcenter]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (le_of_lt (logSumExpWeight_pos w a hw θ i)) (sq_nonneg _)

theorem logSumExpVariance_pos_of_exists_ne
    {ι : Type _} [Fintype ι] [Nonempty ι]
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ)
    (hne : ∃ i j, a i ≠ a j) :
    0 < logSumExpVariance w a θ := by
  by_contra hnot
  have hzero : logSumExpVariance w a θ = 0 :=
    le_antisymm (le_of_not_gt hnot) (logSumExpVariance_nonneg w a hw θ)
  rw [logSumExpVariance,
    logSumExpSecondMoment_eq_weighted_sum w a hw θ,
    logSumExpMean_eq_weighted_sum w a hw θ] at hzero
  have hsum : ∑ i, logSumExpWeight w a θ i = 1 :=
    logSumExpWeight_sum_one w a hw θ
  let m : ℝ := ∑ i, logSumExpWeight w a θ i * a i
  have hcenter :
      (∑ i, logSumExpWeight w a θ i * a i ^ (2 : ℕ)) - m ^ (2 : ℕ) =
        ∑ i, logSumExpWeight w a θ i * (a i - m) ^ (2 : ℕ) := by
    calc
      (∑ i, logSumExpWeight w a θ i * a i ^ (2 : ℕ)) - m ^ (2 : ℕ) =
          (∑ i, logSumExpWeight w a θ i * a i ^ (2 : ℕ)) -
            (∑ i, logSumExpWeight w a θ i) * m ^ (2 : ℕ) := by rw [hsum]; ring
      _ = ∑ i, (logSumExpWeight w a θ i * a i ^ (2 : ℕ) -
            2 * m * (logSumExpWeight w a θ i * a i) +
            m ^ (2 : ℕ) * logSumExpWeight w a θ i) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              rw [← Finset.mul_sum, ← Finset.mul_sum]
              dsimp [m]
              rw [hsum]
              ring
      _ = ∑ i, logSumExpWeight w a θ i * (a i - m) ^ (2 : ℕ) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
  have hsq : ∀ i, (a i - m) ^ (2 : ℕ) = 0 := by
    intro i
    have hsumzero : ∑ i, logSumExpWeight w a θ i * (a i - m) ^ (2 : ℕ) = 0 := by
      rw [← hcenter]
      exact hzero
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (le_of_lt (logSumExpWeight_pos w a hw θ j)) (sq_nonneg _))).mp hsumzero i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hi).resolve_left (ne_of_gt (logSumExpWeight_pos w a hw θ i))
  obtain ⟨i, j, hij⟩ := hne
  have hi : a i = m := sub_eq_zero.mp (sq_eq_zero_iff.mp (hsq i))
  have hj : a j = m := sub_eq_zero.mp (sq_eq_zero_iff.mp (hsq j))
  exact hij (hi.trans hj.symm)

theorem logSumExpVariance_eq_zero_of_forall_eq
    {ι : Type _} [Fintype ι] [Nonempty ι]
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ c : ℝ)
    (ha : ∀ i, a i = c) :
    logSumExpVariance w a θ = 0 := by
  rw [logSumExpVariance,
    logSumExpSecondMoment_eq_weighted_sum w a hw θ,
    logSumExpMean_eq_weighted_sum w a hw θ]
  have hsum : ∑ i, logSumExpWeight w a θ i = 1 :=
    logSumExpWeight_sum_one w a hw θ
  simp_rw [ha]
  have h₁ : (∑ i, logSumExpWeight w a θ i * c ^ 2) =
      (∑ i, logSumExpWeight w a θ i) * c ^ 2 := by
    rw [Finset.sum_mul]
  have h₂ : (∑ i, logSumExpWeight w a θ i * c) =
      (∑ i, logSumExpWeight w a θ i) * c := by
    rw [Finset.sum_mul]
  rw [h₁, h₂, hsum]
  ring

end InfoGeometry.Analytic
