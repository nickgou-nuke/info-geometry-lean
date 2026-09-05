import InfoGeometry.InformationGeometry.ItakuraSaitoBregmanBridge
import Mathlib

/-!
# Finite centered log-ratio geometry and a specified barrier relaxation

This uses the repository's `isDivergence` and `bregmanNegLog`. The centered
log-ratio identity is on positive coordinate data, not on an alleged partial
trace of a chiral direct sum. The dissipative result is proved for the
explicit flow `y + exp(-t) * (x0-y)`; it is not inferred from Clifford grades,
a stochastic branching generator, or the name Massieu.
-/

noncomputable section

namespace InfoGeometry.InformationGeometry.FiniteChannelLogRatioBarrier

open InfoGeometry.InformationGeometry.ItakuraSaito

variable {ι : Type*} [Fintype ι]

/-- Subtract the arithmetic mean in logarithmic coordinates. -/
def centered (u : ι → ℝ) (i : ι) : ℝ :=
  u i - (∑ j, u j) / Fintype.card ι

/-- Centered logarithmic coordinates of a positive representative. -/
def clr (x : ι → ℝ) : ι → ℝ := centered (fun i => Real.log (x i))

section Nonempty

variable [Nonempty ι]

lemma card_cast_ne_zero : (Fintype.card ι : ℝ) ≠ 0 := by
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)

theorem sum_centered (u : ι → ℝ) : (∑ i, centered u i) = 0 := by
  simp only [centered, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp [card_cast_ne_zero (ι := ι)] <;> ring

theorem centered_difference (u : ι → ℝ) (i j : ι) :
    centered u i - centered u j = u i - u j := by
  unfold centered
  ring

theorem centered_sub (u v : ι → ℝ) (i : ι) :
    centered (fun j => u j - v j) i = centered u i - centered v i := by
  simp only [centered, Finset.sum_sub_distrib]
  ring

theorem centered_add_constant (u : ι → ℝ) (c : ℝ) :
    centered (fun i => c + u i) = centered u := by
  funext i
  simp only [centered, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp [card_cast_ne_zero (ι := ι)] <;> ring

/-- The finite pairwise quadratic identity which supplies the factor `1/(2n)`. -/
theorem pairwise_squares_of_sum_zero (u : ι → ℝ) (hu : ∑ i, u i = 0) :
    (∑ i, ∑ j, (u i - u j) ^ 2) =
      2 * (Fintype.card ι : ℝ) * ∑ i, (u i) ^ 2 := by
  have inner (i : ι) :
      (∑ j, (u i - u j) ^ 2) =
        (Fintype.card ι : ℝ) * (u i) ^ 2 -
          2 * u i * (∑ j, u j) + ∑ j, (u j) ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] <;> ring
  simp_rw [inner, hu, mul_zero, sub_zero]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum] <;> ring

theorem centered_pairwise_squares (u : ι → ℝ) :
    (∑ i, (centered u i) ^ 2) =
      (∑ i, ∑ j, (u i - u j) ^ 2) / (2 * (Fintype.card ι : ℝ)) := by
  have h := pairwise_squares_of_sum_zero (centered u) (sum_centered u)
  simp only [centered_difference] at h
  rw [h]
  field_simp [card_cast_ne_zero (ι := ι)] <;> ring

/-- Common rescaling changes logarithms by a constant, removed by centering. -/
theorem clr_scale (x : ι → ℝ) (hx : ∀ i, 0 < x i) (c : ℝ) (hc : 0 < c) :
    clr (fun i => c * x i) = clr x := by
  have hlog : (fun i => Real.log (c * x i)) =
      (fun i => Real.log c + Real.log (x i)) := by
    funext i
    exact Real.log_mul hc.ne' (hx i).ne'
  unfold clr
  rw [hlog, centered_add_constant]

/-- Aitchison's pairwise formula is the Euclidean square of the centered logs.
No normalization of the positive representatives is needed. -/
theorem clr_pairwise_log_ratios (x y : ι → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    (∑ i, (clr x i - clr y i) ^ 2) =
      (1 / (2 * (Fintype.card ι : ℝ))) *
        ∑ i, ∑ j, (Real.log (x i / x j) - Real.log (y i / y j)) ^ 2 := by
  have h := centered_pairwise_squares (fun i => Real.log (x i) - Real.log (y i))
  simp only [centered_sub] at h
  change (∑ i, (clr x i - clr y i) ^ 2) = _ at h
  have hpair (i j : ι) :
      (Real.log (x i) - Real.log (y i)) -
          (Real.log (x j) - Real.log (y j)) =
        Real.log (x i / x j) - Real.log (y i / y j) := by
    rw [Real.log_div (hx i).ne' (hx j).ne', Real.log_div (hy i).ne' (hy j).ne']
    ring
  simp_rw [hpair] at h
  rw [h]
  ring

end Nonempty

/-- The existing scalar logarithmic-barrier divergence summed over channels. -/
def channelIS (x y : ι → ℝ) : ℝ := ∑ i, isDivergence (x i) (y i)

theorem channelIS_nonneg (x y : ι → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) : 0 ≤ channelIS x y := by
  exact Finset.sum_nonneg (fun i _ => isDivergence_nonneg (x i) (y i) (hx i) (hy i))

theorem channelIS_is_bregman (x y : ι → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    channelIS x y = ∑ i, bregmanNegLog (x i) (y i) := by
  apply Finset.sum_congr rfl
  intro i _
  exact (bregmanNegLog_eq_isDivergence (x i) (y i) (hx i) (hy i)).symm

/-- A concrete relaxation law, not a consequence of a chosen algebraic carrier. -/
def relaxation (x0 y : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  y i + (x0 i - y i) * Real.exp (-t)

theorem relaxation_pos (x0 y : ι → ℝ)
    (hx0 : ∀ i, 0 < x0 i) (hy : ∀ i, 0 < y i)
    {t : ℝ} (ht : 0 ≤ t) (i : ι) : 0 < relaxation x0 y t i := by
  have ha : 0 < Real.exp (-t) := Real.exp_pos _
  have hb : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have h1 : 0 ≤ (1 - Real.exp (-t)) * y i := mul_nonneg (sub_nonneg.mpr hb) (hy i).le
  have h2 : 0 < Real.exp (-t) * x0 i := mul_pos ha (hx0 i)
  unfold relaxation
  nlinarith

theorem hasDerivAt_relaxation (x0 y : ι → ℝ) (t : ℝ) (i : ι) :
    HasDerivAt (fun s => relaxation x0 y s i) (y i - relaxation x0 y t i) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hd := (he.const_mul (x0 i - y i)).const_add (y i)
  convert hd using 1 <;> dsimp [relaxation] <;> ring

/-- Genuine derivative of the existing scalar IS function in its first argument. -/
theorem hasDerivAt_isDivergence_left {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    HasDerivAt (fun u => isDivergence u y) (1 / y - 1 / x) x := by
  have hq : HasDerivAt (fun u : ℝ => u / y) (1 / y) x :=
    (hasDerivAt_id x).div_const y
  have hl := (Real.hasDerivAt_log (div_ne_zero hx hy)).comp x hq
  have hd := (hq.sub hl).sub_const 1
  convert hd using 1 <;> dsimp [isDivergence] <;> field_simp [hx, hy] <;> ring

/-- Exact decay identity along the explicit positive relaxation. -/
theorem hasDerivAt_channelIS_relaxation (x0 y : ι → ℝ)
    (hx0 : ∀ i, 0 < x0 i) (hy : ∀ i, 0 < y i)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => channelIS (relaxation x0 y s) y)
      (-(∑ i, (relaxation x0 y t i - y i) ^ 2 /
        (relaxation x0 y t i * y i))) t := by
  have hi (i : ι) :
      HasDerivAt (fun s => isDivergence (relaxation x0 y s i) (y i))
        (-((relaxation x0 y t i - y i) ^ 2 /
          (relaxation x0 y t i * y i))) t := by
    have hx := (relaxation_pos x0 y hx0 hy ht i).ne'
    have hd := (hasDerivAt_isDivergence_left hx (hy i).ne').comp t
      (hasDerivAt_relaxation x0 y t i)
    convert hd using 1 <;> field_simp [hx, (hy i).ne'] <;> ring
  simpa only [channelIS, Finset.sum_apply, Finset.sum_neg_distrib] using
    (HasDerivAt.sum (u := Finset.univ) (fun i _ => hi i))

theorem deriv_channelIS_relaxation_nonpos (x0 y : ι → ℝ)
    (hx0 : ∀ i, 0 < x0 i) (hy : ∀ i, 0 < y i)
    {t : ℝ} (ht : 0 ≤ t) :
    deriv (fun s => channelIS (relaxation x0 y s) y) t ≤ 0 := by
  rw [(hasDerivAt_channelIS_relaxation x0 y hx0 hy ht).deriv]
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) (mul_pos (relaxation_pos x0 y hx0 hy ht i) (hy i)).le

/-- The coefficient in the attachment is exactly `1/(2*32)`. -/
theorem clr_32_pairwise_log_ratios (x y : Finset (Fin 5) → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    (∑ i, (clr x i - clr y i) ^ 2) =
      (1 / 64 : ℝ) * ∑ i, ∑ j,
        (Real.log (x i / x j) - Real.log (y i / y j)) ^ 2 := by
  have h := clr_pairwise_log_ratios x y hx hy
  norm_num [Fintype.card_finset] at h
  exact h

end InfoGeometry.InformationGeometry.FiniteChannelLogRatioBarrier
