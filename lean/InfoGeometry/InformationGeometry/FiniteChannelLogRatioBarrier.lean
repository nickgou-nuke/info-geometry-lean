import InfoGeometry.InformationGeometry.ItakuraSaitoBregmanBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib

/-! Finite centered log-ratio identities and an explicit positive relaxation.
These are readouts on positive channels; they do not add a physical
interpretation to the underlying operator carriers. -/
noncomputable section
namespace InfoGeometry.InformationGeometry.FiniteChannelLogRatioBarrier

open InfoGeometry.InformationGeometry.ItakuraSaito
variable {ι : Type*} [Fintype ι]

def centered (u : ι → ℝ) (i : ι) : ℝ :=
  u i - (∑ j, u j) / Fintype.card ι

def clr (x : ι → ℝ) : ι → ℝ := centered (fun i => Real.log (x i))

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

theorem centered_add_constant (u : ι → ℝ) (c : ℝ) :
    centered (fun i => c + u i) = centered u := by
  funext i
  simp only [centered, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp [card_cast_ne_zero (ι := ι)] <;> ring

theorem clr_scale (x : ι → ℝ) (hx : ∀ i, 0 < x i) (c : ℝ) (hc : 0 < c) :
    clr (fun i => c * x i) = clr x := by
  have hlog : (fun i => Real.log (c * x i)) =
      (fun i => Real.log c + Real.log (x i)) := by
    funext i
    exact Real.log_mul hc.ne' (hx i).ne'
  unfold clr
  rw [hlog, centered_add_constant]

def channelIS (x y : ι → ℝ) : ℝ := ∑ i, isDivergence (x i) (y i)

theorem channelIS_nonneg (x y : ι → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) : 0 ≤ channelIS x y := by
  exact Finset.sum_nonneg (fun i _ => isDivergence_nonneg (x i) (y i) (hx i) (hy i))

def relaxation (x₀ y : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  y i + (x₀ i - y i) * Real.exp (-t)

theorem relaxation_pos (x₀ y : ι → ℝ)
    (hx₀ : ∀ i, 0 < x₀ i) (hy : ∀ i, 0 < y i)
    {t : ℝ} (ht : 0 ≤ t) (i : ι) : 0 < relaxation x₀ y t i := by
  have he : 0 < Real.exp (-t) := Real.exp_pos _
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  unfold relaxation
  nlinarith [mul_nonneg (sub_nonneg.mpr he1) (hy i).le,
    mul_pos he (hx₀ i)]

theorem hasDerivAt_relaxation (x₀ y : ι → ℝ) (t : ℝ) (i : ι) :
    HasDerivAt (fun s => relaxation x₀ y s i) (y i - relaxation x₀ y t i) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  convert ((he.const_mul (x₀ i - y i)).const_add (y i)) using 1 <;>
    dsimp [relaxation] <;> ring

end InfoGeometry.InformationGeometry.FiniteChannelLogRatioBarrier
