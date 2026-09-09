import InfoGeometry.Projective.ExpectationRatioMetric
import InfoGeometry.Analytic.LogSumExp
import InfoGeometry.Routing.FiniteSoftmax

/-!
# Finite attention as an exponential tilt of a positive reference ray

The positive reference weights are explicit. Softmax is the unit-reference
case. Scores are not assigned a physical energy or time interpretation.
The log-partition derivative has the positive score-mean sign for exp(beta*s).
-/

noncomputable section
namespace InfoGeometry.Projective.GibbsRayGeometry

open InfoGeometry
open InfoGeometry.Analytic
open ExpectationRatioMetric
open scoped BigOperators

variable {ι : Type*}

def tilt (w : Weight ι) (s : ι → ℝ) (β : ℝ) : Weight ι :=
  ⟨fun i => w i * Real.exp (β * s i), fun i => mul_pos (w.pos i) (Real.exp_pos _)⟩

def gibbsRay (w : Weight ι) (s : ι → ℝ) (β : ℝ) : Ray ι := ray (tilt w s β)

/-- Common logit shifts change only the homogeneous representative. -/
theorem tilt_shift (w : Weight ι) (s : ι → ℝ) (β c : ℝ) :
    tilt w (fun i => s i + c) β =
      PositiveMeasure.scale (Real.exp (β*c)) (Real.exp_pos _) (tilt w s β) := by
  apply PositiveMeasure.ext
  funext i
  dsimp [tilt, PositiveMeasure.scale]
  rw [mul_add, Real.exp_add]
  ring

@[simp] theorem gibbsRay_shift (w : Weight ι) (s : ι → ℝ) (β c : ℝ) :
    gibbsRay w (fun i => s i + c) β = gibbsRay w s β := by
  unfold gibbsRay
  rw [tilt_shift, ray_scale]

theorem gibbsRay_reference_scale (w : Weight ι) (s : ι → ℝ) (β c : ℝ) (hc : 0 < c) :
    gibbsRay (PositiveMeasure.scale c hc w) s β = gibbsRay w s β := by
  have h : tilt (PositiveMeasure.scale c hc w) s β =
      PositiveMeasure.scale c hc (tilt w s β) := by
    apply PositiveMeasure.ext
    funext i
    dsimp [tilt, PositiveMeasure.scale]
    ring
  unfold gibbsRay
  rw [h, ray_scale]

/-- Score contrasts, rather than absolute scores, determine relative weights. -/
theorem gibbsRay_logCoordinates (w : Weight ι) (s : ι → ℝ) (β : ℝ) (i j : ι) :
    logCoordinates (gibbsRay w s β) (i,j) =
      Real.log (w i / w j) + β * (s i - s j) := by
  rw [gibbsRay, logCoordinates_ray]
  dsimp [tilt]
  rw [Real.log_mul (w.pos i).ne' (Real.exp_ne_zero _),
    Real.log_mul (w.pos j).ne' (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp, Real.log_div (w.pos i).ne' (w.pos j).ne']
  ring

theorem gibbsRay_equal_iff_score_shift [Nonempty ι]
    (w : Weight ι) (s t : ι → ℝ) (β : ℝ) (hβ : β ≠ 0) :
    gibbsRay w s β = gibbsRay w t β ↔ ∃ c : ℝ, ∀ i, s i = t i + c := by
  classical
  constructor
  · intro h
    let j : ι := Classical.choice inferInstance
    refine ⟨s j - t j, ?_⟩
    intro i
    have hij := congrArg (fun q => logCoordinates q (i,j)) h
    change logCoordinates (gibbsRay w s β) (i,j) =
      logCoordinates (gibbsRay w t β) (i,j) at hij
    rw [gibbsRay_logCoordinates, gibbsRay_logCoordinates] at hij
    have he : β * (s i - s j) = β * (t i - t j) := add_left_cancel hij
    have hc := mul_left_cancel₀ hβ he
    linarith
  · rintro ⟨c, hc⟩
    have hs : s = fun i => t i + c := funext hc
    rw [hs, gibbsRay_shift]

section Finite
variable [Fintype ι] [Nonempty ι]

/-- Exact Hilbert/log-ratio distance between two score rows at a fixed reference. -/
theorem gibbsRay_distance (w : Weight ι) (s t : ι → ℝ) (β : ℝ) :
    projectiveDistance (gibbsRay w s β) (gibbsRay w t β) =
      ‖fun ij : ι × ι => β * ((s ij.1 - t ij.1) - (s ij.2 - t ij.2))‖ := by
  rw [projectiveDistance_eq_norm]
  congr 1
  funext ij
  rcases ij with ⟨i,j⟩
  change logCoordinates (gibbsRay w s β) (i,j) -
      logCoordinates (gibbsRay w t β) (i,j) = _
  rw [gibbsRay_logCoordinates, gibbsRay_logCoordinates]
  ring

def unitReference : Weight ι := ⟨fun _ => 1, fun _ => zero_lt_one⟩

theorem unitReference_probability_eq_softmax (s : ι → ℝ) (τ : ℝ) (i : ι) :
    PositiveMeasure.normalize (tilt (unitReference (ι := ι)) s (1/τ)) i =
      Routing.FiniteSoftmax.weight s τ i := by
  simp [PositiveMeasure.normalize_apply, tilt, unitReference, PositiveMeasure.Z,
    Routing.FiniteSoftmax.weight, Routing.FiniteSoftmax.partitionZ, div_eq_mul_inv, mul_comm]

/-- The existing analytic log-partition, not a second exponential-family owner. -/
def logPartition (w : Weight ι) (s : ι → ℝ) : ℝ → ℝ := logSumExp (fun i => w i) s

theorem logPartition_deriv (w : Weight ι) (s : ι → ℝ) (β : ℝ) :
    deriv (logPartition w s) β = rayMean (gibbsRay w s β) s := by
  change deriv (logSumExp (fun i => w i) s) β = mean (tilt w s β) s
  rw [logSumExp_deriv_eq_ratio (fun i => w i) s w.pos β]
  rfl

/-- The derivative is minus the mean of E=-s, not minus the mean score. -/
theorem logPartition_deriv_energy_convention (w : Weight ι) (s : ι → ℝ) (β : ℝ) :
    deriv (logPartition w s) β = -rayMean (gibbsRay w s β) (fun i => -s i) := by
  rw [logPartition_deriv]
  have h := rayMean_smul (gibbsRay w s β) (-1) s
  simp only [neg_one_mul] at h
  rw [h, neg_neg]

theorem logPartition_secondDeriv_centered (w : Weight ι) (s : ι → ℝ) (β : ℝ) :
    deriv (fun b => deriv (logPartition w s) b) β =
      ∑ i, PositiveMeasure.normalize (tilt w s β) i *
        (s i - rayMean (gibbsRay w s β) s)^2 := by
  change deriv (fun b => deriv (logSumExp (fun i => w i) s) b) β = _
  rw [logSumExp_secondDeriv_eq_variance (fun i => w i) s w.pos β,
    logSumExpVariance_eq_centered (fun i => w i) s w.pos β]
  have hp (i : ι) : logSumExpWeight (fun i => w i) s β i =
      PositiveMeasure.normalize (tilt w s β) i := rfl
  simp only [hp, gibbsRay, rayMean_ray, mean_eq_sum]

theorem logPartition_secondDeriv_nonneg (w : Weight ι) (s : ι → ℝ) (β : ℝ) :
    0 ≤ deriv (fun b => deriv (logPartition w s) b) β := by
  rw [logPartition_secondDeriv_centered]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg ((PositiveMeasure.normalize (tilt w s β)).pos i).le (sq_nonneg _)

/-- Log density relative to the explicitly retained reference weights. -/
theorem log_relative_probability (w : Weight ι) (s : ι → ℝ) (β : ℝ) (i : ι) :
    Real.log (PositiveMeasure.normalize (tilt w s β) i / w i) =
      β * s i - logPartition w s β := by
  rw [Real.log_div ((PositiveMeasure.normalize (tilt w s β)).pos i).ne' (w.pos i).ne',
    PositiveMeasure.normalize_apply,
    Real.log_div ((tilt w s β).pos i).ne' (PositiveMeasure.Z_ne_zero _)]
  change Real.log (w i * Real.exp (β*s i)) - Real.log (PositiveMeasure.Z (tilt w s β)) -
    Real.log (w i) = _
  rw [Real.log_mul (w.pos i).ne' (Real.exp_ne_zero _), Real.log_exp]
  change Real.log (w i) + β*s i - logPartition w s β - Real.log (w i) = _
  ring

def referenceEntropy (w : Weight ι) (s : ι → ℝ) (β : ℝ) : ℝ :=
  -∑ i, PositiveMeasure.normalize (tilt w s β) i *
    Real.log (PositiveMeasure.normalize (tilt w s β) i / w i)

theorem referenceEntropy_eq (w : Weight ι) (s : ι → ℝ) (β : ℝ) :
    referenceEntropy w s β = logPartition w s β - β * rayMean (gibbsRay w s β) s := by
  unfold referenceEntropy
  simp_rw [log_relative_probability, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hmean : ∑ i, PositiveMeasure.normalize (tilt w s β) i * (β * s i) =
      β * rayMean (gibbsRay w s β) s := by
    rw [gibbsRay, rayMean_ray, mean_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hmean, ← Finset.sum_mul]
  have hsum : ∑ i, PositiveMeasure.normalize (tilt w s β) i = 1 :=
    PositiveMeasure.Z_normalize _
  rw [hsum]
  ring

/-- Ordinary attention-value contraction is an expectation in the positive ray. -/
theorem attention_value_as_rayMean (s v : ι → ℝ) (τ : ℝ) :
    (∑ i, Routing.FiniteSoftmax.weight s τ i * v i) =
      rayMean (gibbsRay (unitReference (ι := ι)) s (1/τ)) v := by
  rw [gibbsRay, rayMean_ray, mean_eq_sum]
  simp_rw [unitReference_probability_eq_softmax]

end Finite
end InfoGeometry.Projective.GibbsRayGeometry
