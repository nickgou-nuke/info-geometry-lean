import InfoGeometry.Basic
import InfoGeometry.ExponentialFamily.Analytic.LogSumExp
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators ENNReal

namespace InfoGeometry.Analytic

open Finset

variable {ι : Type _} [Fintype ι]

/-!
Softmax API wrapper over `InfoGeometry.ExponentialFamily.Analytic.LogSumExp`.

Core partition/weight/moment derivatives are inherited from `LogSumExp`; this
file keeps the value-add packaging into strict finite distributions and
expectation-based mean/variance statements.
-/

/-- Weighted exponential sum (partition function). -/
noncomputable abbrev softmaxPartition (w a : ι → ℝ) (θ : ℝ) : ℝ :=
  logSumExpPartition w a θ

/-- Softmax probability. -/
noncomputable abbrev softmaxProb (w a : ι → ℝ) (θ : ℝ) (i : ι) : ℝ :=
  logSumExpWeight w a θ i

/-- Unnormalized first moment `M₁(θ) = ∑ᵢ wᵢ exp(θ aᵢ) aᵢ`. -/
noncomputable abbrev firstMomentUnnormalized (w a : ι → ℝ) (θ : ℝ) : ℝ :=
  logSumExpMoment1 w a θ

/-- Unnormalized second moment `M₂(θ) = ∑ᵢ wᵢ exp(θ aᵢ) aᵢ²`. -/
noncomputable abbrev secondMomentUnnormalized (w a : ι → ℝ) (θ : ℝ) : ℝ :=
  logSumExpMoment2 w a θ

section Nonempty

variable [Nonempty ι]

lemma softmaxPartition_pos
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    0 < softmaxPartition w a θ := by
  simpa [softmaxPartition] using logSumExp_sum_pos (w := w) (a := a) hw θ

lemma softmaxProb_pos
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) (i : ι) :
    0 < softmaxProb w a θ i := by
  simpa [softmaxProb] using logSumExpWeight_pos (w := w) (a := a) hw θ i

lemma softmaxProb_sum_one
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    ∑ i, softmaxProb w a θ i = 1 := by
  simpa [softmaxProb] using logSumExpWeight_sum_one (w := w) (a := a) hw θ

/-- Pack softmax as a strict finite distribution. -/
noncomputable def softmaxDist
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    InfoGeometry.StrictProbabilityDist ι :=
  by
    classical
    have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ softmaxProb w a θ i := by
      intro i hi
      exact le_of_lt (softmaxProb_pos (w := w) (a := a) hw θ i)
    have hsum : ∑ i, ENNReal.ofReal (softmaxProb w a θ i) = 1 := by
      calc
        ∑ i, ENNReal.ofReal (softmaxProb w a θ i)
            = ENNReal.ofReal (∑ i, softmaxProb w a θ i) := by
                simpa using
                  (ENNReal.ofReal_sum_of_nonneg
                    (s := (Finset.univ : Finset ι))
                    (f := fun i => softmaxProb w a θ i)
                    hnonneg).symm
        _ = ENNReal.ofReal 1 := by
              simp [softmaxProb_sum_one (w := w) (a := a) hw θ]
        _ = 1 := by simp
    exact InfoGeometry.FinProb.of_fintype (fun i => ENNReal.ofReal (softmaxProb w a θ i)) hsum

@[simp] lemma softmaxDist_prob_eq
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) (i : ι) :
    ((softmaxDist (w := w) (a := a) hw θ) i).toReal = softmaxProb w a θ i := by
  have hnonneg : 0 ≤ softmaxProb w a θ i :=
    le_of_lt (softmaxProb_pos (w := w) (a := a) hw θ i)
  simp [softmaxDist, InfoGeometry.FinProb.of_fintype, PMF.ofFintype_apply, hnonneg]

/-- Mean `E_p[a]`. -/
noncomputable def softmaxMean
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) : ℝ :=
  InfoGeometry.expectation (softmaxDist (w := w) (a := a) hw θ) a

/-- Second moment `E_p[a^2]`. -/
noncomputable def softmaxSecondMoment
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) : ℝ :=
  InfoGeometry.expectation (softmaxDist (w := w) (a := a) hw θ) (fun i => (a i) ^ (2 : ℕ))

/-- Variance `E_p[(a - E_p[a])^2]`. -/
noncomputable def softmaxVariance
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) : ℝ :=
  InfoGeometry.expectation (softmaxDist (w := w) (a := a) hw θ)
    (fun i => (a i - softmaxMean (w := w) (a := a) hw θ) ^ (2 : ℕ))

lemma softmaxVariance_nonneg
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    0 ≤ softmaxVariance (w := w) (a := a) hw θ := by
  unfold softmaxVariance InfoGeometry.expectation
  refine Finset.sum_nonneg ?_
  intro i hi
  have hp : 0 ≤ ((softmaxDist (w := w) (a := a) hw θ) i).toReal :=
    ENNReal.toReal_nonneg
  exact mul_nonneg hp (pow_two_nonneg _)

end Nonempty

lemma hasDerivAt_softmaxPartition
    (w a : ι → ℝ) (θ : ℝ) :
    HasDerivAt (softmaxPartition w a) (firstMomentUnnormalized w a θ) θ := by
  simpa [softmaxPartition, firstMomentUnnormalized] using
    hasDerivAt_logSumExpPartition (w := w) (a := a) (θ := θ)

lemma deriv_softmaxPartition
    (w a : ι → ℝ) (θ : ℝ) :
    deriv (softmaxPartition w a) θ = firstMomentUnnormalized w a θ := by
  simpa [softmaxPartition, firstMomentUnnormalized] using
    deriv_logSumExpPartition (w := w) (a := a) (θ := θ)

lemma hasDerivAt_firstMomentUnnormalized
    (w a : ι → ℝ) (θ : ℝ) :
    HasDerivAt (firstMomentUnnormalized w a) (secondMomentUnnormalized w a θ) θ := by
  simpa [firstMomentUnnormalized, secondMomentUnnormalized] using
    hasDerivAt_logSumExpMoment1 (w := w) (a := a) (θ := θ)

lemma deriv_firstMomentUnnormalized
    (w a : ι → ℝ) (θ : ℝ) :
    deriv (firstMomentUnnormalized w a) θ = secondMomentUnnormalized w a θ := by
  simpa [firstMomentUnnormalized, secondMomentUnnormalized] using
    deriv_logSumExpMoment1 (w := w) (a := a) (θ := θ)

/-- `logSumExp w a = log(Z)` with `Z = softmaxPartition`. -/
lemma logSumExp_eq_log_partition (w a : ι → ℝ) :
    logSumExp w a = fun θ => Real.log (softmaxPartition w a θ) := by
  rfl

section Nonempty

variable [Nonempty ι]

/-- First derivative: `(log Z)'(θ) = Z'(θ)/Z(θ) = M₁(θ)/Z(θ)`. -/
lemma deriv_logSumExp_eq_firstMoment_div_partition
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    deriv (logSumExp w a) θ
      = firstMomentUnnormalized w a θ / softmaxPartition w a θ := by
  simpa [firstMomentUnnormalized, softmaxPartition] using
    logSumExp_deriv_eq_ratio (w := w) (a := a) hw θ

lemma softmaxMean_eq_logSumExpMean
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    softmaxMean (w := w) (a := a) hw θ = logSumExpMean w a θ := by
  unfold softmaxMean InfoGeometry.expectation
  simpa [softmaxProb] using (logSumExpMean_eq_weighted_sum (w := w) (a := a) hw θ).symm

/-- `E_p[a] = M₁/Z`. -/
lemma softmaxMean_eq_firstMoment_div_partition
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    softmaxMean (w := w) (a := a) hw θ
      = firstMomentUnnormalized w a θ / softmaxPartition w a θ := by
  rw [softmaxMean_eq_logSumExpMean (w := w) (a := a) hw θ]
  rfl

/-- `E_p[a²]` agrees with the canonical `logSumExp` second moment. -/
lemma softmaxSecondMoment_eq_logSumExpSecondMoment
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    softmaxSecondMoment (w := w) (a := a) hw θ = logSumExpSecondMoment w a θ := by
  unfold softmaxSecondMoment InfoGeometry.expectation
  simpa [softmaxProb] using
    (logSumExpSecondMoment_eq_weighted_sum (w := w) (a := a) hw θ).symm

/-- Normalized second moment equals `M₂/Z`. -/
lemma softmaxSecondMoment_eq_secondMomentUnnormalized_div_partition
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    softmaxSecondMoment (w := w) (a := a) hw θ
      = secondMomentUnnormalized w a θ / softmaxPartition w a θ := by
  rw [softmaxSecondMoment_eq_logSumExpSecondMoment (w := w) (a := a) hw θ]
  rfl

/-- Main first-derivative identity: `deriv(logSumExp) = E_p[a]`. -/
theorem deriv_logSumExp_eq_softmaxMean
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    deriv (logSumExp w a) θ = softmaxMean (w := w) (a := a) hw θ := by
  rw [softmaxMean_eq_logSumExpMean (w := w) (a := a) hw θ]
  simpa using logSumExp_deriv_eq_mean (w := w) (a := a) hw θ

/-- Variance expansion: `Var = E[a²] - (E[a])²`. -/
lemma softmaxVariance_eq_secondMoment_sub_mean_sq
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    softmaxVariance (w := w) (a := a) hw θ
      = softmaxSecondMoment (w := w) (a := a) hw θ
        - (softmaxMean (w := w) (a := a) hw θ) ^ (2 : ℕ) := by
  let p : ι → ℝ := fun i => ((softmaxDist (w := w) (a := a) hw θ) i).toReal
  unfold softmaxVariance softmaxSecondMoment softmaxMean InfoGeometry.expectation
  change
    ∑ i : ι, p i * (a i - (∑ j : ι, p j * a j)) ^ (2 : ℕ)
      =
    (∑ i : ι, p i * (a i) ^ (2 : ℕ)) - (∑ i : ι, p i * a i) ^ (2 : ℕ)
  let m : ℝ := ∑ j : ι, p j * a j
  have hexpand :
      ∑ i : ι,
          p i * (a i - m) ^ (2 : ℕ)
        =
      (∑ i : ι, p i * (a i) ^ (2 : ℕ))
        - 2 * m * (∑ i : ι, p i * a i)
        + m ^ (2 : ℕ) * (∑ i : ι, p i) := by
    calc
      ∑ i : ι,
          p i * (a i - m) ^ (2 : ℕ)
          =
        ∑ i : ι,
          (p i * (a i) ^ (2 : ℕ) - (2 * m) * (p i * a i) + m ^ (2 : ℕ) * p i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ =
        (∑ i : ι, p i * (a i) ^ (2 : ℕ))
          - (2 * m) * (∑ i : ι, p i * a i)
          + m ^ (2 : ℕ) * (∑ i : ι, p i) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hp1 : ∑ i : ι, p i = 1 := by
    simpa [p, softmaxDist_prob_eq] using
      softmaxProb_sum_one (w := w) (a := a) hw θ
  have hm : ∑ i : ι, p i * a i = m := by rfl
  rw [hexpand, hm, hp1]
  ring

/-- Second derivative (Hessian in 1D). -/
noncomputable def softmaxHessian (w a : ι → ℝ) (θ : ℝ) : ℝ :=
  deriv (fun t => deriv (logSumExp w a) t) θ

lemma softmaxHessian_eq_secondMoment_sub_mean_sq
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    softmaxHessian w a θ
      = softmaxSecondMoment (w := w) (a := a) hw θ
        - (softmaxMean (w := w) (a := a) hw θ) ^ (2 : ℕ) := by
  unfold softmaxHessian
  rw [logSumExp_secondDeriv_eq_variance (w := w) (a := a) hw θ]
  rw [logSumExpVariance]
  rw [← softmaxSecondMoment_eq_logSumExpSecondMoment (w := w) (a := a) hw θ]
  rw [← softmaxMean_eq_logSumExpMean (w := w) (a := a) hw θ]

/-- Main second-derivative identity: `deriv²(logSumExp) = Var_p[a]`. -/
theorem deriv2_logSumExp_eq_softmaxVariance
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    deriv (fun t => deriv (logSumExp w a) t) θ
      = softmaxVariance (w := w) (a := a) hw θ := by
  have hH :
      softmaxHessian w a θ
        = softmaxSecondMoment (w := w) (a := a) hw θ
          - (softmaxMean (w := w) (a := a) hw θ) ^ (2 : ℕ) :=
    softmaxHessian_eq_secondMoment_sub_mean_sq (w := w) (a := a) hw θ
  have hV :
      softmaxVariance (w := w) (a := a) hw θ
        = softmaxSecondMoment (w := w) (a := a) hw θ
          - (softmaxMean (w := w) (a := a) hw θ) ^ (2 : ℕ) :=
    softmaxVariance_eq_secondMoment_sub_mean_sq (w := w) (a := a) hw θ
  simpa [softmaxHessian] using (hH.trans hV.symm)

end Nonempty

end InfoGeometry.Analytic
