import InfoGeometry.Basic
import InfoGeometry.Analytic.LogSumExp

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace InfoGeometry.Analytic

open Finset

variable {ι : Type _} [Fintype ι]

/-!
Softmax from weights `w` and slopes `a`:

`Z(θ)   := ∑ᵢ wᵢ exp(θ aᵢ)`
`pᵢ(θ)  := wᵢ exp(θ aᵢ) / Z(θ)`

Then:
`(log Z)'   = E_p[a]`
`(log Z)''  = Var_p[a]`
-/

/-- Weighted exponential sum (partition function). -/
noncomputable def softmaxPartition (w a : ι → ℝ) (θ : ℝ) : ℝ :=
  ∑ i, w i * Real.exp (θ * a i)

/-- Softmax probability. -/
noncomputable def softmaxProb (w a : ι → ℝ) (θ : ℝ) (i : ι) : ℝ :=
  w i * Real.exp (θ * a i) / softmaxPartition w a θ

section Nonempty

variable [Nonempty ι]

lemma softmaxPartition_pos
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    0 < softmaxPartition w a θ := by
  simpa [softmaxPartition] using logSumExp_sum_pos (w := w) (a := a) hw θ

lemma softmaxProb_pos
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) (i : ι) :
    0 < softmaxProb w a θ i := by
  unfold softmaxProb
  have hZpos := softmaxPartition_pos (w := w) (a := a) hw θ
  exact div_pos (mul_pos (hw i) (Real.exp_pos _)) hZpos

lemma softmaxProb_sum_one
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    ∑ i, softmaxProb w a θ i = 1 := by
  unfold softmaxProb softmaxPartition
  have hZne :
      (∑ i : ι, w i * Real.exp (θ * a i)) ≠ 0 :=
    ne_of_gt (logSumExp_sum_pos (w := w) (a := a) hw θ)
  calc
    ∑ i : ι, w i * Real.exp (θ * a i) / ∑ j : ι, w j * Real.exp (θ * a j)
        =
      (∑ i : ι, w i * Real.exp (θ * a i)) / ∑ j : ι, w j * Real.exp (θ * a j) := by
        symm
        simpa using
          (Finset.sum_div
            (s := (Finset.univ : Finset ι))
            (f := fun i => w i * Real.exp (θ * a i))
            (a := ∑ j : ι, w j * Real.exp (θ * a j)))
    _ = 1 := by
        exact div_self hZne

/-- Pack softmax as a strict finite distribution. -/
noncomputable def softmaxDist
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
  InfoGeometry.StrictProbabilityDist ι :=
  InfoGeometry.FinProb.of_fintype
    (fun i => ENNReal.ofReal (softmaxProb w a θ i)) (by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sum_of_nonneg]
      · simpa using softmaxProb_sum_one (w := w) (a := a) hw θ
      · intro i hi
        exact le_of_lt (softmaxProb_pos (w := w) (a := a) hw θ i))

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

/-! Derivative kernels (unnormalized moments). -/

/-- Unnormalized first moment `M₁(θ) = ∑ᵢ wᵢ exp(θ aᵢ) aᵢ`. -/
noncomputable def firstMomentUnnormalized (w a : ι → ℝ) (θ : ℝ) : ℝ :=
  ∑ i, w i * Real.exp (θ * a i) * a i

/-- Unnormalized second moment `M₂(θ) = ∑ᵢ wᵢ exp(θ aᵢ) aᵢ²`. -/
noncomputable def secondMomentUnnormalized (w a : ι → ℝ) (θ : ℝ) : ℝ :=
  ∑ i, w i * Real.exp (θ * a i) * (a i) ^ (2 : ℕ)

omit [Fintype ι] in
lemma hasDerivAt_exp_mul (c θ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (t * c))
      (Real.exp (θ * c) * c) θ := by
  have hlin : HasDerivAt (fun t : ℝ => t * c) c θ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_id' θ).mul_const c
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (Real.hasDerivAt_exp (θ * c)).comp θ hlin

omit [Fintype ι] in
lemma hasDerivAt_partitionTerm (w a : ι → ℝ) (θ : ℝ) (i : ι) :
    HasDerivAt
      (fun t : ℝ => w i * Real.exp (t * a i))
      (w i * Real.exp (θ * a i) * a i)
      θ := by
  have h := (hasDerivAt_exp_mul (c := a i) (θ := θ)).const_mul (w i)
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- `Z'(θ) = M₁(θ)`. -/
lemma hasDerivAt_softmaxPartition
    (w a : ι → ℝ) (θ : ℝ) :
    HasDerivAt (softmaxPartition w a) (firstMomentUnnormalized w a θ) θ := by
  classical
  have hsum :
      HasDerivAt
        (fun t : ℝ => ∑ i : ι, w i * Real.exp (t * a i))
        (∑ i : ι, w i * Real.exp (θ * a i) * a i)
        θ := by
    simpa using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset ι))
        (fun i _hi => hasDerivAt_partitionTerm (w := w) (a := a) θ i))
  unfold softmaxPartition firstMomentUnnormalized
  simpa [mul_assoc] using hsum

lemma deriv_softmaxPartition
    (w a : ι → ℝ) (θ : ℝ) :
    deriv (softmaxPartition w a) θ = firstMomentUnnormalized w a θ :=
  (hasDerivAt_softmaxPartition (w := w) (a := a) θ).deriv

omit [Fintype ι] in
lemma hasDerivAt_firstMomentTerm (w a : ι → ℝ) (θ : ℝ) (i : ι) :
    HasDerivAt
      (fun t : ℝ => w i * Real.exp (t * a i) * a i)
      (w i * Real.exp (θ * a i) * (a i) ^ (2 : ℕ))
      θ := by
  have hExp := hasDerivAt_exp_mul (c := a i) (θ := θ)
  have h := hExp.const_mul (w i * a i)
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using h

/-- `M₁'(θ) = M₂(θ)`. -/
lemma hasDerivAt_firstMomentUnnormalized
    (w a : ι → ℝ) (θ : ℝ) :
    HasDerivAt (firstMomentUnnormalized w a) (secondMomentUnnormalized w a θ) θ := by
  classical
  have hsum :
      HasDerivAt
        (fun t : ℝ => ∑ i : ι, w i * Real.exp (t * a i) * a i)
        (∑ i : ι, w i * Real.exp (θ * a i) * (a i) ^ (2 : ℕ))
        θ := by
    simpa using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset ι))
        (fun i _hi => hasDerivAt_firstMomentTerm (w := w) (a := a) θ i))
  unfold firstMomentUnnormalized secondMomentUnnormalized
  simpa [mul_assoc] using hsum

lemma deriv_firstMomentUnnormalized
    (w a : ι → ℝ) (θ : ℝ) :
    deriv (firstMomentUnnormalized w a) θ = secondMomentUnnormalized w a θ :=
  (hasDerivAt_firstMomentUnnormalized (w := w) (a := a) θ).deriv

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
  have hdiff : DifferentiableAt ℝ (softmaxPartition w a) θ :=
    (hasDerivAt_softmaxPartition (w := w) (a := a) θ).differentiableAt
  have hne : softmaxPartition w a θ ≠ 0 :=
    ne_of_gt (softmaxPartition_pos (w := w) (a := a) hw θ)
  unfold logSumExp
  simpa [softmaxPartition] using
    (by
      calc
        deriv (fun t => Real.log (softmaxPartition w a t)) θ
            = deriv (softmaxPartition w a) θ / softmaxPartition w a θ := by
                simpa using (deriv.log (f := softmaxPartition w a) hdiff hne)
        _ = firstMomentUnnormalized w a θ / softmaxPartition w a θ := by
                rw [deriv_softmaxPartition (w := w) (a := a) θ])

/-- `E_p[a] = M₁/Z`. -/
lemma softmaxMean_eq_firstMoment_div_partition
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    softmaxMean (w := w) (a := a) hw θ
      = firstMomentUnnormalized w a θ / softmaxPartition w a θ := by
  unfold softmaxMean InfoGeometry.expectation softmaxDist
  simp only [InfoGeometry.FinProb.of_fintype, PMF.ofFintype_apply]
  have htoReal : ∀ i : ι, (ENNReal.ofReal (softmaxProb w a θ i)).toReal =
      softmaxProb w a θ i := by
    intro i
    rw [ENNReal.toReal_ofReal (le_of_lt (softmaxProb_pos w a hw θ i))]
  simp_rw [htoReal]
  simp [softmaxProb, firstMomentUnnormalized, softmaxPartition] at *
  have hZne : softmaxPartition w a θ ≠ 0 :=
    ne_of_gt (softmaxPartition_pos (w := w) (a := a) hw θ)
  calc
    ∑ i : ι, (w i * Real.exp (θ * a i) / softmaxPartition w a θ) * a i
        =
      ∑ i : ι, (w i * Real.exp (θ * a i) * a i) / softmaxPartition w a θ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        field_simp [hZne]
    _ =
      (∑ i : ι, w i * Real.exp (θ * a i) * a i) / softmaxPartition w a θ := by
        symm
        simpa using
          (Finset.sum_div
            (s := (Finset.univ : Finset ι))
            (f := fun i => w i * Real.exp (θ * a i) * a i)
            (a := softmaxPartition w a θ))
    _ = firstMomentUnnormalized w a θ / softmaxPartition w a θ := by
        rfl

/-- Main first-derivative identity: `deriv(logSumExp) = E_p[a]`. -/
theorem deriv_logSumExp_eq_softmaxMean
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    deriv (logSumExp w a) θ = softmaxMean (w := w) (a := a) hw θ := by
  rw [deriv_logSumExp_eq_firstMoment_div_partition (w := w) (a := a) hw θ]
  rw [softmaxMean_eq_firstMoment_div_partition (w := w) (a := a) hw θ]

/-- Normalized second moment equals `M₂/Z`. -/
lemma softmaxSecondMoment_eq_secondMomentUnnormalized_div_partition
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    softmaxSecondMoment (w := w) (a := a) hw θ
      = secondMomentUnnormalized w a θ / softmaxPartition w a θ := by
  unfold softmaxSecondMoment InfoGeometry.expectation softmaxDist
  simp only [InfoGeometry.FinProb.of_fintype, PMF.ofFintype_apply]
  have htoReal : ∀ i : ι, (ENNReal.ofReal (softmaxProb w a θ i)).toReal =
      softmaxProb w a θ i := by
    intro i
    rw [ENNReal.toReal_ofReal (le_of_lt (softmaxProb_pos w a hw θ i))]
  simp_rw [htoReal]
  simp [softmaxProb, secondMomentUnnormalized, softmaxPartition] at *
  have hZne : softmaxPartition w a θ ≠ 0 :=
    ne_of_gt (softmaxPartition_pos (w := w) (a := a) hw θ)
  calc
    ∑ i : ι,
        (w i * Real.exp (θ * a i) / softmaxPartition w a θ) * (a i) ^ (2 : ℕ)
        =
      ∑ i : ι, (w i * Real.exp (θ * a i) * (a i) ^ (2 : ℕ)) / softmaxPartition w a θ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        field_simp [hZne]
    _ =
      (∑ i : ι, w i * Real.exp (θ * a i) * (a i) ^ (2 : ℕ)) / softmaxPartition w a θ := by
        symm
        simpa using
          (Finset.sum_div
            (s := (Finset.univ : Finset ι))
            (f := fun i => w i * Real.exp (θ * a i) * (a i) ^ (2 : ℕ))
            (a := softmaxPartition w a θ))
    _ = secondMomentUnnormalized w a θ / softmaxPartition w a θ := by
        rfl

/-- Variance expansion: `Var = E[a²] - (E[a])²`. -/
lemma softmaxVariance_eq_secondMoment_sub_mean_sq
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    softmaxVariance (w := w) (a := a) hw θ
      = softmaxSecondMoment (w := w) (a := a) hw θ
        - (softmaxMean (w := w) (a := a) hw θ) ^ (2 : ℕ) := by
  let p : ι → ℝ := fun i => (softmaxDist (w := w) (a := a) hw θ i).toReal
  unfold softmaxVariance softmaxSecondMoment softmaxMean InfoGeometry.expectation
  simp only [softmaxDist, InfoGeometry.FinProb.of_fintype, PMF.ofFintype_apply]
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
    have htoReal : ∀ i : ι,
        (ENNReal.ofReal (softmaxProb w a θ i)).toReal = softmaxProb w a θ i := by
      intro i
      rw [ENNReal.toReal_ofReal (le_of_lt (softmaxProb_pos w a hw θ i))]
    exact (by
      simpa [p, softmaxDist, InfoGeometry.FinProb.of_fintype,
        PMF.ofFintype_apply, htoReal] using
        softmaxProb_sum_one (w := w) (a := a) hw θ)
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
  have hderivFun :
      (fun t => deriv (logSumExp w a) t)
        =
      fun t => firstMomentUnnormalized w a t / softmaxPartition w a t := by
    funext t
    exact deriv_logSumExp_eq_firstMoment_div_partition (w := w) (a := a) hw t
  rw [hderivFun]
  have hnumDiff : DifferentiableAt ℝ (firstMomentUnnormalized w a) θ :=
    (hasDerivAt_firstMomentUnnormalized (w := w) (a := a) θ).differentiableAt
  have hdenDiff : DifferentiableAt ℝ (softmaxPartition w a) θ :=
    (hasDerivAt_softmaxPartition (w := w) (a := a) θ).differentiableAt
  have hZne : softmaxPartition w a θ ≠ 0 :=
    ne_of_gt (softmaxPartition_pos (w := w) (a := a) hw θ)
  have hquot :
      deriv (fun t => firstMomentUnnormalized w a t / softmaxPartition w a t) θ
        =
      (deriv (firstMomentUnnormalized w a) θ * softmaxPartition w a θ
        - firstMomentUnnormalized w a θ * deriv (softmaxPartition w a) θ) /
        (softmaxPartition w a θ) ^ (2 : ℕ) := by
    simpa using
      (deriv_div (c := firstMomentUnnormalized w a) (d := softmaxPartition w a)
        (x := θ) hnumDiff hdenDiff hZne)
  rw [hquot]
  rw [deriv_firstMomentUnnormalized (w := w) (a := a) θ]
  rw [deriv_softmaxPartition (w := w) (a := a) θ]
  set Z := softmaxPartition w a θ
  set M1 := firstMomentUnnormalized w a θ
  set M2 := secondMomentUnnormalized w a θ
  have hZ : Z ≠ 0 := by simpa [Z] using hZne
  have hM1 : softmaxMean (w := w) (a := a) hw θ = M1 / Z := by
    simpa [M1, Z] using (softmaxMean_eq_firstMoment_div_partition (w := w) (a := a) hw θ)
  have hM2 : softmaxSecondMoment (w := w) (a := a) hw θ = M2 / Z := by
    simpa [M2, Z] using
      (softmaxSecondMoment_eq_secondMomentUnnormalized_div_partition (w := w) (a := a) hw θ)
  rw [hM1, hM2]
  field_simp [hZ]

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
