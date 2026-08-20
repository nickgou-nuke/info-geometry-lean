import Mathlib

/-!
# Finite scalar log-Laplace and Legendre geometry

This file owns the exact finite one-parameter exponential-family core:

* positive reference weights and a real sufficient statistic;
* partition and log-partition functions;
* normalized Gibbs probabilities;
* derivative of the log-partition as the mean;
* derivative of the mean as the variance;
* the Fisher/variance centered-square formula;
* finite KL divergence as the reversed Bregman divergence;
* the sign convention for relative surprisal.

No large-deviation theorem, completed-zeta realization, analytic continuation,
or infinite-volume limit is asserted.
-/

noncomputable section

open Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.FiniteScalarLogLaplace

universe u

variable {ι : Type u} [Fintype ι]

/-- A finite positive reference family with one real sufficient statistic. -/
structure Family (ι : Type u) [Fintype ι] where
  weight : ι → ℝ
  statistic : ι → ℝ
  weight_pos : ∀ i, 0 < weight i

namespace Family

variable (F : Family ι)

/-- Unnormalized exponential weight. -/
def unnormalized (θ : ℝ) (i : ι) : ℝ :=
  F.weight i * Real.exp (θ * F.statistic i)

/-- Finite partition function. -/
def partition (θ : ℝ) : ℝ :=
  ∑ i : ι, F.unnormalized θ i

/-- Log-partition / Massieu potential. -/
def logPartition (θ : ℝ) : ℝ :=
  Real.log (F.partition θ)

/-- Normalized Gibbs probability. -/
def probability (θ : ℝ) (i : ι) : ℝ :=
  F.unnormalized θ i / F.partition θ

/-- Unnormalized first moment. -/
def firstMomentNumerator (θ : ℝ) : ℝ :=
  ∑ i : ι, F.unnormalized θ i * F.statistic i

/-- Mean / expectation coordinate. -/
def mean (θ : ℝ) : ℝ :=
  F.firstMomentNumerator θ / F.partition θ

/-- Unnormalized second moment. -/
def secondMomentNumerator (θ : ℝ) : ℝ :=
  ∑ i : ι, F.unnormalized θ i * (F.statistic i) ^ 2

/-- Normalized second moment. -/
def secondMoment (θ : ℝ) : ℝ :=
  F.secondMomentNumerator θ / F.partition θ

/-- Variance / one-dimensional Fisher-Souriau tensor. -/
def variance (θ : ℝ) : ℝ :=
  F.secondMoment θ - (F.mean θ) ^ 2

/-- Log-density relative to the finite reference carrier. -/
def logDensity (θ : ℝ) (i : ι) : ℝ :=
  Real.log (F.weight i) + θ * F.statistic i - F.logPartition θ

/-- Finite KL divergence, with first parameter as the averaging state. -/
def kl (θ η : ℝ) : ℝ :=
  ∑ i : ι,
    F.probability θ i *
      (Real.log (F.probability θ i) - Real.log (F.probability η i))

/-- Bregman divergence of the log-partition potential. -/
def bregman (θ η : ℝ) : ℝ :=
  F.logPartition θ - F.logPartition η - F.mean η * (θ - η)

/-- Relative surprisal with orientation `-log(pθ / pη)`. -/
def relativeSurprisal (θ η : ℝ) (i : ι) : ℝ :=
  -(Real.log (F.probability θ i) - Real.log (F.probability η i))

private theorem sum_div_const (f : ι → ℝ) (c : ℝ) :
    (∑ i : ι, f i) / c = ∑ i : ι, f i / c := by
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]

@[simp] theorem unnormalized_pos (θ : ℝ) (i : ι) :
    0 < F.unnormalized θ i := by
  exact mul_pos (F.weight_pos i) (Real.exp_pos _)

variable [Nonempty ι]

@[simp] theorem partition_pos (θ : ℝ) :
    0 < F.partition θ := by
  classical
  exact Finset.sum_pos
    (fun i _ => F.unnormalized_pos θ i)
    Finset.univ_nonempty

@[simp] theorem partition_ne_zero (θ : ℝ) :
    F.partition θ ≠ 0 :=
  ne_of_gt (F.partition_pos θ)

@[simp] theorem probability_pos (θ : ℝ) (i : ι) :
    0 < F.probability θ i := by
  exact div_pos (F.unnormalized_pos θ i) (F.partition_pos θ)

@[simp] theorem probability_nonneg (θ : ℝ) (i : ι) :
    0 ≤ F.probability θ i :=
  (F.probability_pos θ i).le

/-- Gibbs probabilities normalize to one. -/
@[simp] theorem sum_probability (θ : ℝ) :
    ∑ i : ι, F.probability θ i = 1 := by
  classical
  calc
    (∑ i : ι, F.probability θ i) =
        (∑ i : ι, F.unnormalized θ i) / F.partition θ := by
          rw [sum_div_const]
          rfl
    _ = F.partition θ / F.partition θ := by rfl
    _ = 1 := div_self (F.partition_ne_zero θ)

/-- The quotient definition of the mean equals the probability expectation. -/
theorem mean_eq_expectation (θ : ℝ) :
    F.mean θ = ∑ i : ι, F.probability θ i * F.statistic i := by
  classical
  calc
    F.mean θ =
        (∑ i : ι, F.unnormalized θ i * F.statistic i) /
          F.partition θ := by rfl
    _ = ∑ i : ι,
        (F.unnormalized θ i * F.statistic i) / F.partition θ := by
          rw [sum_div_const]
    _ = ∑ i : ι, F.probability θ i * F.statistic i := by
          apply Finset.sum_congr rfl
          intro i _
          unfold probability
          ring

/-- The normalized second moment is the corresponding probability expectation. -/
theorem secondMoment_eq_expectation (θ : ℝ) :
    F.secondMoment θ =
      ∑ i : ι, F.probability θ i * (F.statistic i) ^ 2 := by
  classical
  calc
    F.secondMoment θ =
        (∑ i : ι, F.unnormalized θ i * (F.statistic i) ^ 2) /
          F.partition θ := by rfl
    _ = ∑ i : ι,
        (F.unnormalized θ i * (F.statistic i) ^ 2) / F.partition θ := by
          rw [sum_div_const]
    _ = ∑ i : ι, F.probability θ i * (F.statistic i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          unfold probability
          ring

/-- The probability is the exponential of the normalized log-density. -/
theorem probability_eq_exp_logDensity (θ : ℝ) (i : ι) :
    F.probability θ i = Real.exp (F.logDensity θ i) := by
  rw [probability, unnormalized, logDensity, logPartition]
  rw [Real.exp_sub, Real.exp_add]
  rw [Real.exp_log (F.weight_pos i), Real.exp_log (F.partition_pos θ)]

/-- Logarithm of the positive Gibbs probability recovers the log-density. -/
@[simp] theorem log_probability (θ : ℝ) (i : ι) :
    Real.log (F.probability θ i) = F.logDensity θ i := by
  rw [F.probability_eq_exp_logDensity]
  exact Real.log_exp _

/-- Derivative of one unnormalized exponential weight. -/
theorem hasDerivAt_unnormalized (θ : ℝ) (i : ι) :
    HasDerivAt (fun t => F.unnormalized t i)
      (F.unnormalized θ i * F.statistic i) θ := by
  unfold unnormalized
  have h1 : HasDerivAt (fun t : ℝ => t * F.statistic i) (F.statistic i) θ := by
    simpa using (hasDerivAt_id θ).mul_const (F.statistic i)
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (t * F.statistic i))
      (Real.exp (θ * F.statistic i) * F.statistic i) θ :=
    h1.exp
  have h3 : HasDerivAt (fun t : ℝ => F.weight i * Real.exp (t * F.statistic i))
      (F.weight i * (Real.exp (θ * F.statistic i) * F.statistic i)) θ :=
    h2.const_mul (F.weight i)
  simpa [mul_assoc] using h3

/-- Derivative of the finite partition function. -/
theorem hasDerivAt_partition (θ : ℝ) :
    HasDerivAt F.partition (F.firstMomentNumerator θ) θ := by
  classical
  unfold partition firstMomentNumerator
  simpa using
    (HasDerivAt.fun_sum
      (u := Finset.univ)
      (A := fun i t => F.unnormalized t i)
      (A' := fun i => F.unnormalized θ i * F.statistic i)
      (fun i _ => F.hasDerivAt_unnormalized θ i))

/-- Derivative of the unnormalized first moment. -/
theorem hasDerivAt_firstMomentNumerator (θ : ℝ) :
    HasDerivAt F.firstMomentNumerator (F.secondMomentNumerator θ) θ := by
  classical
  unfold firstMomentNumerator secondMomentNumerator
  simpa only [mul_assoc, pow_two] using
    (HasDerivAt.fun_sum
      (u := Finset.univ)
      (A := fun i t => F.unnormalized t i * F.statistic i)
      (A' := fun i => F.unnormalized θ i * F.statistic i * F.statistic i)
      (fun i _ => (F.hasDerivAt_unnormalized θ i).mul_const (F.statistic i)))

/-- The derivative of the log-partition is the Gibbs mean. -/
theorem hasDerivAt_logPartition (θ : ℝ) :
    HasDerivAt F.logPartition (F.mean θ) θ := by
  simpa [logPartition, mean] using
    (F.hasDerivAt_partition θ).log (F.partition_ne_zero θ)

@[simp] theorem deriv_logPartition (θ : ℝ) :
    deriv F.logPartition θ = F.mean θ :=
  (F.hasDerivAt_logPartition θ).deriv

/-- The derivative of the mean is the variance. -/
theorem hasDerivAt_mean (θ : ℝ) :
    HasDerivAt F.mean (F.variance θ) θ := by
  have h := (F.hasDerivAt_firstMomentNumerator θ).fun_div
    (F.hasDerivAt_partition θ) (F.partition_ne_zero θ)
  have heq : (F.secondMomentNumerator θ * F.partition θ - F.firstMomentNumerator θ * F.firstMomentNumerator θ) / (F.partition θ) ^ 2 = F.variance θ := by
    dsimp [variance, secondMoment, mean]
    field_simp [F.partition_ne_zero θ]
    ring
  exact heq ▸ h

@[simp] theorem deriv_mean (θ : ℝ) :
    deriv F.mean θ = F.variance θ :=
  (F.hasDerivAt_mean θ).deriv

/-- The second derivative of the log-partition is the variance. -/
theorem hasDerivAt_deriv_logPartition (θ : ℝ) :
    HasDerivAt (fun t => deriv F.logPartition t) (F.variance θ) θ := by
  have hfun : (fun t => deriv F.logPartition t) = F.mean := by
    funext t
    exact F.deriv_logPartition t
  rw [hfun]
  exact F.hasDerivAt_mean θ

/-- Algebraic centered-square representation of the variance. -/
theorem variance_eq_centered_expectation (θ : ℝ) :
    F.variance θ =
      ∑ i : ι,
        F.probability θ i * (F.statistic i - F.mean θ) ^ 2 := by
  classical
  rw [variance, F.secondMoment_eq_expectation]
  let m : ℝ := F.mean θ
  have hm : m = ∑ i : ι, F.probability θ i * F.statistic i := by
    exact F.mean_eq_expectation θ
  have hexpand :
      (∑ i : ι,
          F.probability θ i * (F.statistic i - m) ^ 2) =
        (∑ i : ι, F.probability θ i * (F.statistic i) ^ 2) -
          2 * m * (∑ i : ι, F.probability θ i * F.statistic i) +
          m ^ 2 * (∑ i : ι, F.probability θ i) := by
    calc
      (∑ i : ι,
          F.probability θ i * (F.statistic i - m) ^ 2) =
        ∑ i : ι,
          (F.probability θ i * (F.statistic i) ^ 2 -
            2 * m * (F.probability θ i * F.statistic i) +
            m ^ 2 * F.probability θ i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ =
        (∑ i : ι, F.probability θ i * (F.statistic i) ^ 2) -
          2 * m * (∑ i : ι, F.probability θ i * F.statistic i) +
          m ^ 2 * (∑ i : ι, F.probability θ i) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hexpand, F.sum_probability, ← hm]
  dsimp [m]
  ring

/-- Variance is nonnegative. -/
theorem variance_nonnegative (θ : ℝ) :
    0 ≤ F.variance θ := by
  rw [F.variance_eq_centered_expectation]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (F.probability_nonneg θ i) (sq_nonneg _)

/-- The finite log-partition has nonnegative second derivative. -/
theorem secondDerivative_nonnegative (θ : ℝ) :
    0 ≤ deriv F.mean θ := by
  rw [F.deriv_mean]
  exact F.variance_nonnegative θ

/-- Exact finite exponential-family identity: KL is reversed Bregman divergence. -/
theorem kl_eq_bregman_reverse (θ η : ℝ) :
    F.kl θ η = F.bregman η θ := by
  classical
  unfold kl bregman
  simp_rw [F.log_probability, logDensity]
  have hpoint (i : ι) :
      F.probability θ i *
          ((Real.log (F.weight i) + θ * F.statistic i - F.logPartition θ) -
            (Real.log (F.weight i) + η * F.statistic i - F.logPartition η)) =
        (θ - η) * (F.probability θ i * F.statistic i) +
          (F.logPartition η - F.logPartition θ) * F.probability θ i := by
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [← F.mean_eq_expectation, F.sum_probability]
  ring

/-- Finite Gibbs KL divergence is nonnegative. -/
theorem kl_nonnegative (θ η : ℝ) :
    0 ≤ F.kl θ η := by
  classical
  have hpoint (i : ι) :
      F.probability θ i - F.probability η i ≤
        F.probability θ i *
          (Real.log (F.probability θ i) -
            Real.log (F.probability η i)) := by
    have hp : 0 < F.probability θ i := F.probability_pos θ i
    have hq : 0 < F.probability η i := F.probability_pos η i
    have hlog := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hp.le
    have hratio :
        F.probability θ i *
            (F.probability η i / F.probability θ i - 1) =
          F.probability η i - F.probability θ i := by
      field_simp [hp.ne']
    rw [hratio] at hmul
    nlinarith
  have hsum :
      (∑ i : ι, (F.probability θ i - F.probability η i)) ≤
        ∑ i : ι,
          F.probability θ i *
            (Real.log (F.probability θ i) -
              Real.log (F.probability η i)) := by
    exact Finset.sum_le_sum fun i _ => hpoint i
  rw [Finset.sum_sub_distrib, F.sum_probability, F.sum_probability,
    sub_self] at hsum
  exact hsum

/-- Bregman divergence is nonnegative in the finite exponential family. -/
theorem bregman_nonnegative (θ η : ℝ) :
    0 ≤ F.bregman θ η := by
  rw [← F.kl_eq_bregman_reverse η θ]
  exact F.kl_nonnegative η θ

/-- KL is the negative expectation of the chosen relative-surprisal orientation. -/
theorem kl_eq_neg_expectation_relativeSurprisal (θ η : ℝ) :
    F.kl θ η =
      -∑ i : ι, F.probability θ i * F.relativeSurprisal θ η i := by
  classical
  unfold kl relativeSurprisal
  simp only [mul_neg, Finset.sum_neg_distrib, neg_neg]

/-- Relative surprisal has the affine exponential-family form. -/
theorem relativeSurprisal_eq (θ η : ℝ) (i : ι) :
    F.relativeSurprisal θ η i =
      (η - θ) * F.statistic i + F.logPartition θ - F.logPartition η := by
  unfold relativeSurprisal
  rw [F.log_probability, F.log_probability]
  unfold logDensity
  ring

end Family

end InfoGeometry.Canonical.FiniteScalarLogLaplace

end noncomputable section
