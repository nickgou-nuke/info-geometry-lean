import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import InfoGeometry.Analytic.LogSumExp
import InfoGeometry.Analytic.LogSumExpVariancePositivity

open Matrix
open scoped BigOperators

namespace AttentionInformationGeometry

variable {M : ℕ} [NeZero M]

/-! ### 1. Partition Function & Softmax Distribution -/

/-- Partition function Z(s) = ∑_m exp(s_m) for a vector of logits s. -/
noncomputable def partitionZ (s : Fin M → ℝ) : ℝ :=
  ∑ m : Fin M, Real.exp (s m)

/-- The log-partition function along the affine logit path `s + t • v`.
This reuses the finite `logSumExp` calculus owner. -/
noncomputable def logPartitionAlong (s v : Fin M → ℝ) (t : ℝ) : ℝ :=
  InfoGeometry.Analytic.logSumExp (fun m => Real.exp (s m)) v t

lemma partitionZ_pos (s : Fin M → ℝ) : 0 < partitionZ s := by
  dsimp [partitionZ]
  apply Finset.sum_pos
  · intro j _
    exact Real.exp_pos (s j)
  · exact Finset.univ_nonempty

lemma partitionZ_ne_zero (s : Fin M → ℝ) : partitionZ s ≠ 0 :=
  ne_of_gt (partitionZ_pos s)

/-- Softmax probability distribution A_j(s) = exp(s_j) / Z(s). -/
noncomputable def softmaxProb (s : Fin M → ℝ) (j : Fin M) : ℝ :=
  Real.exp (s j) / partitionZ s

theorem softmaxProb_pos (s : Fin M → ℝ) (j : Fin M) : 0 < softmaxProb s j :=
  div_pos (Real.exp_pos (s j)) (partitionZ_pos s)

theorem softmaxProb_ne_zero (s : Fin M → ℝ) (j : Fin M) : softmaxProb s j ≠ 0 :=
  ne_of_gt (softmaxProb_pos s j)

/-- Total probability normalization: ∑_j A_j(s) = 1. -/
theorem softmaxProb_sum (s : Fin M → ℝ) : (∑ j : Fin M, softmaxProb s j) = 1 := by
  dsimp [softmaxProb]
  rw [← Finset.sum_div]
  exact div_self (partitionZ_ne_zero s)

omit [NeZero M] in
/-- The affine-path potential is the ordinary log-partition function at the
shifted logits. -/
theorem logPartitionAlong_eq_log_partition (s v : Fin M → ℝ) (t : ℝ) :
    logPartitionAlong s v t =
      Real.log (partitionZ (fun m => s m + t * v m)) := by
  simp [logPartitionAlong, InfoGeometry.Analytic.logSumExp,
    InfoGeometry.Analytic.logSumExpPartition, partitionZ, Real.exp_add]

/-- Adding a constant to every logit adds that constant to the log-partition
potential, independently of the direction parameter. -/
theorem logPartitionAlong_uniform_shift
    (s v : Fin M → ℝ) (c t : ℝ) :
    logPartitionAlong (fun m => s m + c) v t =
      c + logPartitionAlong s v t := by
  let w : Fin M → ℝ := fun m => Real.exp (s m)
  have hw : ∀ m, 0 < w m := fun m => Real.exp_pos (s m)
  have hweights :
      (fun m => Real.exp (s m + c)) = fun m => Real.exp c * w m := by
    funext m
    simp [w, Real.exp_add]
    ring
  change InfoGeometry.Analytic.logSumExp
    (fun m => Real.exp (s m + c)) v t = _
  rw [hweights]
  simpa [logPartitionAlong, w, Real.log_exp] using
    (InfoGeometry.Analytic.logSumExp_weight_scale w v hw
      (Real.exp c) (Real.exp_pos c) t)

/-- The genuine second directional derivative of log-partition is the
softmax-weighted variance of the direction. -/
theorem logPartitionAlong_secondDeriv_eq_variance (s v : Fin M → ℝ) :
    deriv (fun t => deriv (logPartitionAlong s v) t) 0 =
      ∑ m : Fin M, softmaxProb s m *
        (v m - ∑ l : Fin M, softmaxProb s l * v l) ^ (2 : ℕ) := by
  let w : Fin M → ℝ := fun m => Real.exp (s m)
  have hw : ∀ m, 0 < w m := fun m => Real.exp_pos (s m)
  have hweight (m : Fin M) :
      InfoGeometry.Analytic.logSumExpWeight w v 0 m = softmaxProb s m := by
    simp [InfoGeometry.Analytic.logSumExpWeight,
      InfoGeometry.Analytic.logSumExpPartition, softmaxProb, partitionZ, w]
  change deriv (fun t => deriv (InfoGeometry.Analytic.logSumExp w v) t) 0 = _
  rw [InfoGeometry.Analytic.logSumExp_secondDeriv_eq_variance w v hw 0]
  rw [InfoGeometry.Analytic.logSumExpVariance_eq_centered w v hw 0]
  simp_rw [hweight]

/-! ### 2. Token Indicator Observables and Moments -/

/-- Token Indicator Observable O_j(m) = δ_{jm} = if m = j then 1 else 0. -/
def tokenObservable (j : Fin M) : Fin M → ℝ :=
  fun m => if m = j then 1 else 0

/-- Expectation operator under the softmax measure: E[f] = ∑_m A_m(s) * f(m). -/
noncomputable def expectation (s : Fin M → ℝ) (f : Fin M → ℝ) : ℝ :=
  ∑ m : Fin M, softmaxProb s m * f m

omit [NeZero M] in
/-- First Moment: The expectation of the indicator observable is the softmax probability:
    E[O_j] = A_j(s). -/
theorem expectation_tokenObservable (s : Fin M → ℝ) (j : Fin M) :
    expectation s (tokenObservable j) = softmaxProb s j := by
  dsimp [expectation, tokenObservable]
  have h : (∑ m : Fin M, softmaxProb s m * (if m = j then (1 : ℝ) else 0)) =
      softmaxProb s j * (if j = j then (1 : ℝ) else 0) := by
    apply Finset.sum_eq_single j
    · intro m _ hne
      rw [if_neg hne, mul_zero]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  rw [h, if_pos rfl, mul_one]

/-- The coordinate derivative of log-partition is the corresponding softmax
probability; its path is the indicator of coordinate `j`. -/
theorem logPartition_coordinate_deriv (s : Fin M → ℝ) (j : Fin M) :
    deriv (logPartitionAlong s (tokenObservable j)) 0 = softmaxProb s j := by
  let w : Fin M → ℝ := fun m => Real.exp (s m)
  have hw : ∀ m, 0 < w m := fun m => Real.exp_pos (s m)
  have hweight (m : Fin M) :
      InfoGeometry.Analytic.logSumExpWeight w (tokenObservable j) 0 m = softmaxProb s m := by
    simp [InfoGeometry.Analytic.logSumExpWeight,
      InfoGeometry.Analytic.logSumExpPartition, softmaxProb, partitionZ, w]
  change deriv (InfoGeometry.Analytic.logSumExp w (tokenObservable j)) 0 = _
  rw [InfoGeometry.Analytic.logSumExp_deriv_eq_mean w (tokenObservable j) hw 0]
  rw [InfoGeometry.Analytic.logSumExpMean_eq_weighted_sum w (tokenObservable j) hw 0]
  simp_rw [hweight]
  exact expectation_tokenObservable s j

/-- The directional derivative of the log-partition is the softmax expectation
of its direction. -/
theorem logPartitionAlong_directional_deriv_eq_expectation
    (s v : Fin M → ℝ) :
    deriv (logPartitionAlong s v) 0 = expectation s v := by
  let w : Fin M → ℝ := fun m => Real.exp (s m)
  have hw : ∀ m, 0 < w m := fun m => Real.exp_pos (s m)
  have hweight (m : Fin M) :
      InfoGeometry.Analytic.logSumExpWeight w v 0 m = softmaxProb s m := by
    simp [InfoGeometry.Analytic.logSumExpWeight,
      InfoGeometry.Analytic.logSumExpPartition, softmaxProb, partitionZ, w]
  change deriv (InfoGeometry.Analytic.logSumExp w v) 0 = _
  rw [InfoGeometry.Analytic.logSumExp_deriv_eq_mean w v hw 0]
  rw [InfoGeometry.Analytic.logSumExpMean_eq_weighted_sum w v hw 0]
  simp_rw [hweight]
  rfl

/-- Scaling a logit direction scales the log-partition derivative by the same
factor, exposing the attention temperature factor. -/
theorem logPartitionAlong_smul_directional_deriv
    (s v : Fin M → ℝ) (c : ℝ) :
    deriv (logPartitionAlong s (fun i => c * v i)) 0 =
      c * expectation s v := by
  rw [logPartitionAlong_directional_deriv_eq_expectation]
  unfold expectation
  calc
    ∑ i : Fin M, softmaxProb s i * (c * v i) =
        ∑ i : Fin M, c * (softmaxProb s i * v i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = c * ∑ i : Fin M, softmaxProb s i * v i := by
      rw [Finset.mul_sum]

/-- The covariance-form matrix associated to the log-partition potential.
Its quadratic form is proved below to equal the actual second directional
derivative of log-partition. -/
noncomputable def hessianLogZ (s : Fin M → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun j k => (if j = k then softmaxProb s j else 0) - softmaxProb s j * softmaxProb s k

omit [NeZero M] in
private theorem softmaxProb_uniform_shift
    (s : Fin M → ℝ) (c : ℝ) (j : Fin M) :
    softmaxProb (fun m => s m + c) j = softmaxProb s j := by
  dsimp [softmaxProb, partitionZ]
  simp_rw [Real.exp_add]
  rw [← Finset.sum_mul]
  exact mul_div_mul_right _ _ (ne_of_gt (Real.exp_pos c))

omit [NeZero M] in
/-- The covariance-form Hessian is invariant under the global additive-logit
gauge. -/
theorem hessianLogZ_uniform_shift
    (s : Fin M → ℝ) (c : ℝ) (j k : Fin M) :
    hessianLogZ (fun m => s m + c) j k = hessianLogZ s j k := by
  change (if j = k then softmaxProb (fun m => s m + c) j else 0) -
      softmaxProb (fun m => s m + c) j * softmaxProb (fun m => s m + c) k =
    (if j = k then softmaxProb s j else 0) - softmaxProb s j * softmaxProb s k
  rw [softmaxProb_uniform_shift s c j, softmaxProb_uniform_shift s c k]

omit [NeZero M] in
/-- Concrete failure of logit-scale invariance, unlike the additive-shift gauge. -/
theorem softmaxProb_not_invariant_under_logit_scaling :
    softmaxProb (fun i : Fin 2 => 2 * (i : ℝ)) 0 ≠
      softmaxProb (fun i : Fin 2 => (i : ℝ)) 0 := by
  simp [softmaxProb, partitionZ, Fin.sum_univ_two]

/-- The derivative of softmax coordinate `j` along logit coordinate `k` is
the `(j,k)` entry of the covariance-form Hessian. -/
theorem softmaxProb_coordinate_deriv
    (s : Fin M → ℝ) (j k : Fin M) :
    deriv (fun t => softmaxProb
      (fun l => s l + t * tokenObservable k l) j) 0 = hessianLogZ s j k := by
  let w : Fin M → ℝ := fun l => Real.exp (s l)
  have hw : ∀ l, 0 < w l := fun l => Real.exp_pos (s l)
  have hweight (t : ℝ) (l : Fin M) :
      softmaxProb (fun r => s r + t * tokenObservable k r) l =
        InfoGeometry.Analytic.logSumExpWeight w (tokenObservable k) t l := by
    simp [softmaxProb, partitionZ, InfoGeometry.Analytic.logSumExpWeight,
      InfoGeometry.Analytic.logSumExpPartition, w, Real.exp_add]
  have hweightZero (l : Fin M) :
      InfoGeometry.Analytic.logSumExpWeight w (tokenObservable k) 0 l =
        softmaxProb s l := by
    simpa [w] using (hweight 0 l).symm
  have hmean : InfoGeometry.Analytic.logSumExpMean w (tokenObservable k) 0 =
      softmaxProb s k := by
    calc
      _ = ∑ l : Fin M,
          InfoGeometry.Analytic.logSumExpWeight w (tokenObservable k) 0 l *
            tokenObservable k l :=
          InfoGeometry.Analytic.logSumExpMean_eq_weighted_sum w
            (tokenObservable k) hw 0
      _ = expectation s (tokenObservable k) := by
        unfold expectation
        simp_rw [hweightZero]
      _ = softmaxProb s k := expectation_tokenObservable s k
  have hderiv := InfoGeometry.Analytic.logSumExpWeight_deriv
    w (tokenObservable k) hw 0 j
  have hfun :
      (fun t => softmaxProb (fun l => s l + t * tokenObservable k l) j) =
        (fun t => InfoGeometry.Analytic.logSumExpWeight w (tokenObservable k) t j) := by
    funext t
    exact hweight t j
  rw [hfun, hderiv, hweightZero j, hmean]
  by_cases hjk : j = k
  · subst k
    simp [hessianLogZ, tokenObservable]
    ring
  · simp [hessianLogZ, tokenObservable, hjk]

/-- The actual iterated coordinate derivative of the log-partition function
is the covariance-form matrix entry. -/
theorem logPartition_mixedCoordinateDeriv_eq_hessian
    (s : Fin M → ℝ) (j k : Fin M) :
    deriv (fun t => deriv
      (logPartitionAlong (fun l => s l + t * tokenObservable k l)
        (tokenObservable j)) 0) 0 = hessianLogZ s j k := by
  have hgradient :
      (fun t => deriv
        (logPartitionAlong (fun l => s l + t * tokenObservable k l)
          (tokenObservable j)) 0) =
        (fun t => softmaxProb (fun l => s l + t * tokenObservable k l) j) := by
    funext t
    exact logPartition_coordinate_deriv
      (fun l => s l + t * tokenObservable k l) j
  rw [hgradient]
  exact softmaxProb_coordinate_deriv s j k

omit [NeZero M] in
/-- Product of Indicator Observables: O_j(m) * O_k(m) = if j = k then O_j(m) else 0. -/
lemma tokenObservable_mul (j k : Fin M) (m : Fin M) :
    tokenObservable j m * tokenObservable k m =
      if j = k then tokenObservable j m else 0 := by
  by_cases hmj : m = j
  · subst m
    by_cases hjk : j = k
    · subst k
      simp [tokenObservable]
    · simp [tokenObservable, hjk]
  · by_cases hmk : m = k
    · subst m
      by_cases hjk : j = k
      · subst k
        exact (hmj rfl).elim
      · have hkj : k ≠ j := fun h => hjk h.symm
        simp [tokenObservable, hjk, hkj]
    · simp [tokenObservable, hmj, hmk]

omit [NeZero M] in
/-- Second Moment: E[O_j O_k] = if j = k then A_j(s) else 0. -/
theorem expectation_tokenObservable_mul (s : Fin M → ℝ) (j k : Fin M) :
    expectation s (fun m => tokenObservable j m * tokenObservable k m) =
      if j = k then softmaxProb s j else 0 := by
  dsimp [expectation]
  simp_rw [tokenObservable_mul j k]
  split_ifs with hjk
  · subst hjk
    exact expectation_tokenObservable s j
  · have h_zero : (∑ m : Fin M, softmaxProb s m * (0 : ℝ)) = 0 := by
      simp only [mul_zero, Finset.sum_const_zero]
    exact h_zero

/-! ### 3. Covariance Matrix and Hessian Matrix -/

/-- The Centered Covariance Matrix of Token Observables:
    Cov(O_j, O_k) = E[(O_j - E[O_j]) * (O_k - E[O_k])]. -/
noncomputable def tokenCovariance (s : Fin M → ℝ) (j k : Fin M) : ℝ :=
  expectation s (fun m => (tokenObservable j m - softmaxProb s j) *
                          (tokenObservable k m - softmaxProb s k))

/-- The Uncentered Covariance Matrix:
    Cov_uncentered(O_j, O_k) = E[O_j O_k] - E[O_j] E[O_k]. -/
noncomputable def tokenCovarianceUncentered (s : Fin M → ℝ) (j k : Fin M) : ℝ :=
  expectation s (fun m => tokenObservable j m * tokenObservable k m) -
    (expectation s (tokenObservable j)) * (expectation s (tokenObservable k))

/-- Equivalence of Centered and Uncentered Covariance formulations. -/
theorem tokenCovariance_eq_uncentered (s : Fin M → ℝ) (j k : Fin M) :
    tokenCovariance s j k = tokenCovarianceUncentered s j k := by
  dsimp [tokenCovariance, tokenCovarianceUncentered, expectation]
  have h_term (m : Fin M) :
      softmaxProb s m * ((tokenObservable j m - softmaxProb s j) * (tokenObservable k m - softmaxProb s k)) =
        softmaxProb s m * (tokenObservable j m * tokenObservable k m) -
        softmaxProb s k * (softmaxProb s m * tokenObservable j m) -
        softmaxProb s j * (softmaxProb s m * tokenObservable k m) +
        (softmaxProb s j * softmaxProb s k) * softmaxProb s m := by ring
  simp_rw [h_term]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hX : (∑ m : Fin M, softmaxProb s m * tokenObservable j m) = softmaxProb s j := by
    exact expectation_tokenObservable s j
  have hY : (∑ m : Fin M, softmaxProb s m * tokenObservable k m) = softmaxProb s k := by
    exact expectation_tokenObservable s k
  have h1 : (∑ m : Fin M, softmaxProb s m) = 1 := softmaxProb_sum s
  rw [hX, hY, h1]
  ring

omit [NeZero M] in
/-- Algebraic reduction of uncentered covariance to the covariance-form matrix. -/
theorem tokenCovarianceUncentered_eq_hessian (s : Fin M → ℝ) (j k : Fin M) :
    tokenCovarianceUncentered s j k = hessianLogZ s j k := by
  dsimp [tokenCovarianceUncentered, hessianLogZ]
  rw [expectation_tokenObservable_mul, expectation_tokenObservable, expectation_tokenObservable]

/-- The covariance-form matrix equals the covariance matrix of token observables. -/
theorem hessianLogZ_eq_tokenCovariance (s : Fin M → ℝ) (j k : Fin M) :
    hessianLogZ s j k = tokenCovariance s j k := by
  rw [tokenCovariance_eq_uncentered, tokenCovarianceUncentered_eq_hessian]

/-! ### 4. Fisher-Rao Information Metric -/

/-- The centered token observable used as the softmax score function. -/
noncomputable def scoreFunction (s : Fin M → ℝ) (j : Fin M) : Fin M → ℝ :=
  fun m => tokenObservable j m - softmaxProb s j

/-- Log probability of outcome `m` when coordinate `j` is varied by `t`. -/
noncomputable def logSoftmaxAlong
    (s : Fin M → ℝ) (j m : Fin M) (t : ℝ) : ℝ :=
  Real.log (softmaxProb (fun l => s l + t * tokenObservable j l) m)

/-- The score of the finite softmax family is the derivative of its actual
log probability along the `j`th coordinate direction. -/
theorem scoreFunction_eq_logSoftmaxAlong_deriv
    (s : Fin M → ℝ) (j m : Fin M) :
    deriv (logSoftmaxAlong s j m) 0 = scoreFunction s j m := by
  have hlog_eq (t : ℝ) :
      logSoftmaxAlong s j m t =
        (s m + t * tokenObservable j m) -
          logPartitionAlong s (tokenObservable j) t := by
    rw [logSoftmaxAlong, softmaxProb]
    rw [Real.log_div (ne_of_gt (Real.exp_pos _))
      (partitionZ_ne_zero (fun l => s l + t * tokenObservable j l))]
    rw [Real.log_exp, logPartitionAlong_eq_log_partition]

  have hfun : logSoftmaxAlong s j m =
      fun t => (s m + t * tokenObservable j m) -
        logPartitionAlong s (tokenObservable j) t := by
    funext t
    exact hlog_eq t

  have hlin : HasDerivAt
      (fun t : ℝ => s m + t * tokenObservable j m)
      (tokenObservable j m) 0 := by
    have hd := (hasDerivAt_id' (0 : ℝ)).mul_const (tokenObservable j m) |>.const_add (s m)
    change HasDerivAt _ (1 * tokenObservable j m) 0 at hd
    rw [one_mul] at hd
    exact hd

  have hlogPart : HasDerivAt
      (fun t => logPartitionAlong s (tokenObservable j) t)
      (softmaxProb s j) 0 := by
    let w : Fin M → ℝ := fun l => Real.exp (s l)
    have hw : ∀ l, 0 < w l := fun l => Real.exp_pos (s l)
    change HasDerivAt (fun t => InfoGeometry.Analytic.logSumExp w (tokenObservable j) t)
      (softmaxProb s j) 0
    have h := InfoGeometry.Analytic.hasDerivAt_logSumExp
      w (tokenObservable j) hw 0
    have hmean : InfoGeometry.Analytic.logSumExpMean w (tokenObservable j) 0 =
        softmaxProb s j := by
      calc
        _ = deriv (fun t => InfoGeometry.Analytic.logSumExp w (tokenObservable j) t) 0 :=
          h.deriv.symm
        _ = softmaxProb s j := by
          exact logPartition_coordinate_deriv s j
    change HasDerivAt _ (InfoGeometry.Analytic.logSumExpMean w (tokenObservable j) 0) 0 at h
    rw [hmean] at h
    exact h

  rw [hfun]
  have hd := (hlin.sub hlogPart).deriv
  change deriv (fun t => s m + t * tokenObservable j m - logPartitionAlong s (tokenObservable j) t) 0 = tokenObservable j m - softmaxProb s j at hd
  change deriv (fun t => s m + t * tokenObservable j m - logPartitionAlong s (tokenObservable j) t) 0 = scoreFunction s j m
  rw [hd]
  rfl

/-- The Fisher-Rao Information Metric:
    g_{jk}(s) = E[ V_j * V_k ]. -/
noncomputable def fisherInformation (s : Fin M → ℝ) (j k : Fin M) : ℝ :=
  expectation s (fun m => scoreFunction s j m * scoreFunction s k m)

/-- Information-Geometric Identity: The Fisher-Rao Metric equals the Hessian of ln(Z(s)). -/
theorem fisherInformation_eq_hessian (s : Fin M → ℝ) (j k : Fin M) :
    fisherInformation s j k = hessianLogZ s j k := by
  calc
    fisherInformation s j k = tokenCovariance s j k := by
      rfl
    _ = hessianLogZ s j k :=
      (hessianLogZ_eq_tokenCovariance s j k).symm

/-! ### 5. Positive Semi-Definiteness and Convexity -/

/-- Decomposition of the Quadratic Form into Variance:
    ∑_{j, k} v_j * H_{jk} * v_k = ∑_m A_m * (v_m - ∑_l A_l v_l)². -/
lemma hessian_quadratic_form_eq_variance (s : Fin M → ℝ) (v : Fin M → ℝ) :
    (∑ j : Fin M, ∑ k : Fin M, v j * hessianLogZ s j k * v k) =
      ∑ m : Fin M, softmaxProb s m * (v m - (∑ l : Fin M, softmaxProb s l * v l))^2 := by
  have h_rhs_term : ∀ m : Fin M,
      softmaxProb s m * (v m - (∑ l : Fin M, softmaxProb s l * v l))^2 =
        softmaxProb s m * (v m)^2 - 2 * (∑ l : Fin M, softmaxProb s l * v l) * (softmaxProb s m * v m) + (∑ l : Fin M, softmaxProb s l * v l)^2 * softmaxProb s m := by
    intro m
    ring
  simp_rw [h_rhs_term]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h_sum_v : (∑ m : Fin M, softmaxProb s m * v m) = ∑ l : Fin M, softmaxProb s l * v l := rfl
  rw [h_sum_v, softmaxProb_sum s]
  have h_rhs_alg : (∑ m : Fin M, softmaxProb s m * (v m)^2) - 2 * (∑ l : Fin M, softmaxProb s l * v l) * (∑ l : Fin M, softmaxProb s l * v l) + (∑ l : Fin M, softmaxProb s l * v l)^2 * 1 =
      (∑ m : Fin M, softmaxProb s m * (v m)^2) - (∑ l : Fin M, softmaxProb s l * v l)^2 := by ring
  rw [h_rhs_alg]

  -- Expand LHS
  have h_lhs : (∑ j : Fin M, ∑ k : Fin M, v j * hessianLogZ s j k * v k) =
      (∑ j : Fin M, softmaxProb s j * (v j)^2) - (∑ l : Fin M, softmaxProb s l * v l)^2 := by
    have h_inner (j : Fin M) : (∑ k : Fin M, v j * hessianLogZ s j k * v k) =
        softmaxProb s j * (v j)^2 - (softmaxProb s j * v j) * (∑ l : Fin M, softmaxProb s l * v l) := by
      dsimp [hessianLogZ]
      have h_expand (k : Fin M) :
          v j * ((if j = k then softmaxProb s j else 0) - softmaxProb s j * softmaxProb s k) * v k =
            (if j = k then softmaxProb s j * (v j)^2 else 0) - (softmaxProb s j * v j) * (softmaxProb s k * v k) := by
        split_ifs with hjk
        · subst hjk; ring
        · ring
      simp_rw [h_expand]
      rw [Finset.sum_sub_distrib]
      have h_diag : (∑ k : Fin M, if j = k then softmaxProb s j * (v j)^2 else 0) =
          softmaxProb s j * (v j)^2 := by
        classical
        simp
      rw [h_diag]
      have h_right : (∑ k : Fin M, softmaxProb s j * v j * (softmaxProb s k * v k)) =
          (softmaxProb s j * v j) * (∑ k : Fin M, softmaxProb s k * v k) := by
        rw [← Finset.mul_sum]
      rw [h_right]
    simp_rw [h_inner]
    rw [Finset.sum_sub_distrib]
    have h_sum_left : (∑ j : Fin M, softmaxProb s j * v j * ∑ l : Fin M, softmaxProb s l * v l) =
        (∑ j : Fin M, softmaxProb s j * v j) * (∑ l : Fin M, softmaxProb s l * v l) := by
      rw [← Finset.sum_mul]
    rw [h_sum_left]
    rw [h_sum_v]
    ring

  rw [h_lhs]

/-- The covariance-form matrix `hessianLogZ` represents the genuine second
directional derivative of log-partition. -/
theorem logPartitionAlong_secondDeriv_eq_hessian_quadratic (s v : Fin M → ℝ) :
    deriv (fun t => deriv (logPartitionAlong s v) t) 0 =
      ∑ j : Fin M, ∑ k : Fin M, v j * hessianLogZ s j k * v k := by
  rw [logPartitionAlong_secondDeriv_eq_variance, hessian_quadratic_form_eq_variance]

/-- The log-partition curvature is strictly positive exactly in directions
that are not constant across the finite outcome space. Constant directions
are the global additive-logit gauge. -/
theorem hessianLogZ_positive_iff_nonconstant (s v : Fin M → ℝ) :
    0 < ∑ j : Fin M, ∑ k : Fin M, v j * hessianLogZ s j k * v k ↔
      ∃ j k, v j ≠ v k := by
  rw [← logPartitionAlong_secondDeriv_eq_hessian_quadratic]
  let w : Fin M → ℝ := fun m => Real.exp (s m)
  have hw : ∀ m, 0 < w m := fun m => Real.exp_pos (s m)
  have hderiv :
      deriv (fun t => deriv (logPartitionAlong s v) t) 0 =
        InfoGeometry.Analytic.logSumExpVariance w v 0 := by
    change deriv (fun t => deriv (InfoGeometry.Analytic.logSumExp w v) t) 0 = _
    exact InfoGeometry.Analytic.logSumExp_secondDeriv_eq_variance w v hw 0
  rw [hderiv]
  constructor
  · intro h
    by_contra hconstant
    have hv : ∀ i, v i = v 0 := by
      intro i
      by_contra hne
      exact hconstant ⟨i, 0, hne⟩
    have hzero := InfoGeometry.Analytic.logSumExpVariance_eq_zero_of_forall_eq
      w v hw 0 (v 0) hv
    rw [hzero] at h
    exact (lt_irrefl 0) h
  · intro hdiff
    exact InfoGeometry.Analytic.logSumExpVariance_pos_of_exists_ne w v hw 0 hdiff

/-- Strict Convexity: The Hessian matrix of ln(Z(s)) is Positive Semi-Definite. -/
theorem hessianLogZ_positive_semidefinite (s : Fin M → ℝ) (v : Fin M → ℝ) :
    0 ≤ ∑ j : Fin M, ∑ k : Fin M, v j * hessianLogZ s j k * v k := by
  rw [hessian_quadratic_form_eq_variance]
  apply Finset.sum_nonneg
  intro m _
  have hA : 0 ≤ softmaxProb s m := le_of_lt (softmaxProb_pos s m)
  have hsq : 0 ≤ (v m - ∑ l : Fin M, softmaxProb s l * v l)^2 := sq_nonneg _
  exact mul_nonneg hA hsq

/-! ### 6. Full Attention Matrix Formulation -/

variable {N : ℕ} [NeZero N]

/-- The covariance-form matrix for row `i`; its quadratic form is the
second directional derivative along that row's logits. -/
noncomputable def attentionHessian (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    Matrix (Fin M) (Fin M) ℝ :=
  hessianLogZ (S i)

/-- The Covariance Matrix of Token Observables for row i. -/
noncomputable def attentionTokenCovariance (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    Matrix (Fin M) (Fin M) ℝ :=
  fun j k => tokenCovariance (S i) j k

omit [NeZero N] in
/-- The row covariance-form matrix equals the covariance of its token observables. -/
theorem attention_hessian_eq_covariance (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    attentionHessian S i = attentionTokenCovariance S i := by
  ext j k
  exact hessianLogZ_eq_tokenCovariance (S i) j k

end AttentionInformationGeometry
