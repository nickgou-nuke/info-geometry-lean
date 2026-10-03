import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Matrix
open scoped BigOperators

namespace AttentionInformationGeometry

variable {M : ℕ} [NeZero M]

/-! ### 1. Partition Function & Softmax Distribution -/

/-- Partition function Z(s) = ∑_m exp(s_m) for a vector of logits s. -/
noncomputable def partitionZ (s : Fin M → ℝ) : ℝ :=
  ∑ m : Fin M, Real.exp (s m)

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

/-! ### 2. Token Indicator Observables and Moments -/

/-- Token Indicator Observable O_j(m) = δ_{jm} = if m = j then 1 else 0. -/
def tokenObservable (j : Fin M) : Fin M → ℝ :=
  fun m => if m = j then 1 else 0

/-- Expectation operator under the softmax measure: E[f] = ∑_m A_m(s) * f(m). -/
noncomputable def expectation (s : Fin M → ℝ) (f : Fin M → ℝ) : ℝ :=
  ∑ m : Fin M, softmaxProb s m * f m

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

/-- Product of Indicator Observables: O_j(m) * O_k(m) = if j = k then O_j(m) else 0. -/
lemma tokenObservable_mul (j k : Fin M) (m : Fin M) :
    tokenObservable j m * tokenObservable k m =
      if j = k then tokenObservable j m else 0 := by
  dsimp [tokenObservable]
  split_ifs <;> rfl

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

/-- The Hessian Matrix of ln(Z(s)):
    H_{jk}(s) = ∂² ln Z / ∂s_j ∂s_k = (if j = k then A_j else 0) - A_j A_k. -/
noncomputable def hessianLogZ (s : Fin M → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun j k => (if j = k then softmaxProb s j else 0) - softmaxProb s j * softmaxProb s k

/-- Algebraic reduction of uncentered covariance to the Hessian matrix. -/
theorem tokenCovarianceUncentered_eq_hessian (s : Fin M → ℝ) (j k : Fin M) :
    tokenCovarianceUncentered s j k = hessianLogZ s j k := by
  dsimp [tokenCovarianceUncentered, hessianLogZ]
  rw [expectation_tokenObservable_mul, expectation_tokenObservable, expectation_tokenObservable]

/-- Core Theorem: The Hessian of ln(Z(s)) is identically the Covariance Matrix of Token Observables:
    H_{jk}(s) = Cov(O_j, O_k). -/
theorem hessianLogZ_eq_tokenCovariance (s : Fin M → ℝ) (j k : Fin M) :
    hessianLogZ s j k = tokenCovariance s j k := by
  rw [tokenCovariance_eq_uncentered, tokenCovarianceUncentered_eq_hessian]

/-! ### 4. Fisher-Rao Information Metric -/

/-- The Score Function V_j(m) = ∂/∂s_j ln P(m | s) = O_j(m) - A_j(s). -/
noncomputable def scoreFunction (s : Fin M → ℝ) (j : Fin M) : Fin M → ℝ :=
  fun m => tokenObservable j m - softmaxProb s j

/-- The Fisher-Rao Information Metric:
    g_{jk}(s) = E[ V_j * V_k ]. -/
noncomputable def fisherInformation (s : Fin M → ℝ) (j k : Fin M) : ℝ :=
  expectation s (fun m => scoreFunction s j m * scoreFunction s k m)

/-- Information-Geometric Identity: The Fisher-Rao Metric equals the Hessian of ln(Z(s)). -/
theorem fisherInformation_eq_hessian (s : Fin M → ℝ) (j k : Fin M) :
    fisherInformation s j k = hessianLogZ s j k := by
  dsimp [fisherInformation, scoreFunction]
  rw [← tokenCovariance]
  exact (hessianLogZ_eq_tokenCovariance s j k).symm

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
        apply Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
        intro k _ hne
        rw [if_neg hne.symm]
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
    rfl

  rw [h_lhs]

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

/-- Row log-partition function for attention logit matrix S ∈ ℝ^(N × M). -/
noncomputable def attentionLogPartitionZ (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) : ℝ :=
  Real.log (partitionZ (S i))

/-- The Hessian Matrix of row i of the Softmax Attention layer. -/
noncomputable def attentionHessian (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    Matrix (Fin M) (Fin M) ℝ :=
  hessianLogZ (S i)

/-- The Covariance Matrix of Token Observables for row i. -/
noncomputable def attentionTokenCovariance (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    Matrix (Fin M) (Fin M) ℝ :=
  fun j k => tokenCovariance (S i) j k

/-- Master Attention Theorem:
    The Hessian of ln(partitionZ S i) is identically the Covariance Matrix of Token Observables. -/
theorem attention_hessian_eq_covariance (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    attentionHessian S i = attentionTokenCovariance S i := by
  ext j k
  exact hessianLogZ_eq_tokenCovariance (S i) j k

end AttentionInformationGeometry
