/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AttentionInformationGeometry
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Query-space derivatives of finite attention

Keys are genuine continuous real covectors. The query potential is the existing
finite log-partition function composed with their scaled evaluation map. This
file proves its Fréchet derivative, differentiates the actual log probabilities,
and identifies the second derivative along each query line with Fisher
information. The temperature factors are explicit.

The resulting form is semidefinite. For nonzero inverse temperature its null
directions are exactly those on which every key has the same evaluation. No
positive definite metric, physical CPT action, or Transformer evolution law is
assumed or inferred.
-/

noncomputable section

open scoped BigOperators
open AttentionInformationGeometry

namespace InfoGeometry.Canonical.AttentionQueryGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : ℕ} [NeZero M]

/-- Logits obtained by evaluating the key covectors at a query. -/
def queryLogits (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) : Fin M → ℝ :=
  fun j => β * K j q

/-- The finite query-space log-partition potential. -/
def queryPotential (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) : ℝ :=
  Real.log (partitionZ (queryLogits K β q))

/-- Attention probabilities on the fixed finite family of keys. -/
def queryWeight (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) (j : Fin M) : ℝ :=
  softmaxProb (queryLogits K β q) j

/-- The softmax-weighted mean key, still a continuous covector. -/
def meanKey (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) : E →L[ℝ] ℝ :=
  ∑ j, queryWeight K β q j • K j

omit [NeZero M] in
/-- Pulling log-partition back along the actual query line gives the existing
affine-logit analytic path. -/
theorem queryPotential_line_eq (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q u : E) :
    (fun t : ℝ => queryPotential K β (q + t • u)) =
      logPartitionAlong (queryLogits K β q) (fun j => β * K j u) := by
  funext t
  rw [logPartitionAlong_eq_log_partition]
  unfold queryPotential
  congr 2
  funext j
  simp [queryLogits, map_add, map_smul]
  ring

/-- The genuine Fréchet derivative is inverse temperature times the mean key. -/
theorem hasFDerivAt_queryPotential
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) :
    HasFDerivAt (queryPotential K β) (β • meanKey K β q) q := by
  have hterm (j : Fin M) :
      HasFDerivAt (fun x : E => Real.exp (β * K j x))
        (Real.exp (β * K j q) • (β • K j)) q :=
    ((K j).hasFDerivAt.const_mul β).exp
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j)
  have hlog := hsum.log (partitionZ_ne_zero (queryLogits K β q))
  change HasFDerivAt (queryPotential K β)
    ((partitionZ (queryLogits K β q))⁻¹ •
      ∑ j, Real.exp (β * K j q) • (β • K j)) q at hlog
  convert hlog using 1
  ext u
  simp only [meanKey, smul_apply, sum_apply,
    smul_eq_mul, Finset.mul_sum, queryWeight, softmaxProb, queryLogits]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Explicit value of the Fréchet derivative on a query direction. -/
theorem fderiv_queryPotential_apply
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q u : E) :
    fderiv ℝ (queryPotential K β) q u =
      β * ∑ j, queryWeight K β q j * K j u := by
  rw [(hasFDerivAt_queryPotential K β q).fderiv]
  simp [meanKey]

/-- The first derivative along a query line is the mean key evaluation. -/
theorem queryPotential_line_deriv
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q u : E) :
    deriv (fun t : ℝ => queryPotential K β (q + t • u)) 0 =
      β * ∑ j, queryWeight K β q j * K j u := by
  rw [queryPotential_line_eq, logPartitionAlong_smul_directional_deriv]
  rfl

/-- The second derivative along a query line is the covariance of key
evaluations, multiplied by the square of inverse temperature. -/
theorem queryPotential_line_secondDeriv
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q u : E) :
    deriv (fun t => deriv (fun s : ℝ => queryPotential K β (q + s • u)) t) 0 =
      β ^ 2 * ∑ j, queryWeight K β q j *
        (K j u - ∑ l, queryWeight K β q l * K l u) ^ 2 := by
  rw [queryPotential_line_eq, logPartitionAlong_smul_secondDeriv,
    logPartitionAlong_secondDeriv_eq_variance]
  rfl

/-- Derivative of the actual log attention probability along a query line. -/
theorem log_queryWeight_line_deriv
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q u : E) (j : Fin M) :
    deriv (fun t : ℝ => Real.log (queryWeight K β (q + t • u) j)) 0 =
      β * (K j u - ∑ l, queryWeight K β q l * K l u) := by
  have hfun : (fun t : ℝ => Real.log (queryWeight K β (q + t • u) j)) =
      fun t : ℝ => β * K j (q + t • u) - queryPotential K β (q + t • u) := by
    funext t
    simp only [queryWeight, softmaxProb, queryPotential]
    rw [Real.log_div (Real.exp_ne_zero _)
      (partitionZ_ne_zero (queryLogits K β (q + t • u))), Real.log_exp]
    rfl
  have hlin : HasDerivAt (fun t : ℝ => β * K j (q + t • u)) (β * K j u) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).mul_const (K j u)).const_add (K j q)).const_mul β
    simpa [map_add, map_smul] using h
  have hpath : DifferentiableAt ℝ (fun t : ℝ => queryPotential K β (q + t • u)) 0 := by
    rw [queryPotential_line_eq]
    exact (InfoGeometry.Analytic.hasDerivAt_logSumExp
      (fun l => Real.exp (queryLogits K β q l)) (fun l => β * K l u)
      (fun l => Real.exp_pos _) 0).differentiableAt
  rw [hfun]
  change deriv
    ((fun t : ℝ => β * K j (q + t • u)) -
      (fun t : ℝ => queryPotential K β (q + t • u))) 0 = _
  rw [deriv_sub hlin.differentiableAt hpath, hlin.deriv,
    queryPotential_line_deriv]
  ring

/-- Fisher information evaluated on a direction, defined from actual
log-probability derivatives rather than a stipulated covariance. -/
def queryFisher (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q u : E) : ℝ :=
  ∑ j, queryWeight K β q j *
    (deriv (fun t : ℝ => Real.log (queryWeight K β (q + t • u) j)) 0) ^ 2

/-- Exact temperature-scaled covariance formula for query Fisher information. -/
theorem queryFisher_eq_variance
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q u : E) :
    queryFisher K β q u =
      β ^ 2 * ∑ j, queryWeight K β q j *
        (K j u - ∑ l, queryWeight K β q l * K l u) ^ 2 := by
  unfold queryFisher
  simp_rw [log_queryWeight_line_deriv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Query Fisher information equals the genuine second line derivative. -/
theorem queryFisher_eq_secondDeriv
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q u : E) :
    queryFisher K β q u =
      deriv (fun t => deriv (fun s : ℝ => queryPotential K β (q + s • u)) t) 0 := by
  rw [queryFisher_eq_variance, queryPotential_line_secondDeriv]

/-- The query Fisher form is nonnegative for every real inverse temperature. -/
theorem queryFisher_nonneg
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q u : E) :
    0 ≤ queryFisher K β q u := by
  unfold queryFisher
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (le_of_lt (softmaxProb_pos (queryLogits K β q) j)) (sq_nonneg _)

/-- At nonzero inverse temperature, curvature is positive exactly when two
keys distinguish the query direction. -/
theorem queryFisher_pos_iff
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (hβ : β ≠ 0) (q u : E) :
    0 < queryFisher K β q u ↔ ∃ j k, K j u ≠ K k u := by
  rw [queryFisher_eq_secondDeriv, queryPotential_line_eq,
    logPartitionAlong_secondDeriv_eq_hessian_quadratic,
    hessianLogZ_positive_iff_nonconstant]
  constructor
  · rintro ⟨j, k, h⟩
    exact ⟨j, k, fun heq => h (congrArg (β * ·) heq)⟩
  · rintro ⟨j, k, h⟩
    exact ⟨j, k, fun heq => h (mul_left_cancel₀ hβ heq)⟩

/-- The exact null-direction criterion; positive definiteness requires an
additional separation condition on the family of keys. -/
theorem queryFisher_eq_zero_iff
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (hβ : β ≠ 0) (q u : E) :
    queryFisher K β q u = 0 ↔ ∀ j k, K j u = K k u := by
  have hnonneg := queryFisher_nonneg K β q u
  have hpos := queryFisher_pos_iff K β hβ q u
  constructor
  · intro hz j k
    by_contra hne
    have hp := hpos.mpr ⟨j, k, hne⟩
    linarith
  · intro h
    apply le_antisymm _ hnonneg
    by_contra hnle
    obtain ⟨j, k, hne⟩ := hpos.mp (lt_of_not_ge hnle)
    exact hne (h j k)

end InfoGeometry.Canonical.AttentionQueryGeometry
