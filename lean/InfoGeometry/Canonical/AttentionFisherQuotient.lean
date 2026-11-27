/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AttentionQueryGeometry
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# The full attention Hessian and its Fisher quotient

The second derivative is a continuous bilinear map on query space, proved to be
the Fréchet derivative of the actual first derivative. The null submodule is
the intersection of the kernels of the key differences. Its algebraic quotient
carries the descended positive definite form at every nonzero inverse
temperature. The reference-key affine gauge, rather than the unmodified
potential, descends to that quotient.
-/

noncomputable section
open scoped BigOperators
open AttentionInformationGeometry

namespace InfoGeometry.Canonical.AttentionQueryGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : ℕ} [NeZero M]

omit [NeZero M] in
@[simp] theorem meanKey_apply (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q u : E) :
    meanKey K β q u = ∑ j, queryWeight K β q j * K j u := by
  simp [meanKey]

theorem queryWeight_sum (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) :
    ∑ j, queryWeight K β q j = 1 := softmaxProb_sum _

theorem queryWeight_eq_exp (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E)
    (j : Fin M) :
    queryWeight K β q j = Real.exp (β * K j q - queryPotential K β q) := by
  simp [queryWeight, softmaxProb, queryPotential, queryLogits, Real.exp_sub,
    Real.exp_log (partitionZ_pos (queryLogits K β q))]

/-- The derivative of each actual attention probability. -/
theorem hasFDerivAt_queryWeight (K : Fin M → E →L[ℝ] ℝ) (β : ℝ)
    (q : E) (j : Fin M) :
    HasFDerivAt (fun x => queryWeight K β x j)
      ((β * queryWeight K β q j) • (K j - meanKey K β q)) q := by
  have h := (((K j).hasFDerivAt.const_mul β).sub
    (hasFDerivAt_queryPotential K β q)).exp
  convert h using 1
  · funext x
    exact queryWeight_eq_exp K β x j
  · ext u
    simp only [smul_apply, sub_apply, Pi.sub_apply, smul_eq_mul]
    rw [← queryWeight_eq_exp K β q j]
    ring

/-- The continuous bilinear second derivative, in the form produced by the
product rule for the weighted mean key. -/
def queryHessian (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  β • ∑ j, ((β * queryWeight K β q j) •
    (K j - meanKey K β q)).smulRight (K j)

/-- Full Fréchet differentiability of the gradient, on the original query
space. This theorem is stronger than a second derivative along a line. -/
theorem hasFDerivAt_fderiv_queryPotential (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (q : E) :
    HasFDerivAt (fderiv ℝ (queryPotential K β)) (queryHessian K β q) q := by
  have h := (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (hasFDerivAt_queryWeight K β q j).smul_const (K j))).const_smul β
  have hf : fderiv ℝ (queryPotential K β) = fun x => β • meanKey K β x := by
    funext x
    exact (hasFDerivAt_queryPotential K β x).fderiv
  rw [hf]
  exact h

theorem fderiv_fderiv_queryPotential (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (q : E) :
    fderiv ℝ (fderiv ℝ (queryPotential K β)) q = queryHessian K β q :=
  (hasFDerivAt_fderiv_queryPotential K β q).fderiv

omit [NeZero M] in
theorem queryHessian_apply_uncentered (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (q u v : E) :
    queryHessian K β q u v = β ^ 2 *
      ((∑ j, queryWeight K β q j * K j u * K j v) -
        meanKey K β q u * meanKey K β q v) := by
  simp only [queryHessian, smul_apply, sum_apply, ContinuousLinearMap.smulRight_apply,
    sub_apply, smul_eq_mul]
  calc
    β * ∑ j, (β * queryWeight K β q j *
        (K j u - meanKey K β q u)) * K j v =
      β ^ 2 * ∑ j, (queryWeight K β q j * K j u * K j v -
        meanKey K β q u * (queryWeight K β q j * K j v)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← meanKey_apply]

/-- The mixed Hessian is the covariance of the two key evaluations. -/
theorem queryHessian_apply_covariance (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (q u v : E) :
    queryHessian K β q u v = β ^ 2 * ∑ j, queryWeight K β q j *
      (K j u - meanKey K β q u) * (K j v - meanKey K β q v) := by
  rw [queryHessian_apply_uncentered]
  congr 1
  symm
  calc
    ∑ j, queryWeight K β q j * (K j u - meanKey K β q u) *
        (K j v - meanKey K β q v) =
      ∑ j, (queryWeight K β q j * K j u * K j v -
        (queryWeight K β q j * K j u) * meanKey K β q v -
        (queryWeight K β q j * K j v) * meanKey K β q u +
        queryWeight K β q j * (meanKey K β q u * meanKey K β q v)) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        ← meanKey_apply, queryWeight_sum, one_mul]
      ring

theorem queryHessian_symmetric (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (q u v : E) : queryHessian K β q u v = queryHessian K β q v u := by
  rw [queryHessian_apply_covariance, queryHessian_apply_covariance]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem queryHessian_diagonal_eq_fisher (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (q u : E) : queryHessian K β q u u = queryFisher K β q u := by
  rw [queryHessian_apply_covariance, queryFisher_eq_variance]
  simp only [meanKey_apply, pow_two, mul_assoc]

/-- The exact, temperature-independent null directions of the key family. -/
def queryNullSpace (K : Fin M → E →L[ℝ] ℝ) : Submodule ℝ E :=
  ⨅ j, (K j - K 0).ker

@[simp] theorem mem_queryNullSpace (K : Fin M → E →L[ℝ] ℝ) (u : E) :
    u ∈ queryNullSpace K ↔ ∀ j, K j u = K 0 u := by
  simp [queryNullSpace, sub_eq_zero]

theorem mem_queryNullSpace_iff_all_keys (K : Fin M → E →L[ℝ] ℝ) (u : E) :
    u ∈ queryNullSpace K ↔ ∀ j k, K j u = K k u := by
  rw [mem_queryNullSpace]
  constructor
  · intro h j k
    exact (h j).trans (h k).symm
  · intro h j
    exact h j 0

theorem meanKey_apply_null (K : Fin M → E →L[ℝ] ℝ) (β : ℝ)
    (q u : E) (hu : u ∈ queryNullSpace K) : meanKey K β q u = K 0 u := by
  rw [meanKey_apply]
  simp_rw [(mem_queryNullSpace K u).mp hu]
  rw [← Finset.sum_mul, queryWeight_sum, one_mul]

theorem queryHessian_null_left (K : Fin M → E →L[ℝ] ℝ) (β : ℝ)
    (q u v : E) (hu : u ∈ queryNullSpace K) : queryHessian K β q u v = 0 := by
  rw [queryHessian_apply_covariance, meanKey_apply_null K β q u hu]
  simp [(mem_queryNullSpace K u).mp hu]

theorem queryHessian_diagonal_eq_zero_iff (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (hβ : β ≠ 0) (q u : E) :
    queryHessian K β q u u = 0 ↔ u ∈ queryNullSpace K := by
  rw [queryHessian_diagonal_eq_fisher, queryFisher_eq_zero_iff K β hβ,
    mem_queryNullSpace_iff_all_keys]

/-- The native algebraic bilinear map underlying the continuous Hessian. -/
def queryBilinear (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ where
  toFun u := (queryHessian K β q u).toLinearMap
  map_add' u v := by ext w; simp
  map_smul' r u := by ext w; simp

omit [NeZero M] in
@[simp] theorem queryBilinear_apply (K : Fin M → E →L[ℝ] ℝ) (β : ℝ)
    (q u v : E) : queryBilinear K β q u v = queryHessian K β q u v := rfl

theorem queryNullSpace_le_ker (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) :
    queryNullSpace K ≤ (queryBilinear K β q).ker := by
  intro u hu
  ext v
  exact queryHessian_null_left K β q u v hu

theorem queryNullSpace_le_flip_ker (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) :
    queryNullSpace K ≤ (queryBilinear K β q).flip.ker := by
  intro u hu
  ext v
  change queryHessian K β q v u = 0
  rw [queryHessian_symmetric]
  exact queryHessian_null_left K β q u v hu

abbrev QueryQuotient (K : Fin M → E →L[ℝ] ℝ) := E ⧸ queryNullSpace K

/-- The actual descended bilinear form on the query quotient. -/
def quotientFisher (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) :
    QueryQuotient K →ₗ[ℝ] QueryQuotient K →ₗ[ℝ] ℝ :=
  (queryBilinear K β q).liftQ₂ (queryNullSpace K) (queryNullSpace K)
    (queryNullSpace_le_ker K β q) (queryNullSpace_le_flip_ker K β q)

@[simp] theorem quotientFisher_mk (K : Fin M → E →L[ℝ] ℝ) (β : ℝ)
    (q u v : E) :
    quotientFisher K β q (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      queryHessian K β q u v := rfl

theorem quotientFisher_symmetric (K : Fin M → E →L[ℝ] ℝ) (β : ℝ)
    (q : E) (x y : QueryQuotient K) :
    quotientFisher K β q x y = quotientFisher K β q y x := by
  induction x using Submodule.Quotient.induction_on with
  | _ u =>
    induction y using Submodule.Quotient.induction_on with
    | _ v => exact queryHessian_symmetric K β q u v

theorem quotientFisher_nonneg (K : Fin M → E →L[ℝ] ℝ) (β : ℝ)
    (q : E) (x : QueryQuotient K) : 0 ≤ quotientFisher K β q x x := by
  induction x using Submodule.Quotient.induction_on with
  | _ u =>
    rw [quotientFisher_mk, queryHessian_diagonal_eq_fisher]
    exact queryFisher_nonneg K β q u

/-- Positive definiteness is proved on the quotient; no key-separation
assumption is imposed on the original query space. -/
theorem quotientFisher_pos (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (hβ : β ≠ 0)
    (q : E) (x : QueryQuotient K) (hx : x ≠ 0) :
    0 < quotientFisher K β q x x := by
  have hn := quotientFisher_nonneg K β q x
  apply lt_of_le_of_ne hn
  intro hz
  apply hx
  induction x using Submodule.Quotient.induction_on with
  | _ u =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply (queryHessian_diagonal_eq_zero_iff K β hβ q u).mp
    exact hz.symm

theorem quotientFisher_nondegenerate (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (hβ : β ≠ 0) (q : E) : (quotientFisher K β q).Nondegenerate := by
  have hl : (quotientFisher K β q).SeparatingLeft := by
    intro x h
    by_contra hx
    exact (ne_of_gt (quotientFisher_pos K β hβ q x hx)) (h x)
  refine ⟨hl, ?_⟩
  intro y h
  apply hl y
  intro x
  rw [quotientFisher_symmetric]
  exact h x

/-- Common logit shifts leave the probability vector unchanged. -/
theorem queryWeight_add_null (K : Fin M → E →L[ℝ] ℝ) (β : ℝ)
    (q n : E) (hn : n ∈ queryNullSpace K) (j : Fin M) :
    queryWeight K β (q + n) j = queryWeight K β q j := by
  have hkey := (mem_queryNullSpace K n).mp hn
  have hZ : partitionZ (queryLogits K β (q + n)) =
      partitionZ (queryLogits K β q) * Real.exp (β * K 0 n) := by
    simp only [partitionZ, queryLogits, map_add, mul_add, Real.exp_add, hkey,
      Finset.sum_mul]
  simp only [queryWeight, softmaxProb, queryLogits, map_add, mul_add, Real.exp_add,
    hkey, hZ]
  field_simp [Real.exp_ne_zero]

theorem queryHessian_add_null (K : Fin M → E →L[ℝ] ℝ) (β : ℝ)
    (q n : E) (hn : n ∈ queryNullSpace K) :
    queryHessian K β (q + n) = queryHessian K β q := by
  simp only [queryHessian, meanKey, queryWeight_add_null K β q n hn]

theorem quotientFisher_add_null (K : Fin M → E →L[ℝ] ℝ) (β : ℝ)
    (q n : E) (hn : n ∈ queryNullSpace K) :
    quotientFisher K β (q + n) = quotientFisher K β q := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  induction x using Submodule.Quotient.induction_on with
  | _ u =>
    induction y using Submodule.Quotient.induction_on with
    | _ v => simp only [quotientFisher_mk, queryHessian_add_null K β q n hn]

/-- The family of algebraic Fisher metrics descends in its base point as well
as in its two tangent arguments. -/
def quotientFisherMetric (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) :
    QueryQuotient K → QueryQuotient K →ₗ[ℝ] QueryQuotient K →ₗ[ℝ] ℝ :=
  Quotient.lift (quotientFisher K β) (by
    intro x y hxy
    have hmem := (Submodule.quotientRel_def (queryNullSpace K)).mp hxy
    have h := quotientFisher_add_null K β y (x - y) hmem
    have hy : y + (x - y) = x := by abel
    simpa only [hy] using h)

@[simp] theorem quotientFisherMetric_mk (K : Fin M → E →L[ℝ] ℝ) (β : ℝ)
    (q : E) :
    quotientFisherMetric K β (Submodule.Quotient.mk q) = quotientFisher K β q := rfl

theorem quotientFisherMetric_pos (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (hβ : β ≠ 0) (q x : QueryQuotient K) (hx : x ≠ 0) :
    0 < quotientFisherMetric K β q x x := by
  induction q using Submodule.Quotient.induction_on with
  | _ q => exact quotientFisher_pos K β hβ q x hx

theorem quotientFisherMetric_nondegenerate (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (hβ : β ≠ 0) (q : QueryQuotient K) :
    (quotientFisherMetric K β q).Nondegenerate := by
  induction q using Submodule.Quotient.induction_on with
  | _ q => exact quotientFisher_nondegenerate K β hβ q

/-- A native inner-product core at a quotient base point. Its positivity fields
are proved from the exact Fisher nullspace theorem. -/
@[instance_reducible]
def quotientFisherCore (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (hβ : β ≠ 0)
    (q : QueryQuotient K) : InnerProductSpace.Core ℝ (QueryQuotient K) where
  inner := fun x y => quotientFisherMetric K β q x y
  conj_inner_symm x y := by
    change quotientFisherMetric K β q y x = quotientFisherMetric K β q x y
    induction q using Submodule.Quotient.induction_on with
    | _ q => exact quotientFisher_symmetric K β q y x
  re_inner_nonneg x := by
    change 0 ≤ quotientFisherMetric K β q x x
    induction q using Submodule.Quotient.induction_on with
    | _ q => exact quotientFisher_nonneg K β q x
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra hne
    exact (ne_of_gt (quotientFisherMetric_pos K β hβ q x hne)) hx

/-- The actual Fisher norm and metric on the quotient tangent space at `q`.
This is an explicit structure, not a global competing norm instance. -/
@[instance_reducible]
def quotientFisherNormedAddCommGroup (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (hβ : β ≠ 0) (q : QueryQuotient K) : NormedAddCommGroup (QueryQuotient K) :=
  letI : InnerProductSpace.Core ℝ (QueryQuotient K) := quotientFisherCore K β hβ q
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

/-- The Fisher inner product with its induced norm, on the actual quotient. -/
@[instance_reducible]
def quotientFisherInnerProductSpace (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (hβ : β ≠ 0) (q : QueryQuotient K) :
    letI : NormedAddCommGroup (QueryQuotient K) := quotientFisherNormedAddCommGroup K β hβ q
    letI : SeminormedAddCommGroup (QueryQuotient K) :=
      (quotientFisherNormedAddCommGroup K β hβ q).toSeminormedAddCommGroup
    InnerProductSpace ℝ (QueryQuotient K) := by
  letI : InnerProductSpace.Core ℝ (QueryQuotient K) := quotientFisherCore K β hβ q
  exact InnerProductSpace.ofCore (quotientFisherCore K β hβ q).toCore

/-- The unmodified potential has an affine defect along null directions. -/
theorem queryPotential_add_null (K : Fin M → E →L[ℝ] ℝ) (β : ℝ)
    (q n : E) (hn : n ∈ queryNullSpace K) :
    queryPotential K β (q + n) = queryPotential K β q + β * K 0 n := by
  have hkey := (mem_queryNullSpace K n).mp hn
  have hZ : partitionZ (queryLogits K β (q + n)) =
      partitionZ (queryLogits K β q) * Real.exp (β * K 0 n) := by
    simp only [partitionZ, queryLogits, map_add, mul_add, Real.exp_add, hkey,
      Finset.sum_mul]
  simp only [queryPotential, hZ,
    Real.log_mul (partitionZ_ne_zero _) (Real.exp_ne_zero _), Real.log_exp]

/-- The affine gauge obtained by subtracting the reference key. -/
def gaugedQueryPotential (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) : ℝ :=
  queryPotential K β q - β * K 0 q

theorem hasFDerivAt_gaugedQueryPotential (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (q : E) :
    HasFDerivAt (gaugedQueryPotential K β)
      (β • meanKey K β q - β • K 0) q :=
  (hasFDerivAt_queryPotential K β q).sub ((K 0).hasFDerivAt.const_mul β)

/-- The affine gauge changes the first derivative but leaves the full Hessian
unchanged. -/
theorem hasFDerivAt_fderiv_gaugedQueryPotential (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (q : E) :
    HasFDerivAt (fderiv ℝ (gaugedQueryPotential K β)) (queryHessian K β q) q := by
  have hf : fderiv ℝ (gaugedQueryPotential K β) =
      fun x => fderiv ℝ (queryPotential K β) x - β • K 0 := by
    funext x
    rw [(hasFDerivAt_gaugedQueryPotential K β x).fderiv,
      (hasFDerivAt_queryPotential K β x).fderiv]
  rw [hf]
  exact (hasFDerivAt_fderiv_queryPotential K β q).sub_const _

theorem gaugedQueryPotential_add_null (K : Fin M → E →L[ℝ] ℝ) (β : ℝ)
    (q n : E) (hn : n ∈ queryNullSpace K) :
    gaugedQueryPotential K β (q + n) = gaugedQueryPotential K β q := by
  simp only [gaugedQueryPotential, queryPotential_add_null K β q n hn, map_add]
  ring

/-- The potential itself descends after the necessary affine gauge. -/
def quotientQueryPotential (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) :
    QueryQuotient K → ℝ :=
  Quotient.lift (gaugedQueryPotential K β) (by
    intro x y hxy
    have hmem := (Submodule.quotientRel_def (queryNullSpace K)).mp hxy
    have h := gaugedQueryPotential_add_null K β y (x - y) hmem
    have hy : y + (x - y) = x := by abel
    simpa only [hy] using h)

@[simp] theorem quotientQueryPotential_mk (K : Fin M → E →L[ℝ] ℝ)
    (β : ℝ) (q : E) :
    quotientQueryPotential K β (Submodule.Quotient.mk q) =
      queryPotential K β q - β * K 0 q := rfl

end InfoGeometry.Canonical.AttentionQueryGeometry
