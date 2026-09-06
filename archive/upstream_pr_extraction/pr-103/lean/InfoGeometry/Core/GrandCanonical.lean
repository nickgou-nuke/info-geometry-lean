import InfoGeometry.GrandCanonical.Core
import InfoGeometry.GrandCanonical.ResponseMatrix

/-!
# Core Grand Canonical

Core façade re-exporting the finite grand-canonical model and key theorems.
-/

namespace InfoGeometry.Core


section FiniteModel

open InfoGeometry.GrandCanonical

variable {α : Type*} [Fintype α] [Nonempty α]

noncomputable abbrev partition (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.partition params β

noncomputable abbrev potential (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.potential params β

noncomputable abbrev gibbsWeight (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ) (x : α) : ℝ :=
  InfoGeometry.GrandCanonical.gibbsWeight params β x

noncomputable abbrev mean (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.mean params β

noncomputable abbrev variance (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.variance params β

noncomputable abbrev hessian (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.hessian params β

lemma gc_partition_pos (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ) :
    0 < partition params β :=
  partition_pos params β

lemma gc_gibbsWeight_sum_one (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ) :
    ∑ x, gibbsWeight params β x = 1 :=
  gibbsWeight_sum_one params β

lemma gc_potential_deriv_eq_neg_mean (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ) :
    deriv (potential params) β = -mean params β :=
  potential_deriv_eq_neg_mean params β

lemma gc_potential_second_derivative_eq_variance
    (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ) :
    hessian params β = variance params β :=
  potential_second_derivative_eq_variance params β

lemma gc_hessian_eq_variance
    (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ) :
    hessian params β = variance params β :=
  gc_potential_second_derivative_eq_variance params β

lemma gc_hessian_nonneg (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ) :
    0 ≤ hessian params β :=
  hessian_nonneg params β

lemma gc_variance_pos_of_energy_ne
    (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ)
    {x y : α} (hxy : params.energy x ≠ params.energy y) :
    0 < variance params β :=
  InfoGeometry.GrandCanonical.variance_pos_of_energy_ne params β hxy

lemma gc_hessian_pos_of_energy_ne
    (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ)
    {x y : α} (hxy : params.energy x ≠ params.energy y) :
    0 < hessian params β := by
  rw [gc_hessian_eq_variance]
  exact gc_variance_pos_of_energy_ne params β hxy

lemma gc_spinodal_iff_variance_eq_zero
    (params : InfoGeometry.GrandCanonical.GrandCanonicalParams α) (β : ℝ) :
    InfoGeometry.GrandCanonical.Spinodal params β ↔ variance params β = 0 :=
  spinodal_iff_variance_eq_zero params β

end FiniteModel

section FiniteGrandCanonicalModel

open InfoGeometry.GrandCanonical

variable {α : Type*} [Fintype α] [Nonempty α]

noncomputable abbrev shiftedEnergy
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (μ : ℝ) (x : α) : ℝ :=
  InfoGeometry.GrandCanonical.shiftedEnergy params μ x

noncomputable abbrev partitionGC
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.partitionGC params β μ

noncomputable abbrev potentialGC
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.potentialGC params β μ

noncomputable abbrev gibbsWeightGC
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) (x : α) : ℝ :=
  InfoGeometry.GrandCanonical.gibbsWeightGC params β μ x

noncomputable abbrev meanShift
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.meanShift params β μ

noncomputable abbrev meanNumber
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.meanNumber params β μ

lemma gc2_partition_pos
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) :
    0 < partitionGC params β μ :=
  partitionGC_pos params β μ

lemma gc2_gibbsWeight_sum_one
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) :
    ∑ x, gibbsWeightGC params β μ x = 1 :=
  gibbsWeightGC_sum_one params β μ

lemma gc2_gibbsWeight_nonneg
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) (x : α) :
    0 ≤ gibbsWeightGC params β μ x :=
  gibbsWeightGC_nonneg params β μ x

lemma gc2_gibbsWeight_pos
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) (x : α) :
    0 < gibbsWeightGC params β μ x :=
  gibbsWeightGC_pos params β μ x

lemma gc2_potential_deriv_beta_eq_neg_meanShift
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) :
    deriv (fun t => potentialGC params t μ) β = -meanShift params β μ :=
  potentialGC_deriv_beta_eq_neg_meanShift params β μ

lemma gc2_potential_deriv_mu_eq_beta_meanNumber
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) :
    deriv (fun t => potentialGC params β t) μ = β * meanNumber params β μ :=
  potentialGC_deriv_mu_eq_beta_meanNumber params β μ

end FiniteGrandCanonicalModel

namespace GrandCanonical.TwoParam

open InfoGeometry.GrandCanonical

variable {α : Type*} [Fintype α] [Nonempty α]

noncomputable abbrev betaResponse
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaResponse params β μ

noncomputable abbrev muResponse
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muResponse params β μ

noncomputable abbrev betaHessian
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaHessian params β μ

noncomputable abbrev muHessian
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muHessian params β μ

noncomputable abbrev betaMuHessian
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaMuHessian params β μ

noncomputable abbrev muBetaHessian
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muBetaHessian params β μ

noncomputable abbrev responseMatrix
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) :
      InfoGeometry.GrandCanonical.ResponseMatrix2 :=
  InfoGeometry.GrandCanonical.responseMatrix params β μ

abbrev Spinodal2D
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) : Prop :=
  InfoGeometry.GrandCanonical.Spinodal2D params β μ

lemma gc2_betaResponse_eq_neg_meanShift
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) :
    betaResponse params β μ = -meanShift params β μ :=
  InfoGeometry.GrandCanonical.betaResponse_eq_neg_meanShift params β μ

lemma gc2_muResponse_eq_beta_meanNumber
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) :
    muResponse params β μ = β * meanNumber params β μ :=
  InfoGeometry.GrandCanonical.muResponse_eq_beta_meanNumber params β μ

omit [Nonempty α] in
lemma gc2_responseMatrix_symmetric
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ)
    (hMixed : betaMuHessian params β μ = muBetaHessian params β μ) :
    InfoGeometry.GrandCanonical.ResponseMatrix2.Symmetric (responseMatrix params β μ) :=
  InfoGeometry.GrandCanonical.responseMatrix_symmetric params β μ hMixed

omit [Nonempty α] in
lemma gc2_responseMatrix_positiveSemidefinite
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ)
    (hββ : 0 ≤ betaHessian params β μ)
    (hμμ : 0 ≤ muHessian params β μ)
    (hdet : 0 ≤ (responseMatrix params β μ).det) :
    InfoGeometry.GrandCanonical.ResponseMatrix2.PositiveSemidefinite
      (responseMatrix params β μ) :=
  InfoGeometry.GrandCanonical.responseMatrix_positiveSemidefinite params β μ hββ hμμ hdet

omit [Nonempty α] in
lemma gc2_spinodal2D_iff_det_eq_zero
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (β μ : ℝ) :
    Spinodal2D params β μ ↔ (responseMatrix params β μ).det = 0 :=
  InfoGeometry.GrandCanonical.spinodal2D_iff_det_eq_zero params β μ

end GrandCanonical.TwoParam

end InfoGeometry.Core
