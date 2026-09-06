import InfoGeometry.GrandCanonical.Core

/-!
# Core Grand Canonical

Core façade re-exporting the finite grand-canonical model and key theorems.
-/

namespace InfoGeometry.Core

abbrev GrandCanonicalParams := InfoGeometry.GrandCanonical.GrandCanonicalParams

section FiniteModel

open InfoGeometry.GrandCanonical

variable {α : Type _} [Fintype α] [Nonempty α]

noncomputable abbrev partition (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.partition params β

noncomputable abbrev potential (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.potential params β

noncomputable abbrev gibbsWeight (params : GrandCanonicalParams α) (β : ℝ) (x : α) : ℝ :=
  InfoGeometry.GrandCanonical.gibbsWeight params β x

noncomputable abbrev mean (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.mean params β

noncomputable abbrev variance (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.variance params β

noncomputable abbrev hessian (params : GrandCanonicalParams α) (β : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.hessian params β

abbrev Spinodal (params : GrandCanonicalParams α) (β : ℝ) : Prop :=
  InfoGeometry.GrandCanonical.Spinodal params β

lemma gc_partition_pos (params : GrandCanonicalParams α) (β : ℝ) :
    0 < partition params β :=
  partition_pos params β

lemma gc_gibbsWeight_sum_one (params : GrandCanonicalParams α) (β : ℝ) :
    ∑ x, gibbsWeight params β x = 1 :=
  gibbsWeight_sum_one params β

lemma gc_potential_deriv_eq_neg_mean (params : GrandCanonicalParams α) (β : ℝ) :
    deriv (potential params) β = -mean params β :=
  potential_deriv_eq_neg_mean params β

lemma gc_potential_second_derivative_eq_variance
    (params : GrandCanonicalParams α) (β : ℝ) :
    hessian params β = variance params β :=
  potential_second_derivative_eq_variance params β

lemma gc_hessian_nonneg (params : GrandCanonicalParams α) (β : ℝ) :
    0 ≤ hessian params β :=
  hessian_nonneg params β

lemma gc_spinodal_iff_variance_eq_zero
    (params : GrandCanonicalParams α) (β : ℝ) :
    Spinodal params β ↔ variance params β = 0 :=
  spinodal_iff_variance_eq_zero params β

end FiniteModel

end InfoGeometry.Core
