import InfoGeometry.GrandCanonical.Core

/-!
# Core Derivatives

Bridge module exposing derivative identities used by the core API.
-/

namespace InfoGeometry.Core

open InfoGeometry.GrandCanonical

section GrandCanonical

variable {α : Type _} [Fintype α] [Nonempty α]

/-- Core alias for the grand-canonical first-derivative identity. -/
lemma gc_potential_deriv_eq_neg_mean
    (params : GrandCanonicalParams α) (β : ℝ) :
    deriv (potential params) β = -mean params β :=
  potential_deriv_eq_neg_mean params β

/-- Core alias for the grand-canonical Hessian/variance identity. -/
lemma gc_potential_second_derivative_eq_variance
    (params : GrandCanonicalParams α) (β : ℝ) :
    hessian params β = variance params β :=
  potential_second_derivative_eq_variance params β

/-- Core alias for nonnegativity of the grand-canonical Hessian. -/
lemma gc_hessian_nonneg
    (params : GrandCanonicalParams α) (β : ℝ) :
    0 ≤ hessian params β :=
  hessian_nonneg params β

end GrandCanonical

end InfoGeometry.Core
