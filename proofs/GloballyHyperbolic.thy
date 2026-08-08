theory GloballyHyperbolic
  imports Main
begin

text ‹Cauchy surface intersection theorems for non-spacelike curves.›

record Spacetime =
  events :: "nat set"
  causal_rel :: "(nat × nat) set"

definition is_non_spacelike_curve :: "Spacetime ⇒ (nat ⇒ nat) ⇒ bool" where
  "is_non_spacelike_curve S γ ⟷ (∀t. (γ t, γ (t + 1)) ∈ causal_rel S)"

definition is_cauchy_surface :: "Spacetime ⇒ nat set ⇒ bool" where
  "is_cauchy_surface S Σ ⟷ (∀γ. is_non_spacelike_curve S γ ⟶ (∃!t. γ t ∈ Σ))"

theorem cauchy_surface_intersection:
  assumes "is_cauchy_surface S Σ"
  assumes "is_non_spacelike_curve S γ"
  shows "∃!t. γ t ∈ Σ"
  using assms unfolding is_cauchy_surface_def by simp

end
