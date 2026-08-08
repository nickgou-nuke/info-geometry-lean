theory CauchySurfaceHyperbolicity
imports Main Topological_Spaces
begin

text ‹
  Foundational topological boundary conditions for a Cauchy surface.
›

typedecl spacetime_point
consts
  causal_precedes :: "spacetime_point ⇒ spacetime_point ⇒ bool" (infix "≼" 50)
  is_cauchy_surface :: "(spacetime_point set) ⇒ bool"

definition globally_hyperbolic :: "bool" where
  "globally_hyperbolic ≡ ∃S. is_cauchy_surface S"

axiomatization where
  no_closed_timelike_curves: "∀x y. x ≼ y ∧ y ≼ x ⟶ x = y"

theorem cauchy_implies_hyperbolic:
  assumes "is_cauchy_surface S"
  shows "globally_hyperbolic"
  using assms unfolding globally_hyperbolic_def by auto

end
