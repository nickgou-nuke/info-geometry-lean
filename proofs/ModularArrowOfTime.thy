theory ModularArrowOfTime
  imports Main Complex_Main
begin

text ‹
  Formalization of the strict positivity of the entropy production operator
  in the context of the Modular Arrow of Time.
›

class modular_flow = preorder +
  fixes entropy_op :: "'a ⇒ real"

definition entropy_production_strictly_positive :: "('a::modular_flow) ⇒ ('a::modular_flow) ⇒ bool" where
  "entropy_production_strictly_positive x y ⟷ (x ≤ y ∧ entropy_op x < entropy_op y)"

lemma future_entropy_increase:
  assumes "entropy_production_strictly_positive x y"
  shows "entropy_op x < entropy_op y"
  using assms by (simp add: entropy_production_strictly_positive_def)

end
