theory SinkhornThermodynamics
  imports Main Real
begin

text ‹
  Formalization of the Sinkhorn-Knopp algorithm as an entropy regularization process.
  We model a simplified 1D discrete optimal transport step.
›

definition entropy :: "real ⇒ real" where
  "entropy x = (if x > 0 then - x * ln x else 0)"

definition sinkhorn_step :: "real ⇒ real ⇒ real ⇒ real" where
  "sinkhorn_step u K v = u * K * v"

lemma sinkhorn_positivity:
  assumes "u > 0" "K > 0" "v > 0"
  shows "sinkhorn_step u K v > 0"
  using assms unfolding sinkhorn_step_def
  by simp

text ‹
  Thermodynamic regression: minimizing the regularized transport cost 
  is equivalent to Sinkhorn projections.
›

definition regularized_cost :: "real ⇒ real ⇒ real" where
  "regularized_cost C H = C - H"

lemma regularized_cost_bound:
  assumes "C ≥ 0" "H ≤ 0"
  shows "regularized_cost C H ≥ 0"
  using assms unfolding regularized_cost_def
  by simp

end
