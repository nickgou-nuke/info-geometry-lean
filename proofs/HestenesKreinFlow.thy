theory HestenesKreinFlow
  imports Main
begin

text \<open>Hestenes spacetime algebra mapping of the metric-symplectic split.\<close>

definition jordan_product :: "real \<Rightarrow> real \<Rightarrow> real" where
  "jordan_product a b = a * b + b * a"

definition lie_bracket :: "real \<Rightarrow> real \<Rightarrow> real" where
  "lie_bracket a b = a * b - b * a"

definition metriplectic_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "metriplectic_flow f H S = lie_bracket f H + jordan_product f S"

lemma metric_symplectic_split:
  "a * b + a * b = jordan_product a b + lie_bracket a b"
  by (simp add: jordan_product_def lie_bracket_def)

end
