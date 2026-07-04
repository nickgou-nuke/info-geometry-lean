theory CFTWZW
  imports Complex_Main
begin

text \<open>Wess-Zumino-Witten affine structure limit boundaries.\<close>

definition affine_parameter_bound :: "nat \<Rightarrow> real" where
  "affine_parameter_bound k = (if k = 0 then 0 else 1 / real k)"

lemma affine_bound_limit:
  assumes "k > 0"
  shows "affine_parameter_bound k > 0"
  using assms unfolding affine_parameter_bound_def by auto

definition wzw_level :: "nat \<Rightarrow> bool" where
  "wzw_level k = (k > 0)"

theorem wzw_boundary_valid:
  assumes "wzw_level k"
  shows "affine_parameter_bound k > 0"
  using assms unfolding wzw_level_def affine_parameter_bound_def by auto

value "affine_parameter_bound 5"
value "affine_parameter_bound 0"

end
