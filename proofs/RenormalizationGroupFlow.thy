theory RenormalizationGroupFlow
  imports Main
begin

text \<open>
  Continuous topological limits of the RG flow maintaining unitary constraints.
  We abstract the flow to a sequence of real norms and prove that the limit 
  preserves the unitary constraint.
\<close>

definition unitary_constraint :: "real \<Rightarrow> bool" where
  "unitary_constraint norm_val \<longleftrightarrow> norm_val = 1"

definition topological_limit :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "topological_limit flow limit_state \<longleftrightarrow> (\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<bar>flow n - limit_state\<bar> < e)"

lemma unitary_limit:
  assumes "\<forall>n. unitary_constraint (flow n)"
  assumes "topological_limit flow limit_state"
  shows "unitary_constraint limit_state"
  using assms unfolding unitary_constraint_def topological_limit_def
  by (metis abs_zero less_numeral_extra(3) zero_less_one)

end
