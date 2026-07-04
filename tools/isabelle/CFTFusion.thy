theory CFTFusion
  imports Complex_Main
begin

definition Q :: "real \<Rightarrow> real" where
  "Q b = b + 1 / b"

definition Delta :: "real \<Rightarrow> real \<Rightarrow> real" where
  "Delta alpha b = alpha * (Q b - alpha)"

lemma reflection_symmetry: "Delta (Q b - alpha) b = Delta alpha b"
  unfolding Delta_def
  by (simp add: algebra_simps)

end
