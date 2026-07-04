theory CFTBlocks
  imports Complex_Main
begin

definition cross_ratio :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex" where
  "cross_ratio z1 z2 z3 z4 = ((z1 - z2) * (z3 - z4)) / ((z1 - z3) * (z2 - z4))"

lemma cross_ratio_translation_invariance:
  "cross_ratio (z1 + c) (z2 + c) (z3 + c) (z4 + c) = cross_ratio z1 z2 z3 z4"
  unfolding cross_ratio_def
  by simp

lemma cross_ratio_scaling_invariance:
  assumes "k \<noteq> 0"
  shows "cross_ratio (k * z1) (k * z2) (k * z3) (k * z4) = cross_ratio z1 z2 z3 z4"
  unfolding cross_ratio_def
  using assms
proof -
  have "(k * z1 - k * z2) * (k * z3 - k * z4) = k * k * (z1 - z2) * (z3 - z4)"
    by (simp add: algebra_simps)
  moreover have "(k * z1 - k * z3) * (k * z2 - k * z4) = k * k * (z1 - z3) * (z2 - z4)"
    by (simp add: algebra_simps)
  ultimately show "((k * z1 - k * z2) * (k * z3 - k * z4)) / ((k * z1 - k * z3) * (k * z2 - k * z4)) =
                   ((z1 - z2) * (z3 - z4)) / ((z1 - z3) * (z2 - z4))"
    using assms by simp
qed

end
