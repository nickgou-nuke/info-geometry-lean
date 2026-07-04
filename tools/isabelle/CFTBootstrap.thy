theory CFTBootstrap
  imports Complex_Main
begin

definition S_map :: "real \<Rightarrow> real" where
  "S_map \<tau> = - 1 / \<tau>"

lemma S_involution:
  fixes \<tau> :: real
  assumes "\<tau> \<noteq> 0"
  shows "S_map (S_map \<tau>) = \<tau>"
proof -
  have "S_map (S_map \<tau>) = - 1 / (- 1 / \<tau>)"
    by (simp add: S_map_def)
  also have "... = \<tau>"
    using assms by simp
  finally show ?thesis .
qed

end
