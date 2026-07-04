theory InverseLimit
  imports Main
begin

text \<open>An inverse system of sets over the natural numbers, indexed by type 'a.\<close>
text \<open>We model this as a sequence of sets (predicates) and transition maps.\<close>

locale inverse_system =
  fixes A :: "nat \<Rightarrow> 'a set"
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes f_maps: "\<And>n x. x \<in> A (Suc n) \<Longrightarrow> f n x \<in> A n"
begin

text \<open>The inverse limit is the set of sequences that respect the transition maps.\<close>

definition limit_set :: "(nat \<Rightarrow> 'a) set" where
  "limit_set = {x. (\<forall>n. x n \<in> A n) \<and> (\<forall>n. f n (x (Suc n)) = x n)}"

text \<open>Projection maps from the limit to the individual sets.\<close>

definition proj :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "proj n x = x n"

lemma proj_in_A:
  assumes "x \<in> limit_set"
  shows "proj n x \<in> A n"
  using assms unfolding limit_set_def proj_def by simp

lemma proj_f:
  assumes "x \<in> limit_set"
  shows "f n (proj (Suc n) x) = proj n x"
  using assms unfolding limit_set_def proj_def by simp

text \<open>Universal property of the inverse limit.\<close>

lemma universal_property:
  fixes g :: "nat \<Rightarrow> 'a"
  assumes g_in_A: "\<And>n. g n \<in> A n"
  assumes g_commutes: "\<And>n. f n (g (Suc n)) = g n"
  shows "\<exists>! x. x \<in> limit_set \<and> (\<forall>n. proj n x = g n)"
proof (rule ex1I)
  show "g \<in> limit_set \<and> (\<forall>n. proj n g = g n)"
    using g_in_A g_commutes unfolding limit_set_def proj_def by auto
next
  fix x
  assume "x \<in> limit_set \<and> (\<forall>n. proj n x = g n)"
  thus "x = g"
    unfolding proj_def by auto
qed

end

end
