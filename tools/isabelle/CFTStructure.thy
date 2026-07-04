theory CFTStructure
  imports Main Complex_Main
begin

definition half_integer :: "real \<Rightarrow> bool" where
  "half_integer S \<longleftrightarrow> (\<exists>n::int. S = real_of_int n / 2)"

lemma half_integer_add:
  assumes "half_integer S1" and "half_integer S2"
  shows "half_integer (S1 + S2)"
proof -
  from assms(1) obtain n1 :: int where h1: "S1 = real_of_int n1 / 2"
    unfolding half_integer_def by auto
  from assms(2) obtain n2 :: int where h2: "S2 = real_of_int n2 / 2"
    unfolding half_integer_def by auto
  show ?thesis
    unfolding half_integer_def
    apply (rule exI[where x="n1 + n2"])
    using h1 h2 by (simp add: add_divide_distrib)
qed

end
