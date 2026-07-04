theory MobiusThreePoints
  imports Main
begin

definition f1 :: "'a::field \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "f1 z1 z2 z3 z = ((z - z1) * (z2 - z3)) / ((z - z3) * (z2 - z1))"

lemma f1_z1:
  assumes "z1 \<noteq> z3" "z2 \<noteq> z1"
  shows "f1 z1 z2 z3 z1 = 0"
  unfolding f1_def by simp

lemma f1_z2:
  assumes "z1 \<noteq> z3" "z2 \<noteq> z3" "z2 \<noteq> z1"
  shows "f1 z1 z2 z3 z2 = 1"
proof -
  have "z2 - z3 \<noteq> 0" using assms(2) by simp
  have "z2 - z1 \<noteq> 0" using assms(3) by simp
  then show ?thesis
    unfolding f1_def
    using assms by auto
qed

end
