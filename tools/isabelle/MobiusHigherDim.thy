theory MobiusHigherDim
  imports Main
begin

definition reflect :: "'a::field \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "reflect a r x = x - (2 * a * (x * a - r)) / (a * a)"

lemma reflect_involution:
  fixes a r x :: "'a::field_char_0"
  assumes "a \<noteq> 0"
  shows "reflect a r (reflect a r x) = x"
  using assms
  unfolding reflect_def
  by (simp add: field_simps)

end
