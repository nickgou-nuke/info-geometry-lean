theory MobiusEquivalence
  imports Main
begin

lemma mobius_equivalence:
  fixes a b c d L z :: "'a::field"
  assumes "L \<noteq> 0"
  assumes "c * z + d \<noteq> 0"
  shows "(L * a * z + L * b) / (L * c * z + L * d) = (a * z + b) / (c * z + d)"
proof -
  have "(L * a * z + L * b) / (L * c * z + L * d) = (L * (a * z + b)) / (L * (c * z + d))"
    by (simp add: algebra_simps)
  also have "\<dots> = (a * z + b) / (c * z + d)"
    using assms by simp
  finally show ?thesis .
qed

end
