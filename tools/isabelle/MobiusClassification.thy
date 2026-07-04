theory MobiusClassification
  imports Main
begin

lemma trace_squared:
  fixes l :: "'a::field"
  assumes "t = l + 1 / l"
    and "l ~= 0"
  shows "t^2 = l^2 + 2 + (1 / l)^2"
proof -
  have "t^2 = (l + 1 / l)^2"
    by (simp add: assms(1))
  also have "... = l^2 + 2 * l * (1 / l) + (1 / l)^2"
    by (simp add: power2_eq_square algebra_simps)
  also have "... = l^2 + 2 + (1 / l)^2"
    using assms(2) by simp
  finally show ?thesis .
qed

end
