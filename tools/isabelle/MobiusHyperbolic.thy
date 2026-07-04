theory MobiusHyperbolic
  imports Main
begin

lemma hyperbolic_trace_relation:
  fixes L :: "'a::field_char_0"
  assumes "L ~= 0"
  shows "(L + 1 / L)^2 - 4 = (L - 1 / L)^2"
proof -
  have "(L + 1 / L)^2 - 4 = L^2 + 2 * L * (1 / L) + (1 / L)^2 - 4"
    by (simp add: power2_eq_square algebra_simps)
  also have "... = L^2 + 2 + (1 / L)^2 - 4"
    using assms by simp
  also have "... = L^2 - 2 + (1 / L)^2"
    by simp
  also have "... = L^2 - 2 * L * (1 / L) + (1 / L)^2"
    using assms by simp
  also have "... = (L - 1 / L)^2"
    by (simp add: power2_eq_square algebra_simps)
  finally show ?thesis .
qed

end
