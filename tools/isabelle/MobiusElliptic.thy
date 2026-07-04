theory MobiusElliptic
  imports Main
begin

lemma elliptic_invariant:
  fixes u v x y :: "'a::comm_ring_1"
  assumes "u^2 + v^2 = 1"
  shows "(u * x - v * y)^2 + (v * x + u * y)^2 = x^2 + y^2"
proof -
  have "(u * x - v * y)^2 + (v * x + u * y)^2 = (u^2 + v^2) * x^2 + (u^2 + v^2) * y^2"
    by (simp add: power2_eq_square algebra_simps)
  also have "... = 1 * x^2 + 1 * y^2"
    using assms by simp
  also have "... = x^2 + y^2"
    by simp
  finally show ?thesis .
qed

end
