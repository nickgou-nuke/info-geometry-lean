theory MobiusIteration
  imports Main
begin

lemma mobius_trace_sq:
  fixes L Linv :: "'a::comm_ring_1"
  assumes "L * Linv = 1"
  shows "(L + Linv)^2 - 2 = L^2 + Linv^2"
proof -
  have "(L + Linv)^2 = L^2 + L * Linv + Linv * L + Linv^2"
    by (simp add: power2_eq_square algebra_simps)
  also have "... = L^2 + 1 + 1 + Linv^2"
    using assms mult.commute[of Linv L] by simp
  also have "... = L^2 + 2 + Linv^2"
    by simp
  finally show ?thesis
    by simp
qed

end
