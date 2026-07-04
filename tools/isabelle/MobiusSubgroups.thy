theory MobiusSubgroups
  imports Complex_Main
begin

lemma psu2_det_one:
  fixes u v :: real
  assumes "u^2 + v^2 = 1"
  shows "u * u - (-v) * v = 1"
  using assms by (simp add: power2_eq_square)

end
