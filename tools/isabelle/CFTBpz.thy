theory CFTBpz
  imports Main Complex_Main
begin

lemma liouville_central_charge:
  fixes b :: real
  assumes "b \<noteq> 0"
  shows "1 + 6 * (b + 1/b)^2 = 13 + 6 * b^2 + 6 / b^2"
  using assms by (simp add: power2_eq_square algebra_simps)

end
