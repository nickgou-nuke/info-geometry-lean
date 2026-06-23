theory FibonacciPartition
  imports Complex_Main
begin

theorem Fibonacci_scale_decomp:
  fixes UpperPhi :: real and LowerPhi :: real
  assumes UpperPhi_eq_one_add_LowerPhi: "UpperPhi = 1 + LowerPhi"
      and UpperPhi_sq: "UpperPhi^2 = UpperPhi + 1"
  shows "20 * UpperPhi^4 = 100 + 60 * LowerPhi"
proof -
  have "UpperPhi^4 = (UpperPhi^2)^2" by (simp add: power2_eq_square [symmetric] power_mult [symmetric])
  also have "... = (UpperPhi + 1)^2" by (simp add: UpperPhi_sq)
  also have "... = UpperPhi^2 + 2 * UpperPhi + 1" by (simp add: power2_eq_square algebra_simps)
  also have "... = (UpperPhi + 1) + 2 * UpperPhi + 1" by (simp add: UpperPhi_sq)
  also have "... = 3 * UpperPhi + 2" by simp
  finally have "UpperPhi^4 = 3 * UpperPhi + 2" .
  then have "20 * UpperPhi^4 = 60 * UpperPhi + 40" by simp
  also have "... = 60 * (1 + LowerPhi) + 40" by (simp add: UpperPhi_eq_one_add_LowerPhi)
  also have "... = 100 + 60 * LowerPhi" by simp
  finally show ?thesis .
qed

theorem bosonic_minus_fermionic_eq_sq_mul_bosonic:
  fixes x :: real
  assumes "x \<noteq> 1"
  shows "(1 / (1 - x)) - (1 + x) = x^2 * (1 / (1 - x))"
  using assms by (simp add: divide_simps power2_eq_square algebra_simps)

end
