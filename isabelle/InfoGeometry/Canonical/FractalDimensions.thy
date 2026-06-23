theory FractalDimensions
  imports Complex_Main
begin

theorem UpperPhi_fifth_minus_LowerPhi_fifth:
  fixes UpperPhi LowerPhi :: real
  assumes UpperPhi_eq_one_add_LowerPhi: "UpperPhi = 1 + LowerPhi"
    and UpperPhi_mul_LowerPhi: "UpperPhi * LowerPhi = 1"
  shows "UpperPhi^5 - LowerPhi^5 = 11"
proof -
  have H_factor: "UpperPhi^5 - LowerPhi^5 =
    (UpperPhi - LowerPhi)^5 +
    5 * (UpperPhi * LowerPhi) * (UpperPhi - LowerPhi)^3 +
    5 * (UpperPhi * LowerPhi)^2 * (UpperPhi - LowerPhi)"
    by algebra
  have H_sub: "UpperPhi - LowerPhi = 1"
    using assms by simp
  then show ?thesis
    using H_factor assms by simp
qed

theorem D_scaling:
  fixes UpperPhi :: real
  fixes D :: "int \<Rightarrow> real"
  assumes UpperPhi_pos: "UpperPhi > 0"
    and D_def: "\<And>n. D n = 10 * UpperPhi powr (real_of_int n - 6)"
  shows "D (n + 1) = UpperPhi * D n"
proof -
  have "D (n + 1) = 10 * UpperPhi powr (real_of_int (n + 1) - 6)"
    by (simp add: D_def)
  also have "... = 10 * UpperPhi powr ((real_of_int n - 6) + 1)"
    by simp
  also have "... = 10 * (UpperPhi powr (real_of_int n - 6) * UpperPhi powr 1)"
    by (simp only: powr_add)
  also have "... = 10 * (UpperPhi powr (real_of_int n - 6) * UpperPhi)"
    using UpperPhi_pos by simp
  also have "... = UpperPhi * (10 * UpperPhi powr (real_of_int n - 6))"
    by (simp add: algebra_simps)
  also have "... = UpperPhi * D n"
    by (simp add: D_def)
  finally show ?thesis .
qed

theorem E8_E8_dim_eq_double:
  fixes D_E8 D_E8E8 :: nat
  assumes D_E8_def: "D_E8 = 248"
    and D_E8E8_def: "D_E8E8 = 496"
  shows "D_E8E8 = 2 * D_E8"
  using assms by simp

end
