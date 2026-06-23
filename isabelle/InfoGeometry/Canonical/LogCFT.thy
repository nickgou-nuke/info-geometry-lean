theory LogCFT
  imports Complex_Main
begin

locale log_cft =
  fixes N :: "'a"
    and I :: "'a"
    and zero :: "'a"
    and mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)
    and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 65)
    and smul :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes N_nilpotent: "N * N = zero"
begin

theorem JordanN_sq_zero: "N * N = zero"
  by (rule N_nilpotent)

end

theorem fibonacci_scale_reduction:
  fixes phi :: real
  assumes phi_def: "phi^2 = phi + 1"
  shows "20 * phi^4 = 60 * phi + 40"
proof -
  have "phi^4 = (phi^2)^2" by (simp add: power2_eq_square [symmetric] power_mult [symmetric])
  also have "... = (phi + 1)^2" by (simp add: phi_def)
  also have "... = phi^2 + 2 * phi + 1" by (simp add: power2_eq_square algebra_simps)
  also have "... = (phi + 1) + 2 * phi + 1" by (simp add: phi_def)
  also have "... = 3 * phi + 2" by simp
  finally have "phi^4 = 3 * phi + 2" .
  then show ?thesis by simp
qed

theorem combinatorial_backbone:
  "(3::real) + 7 + 127 = 137"
  by simp

end
