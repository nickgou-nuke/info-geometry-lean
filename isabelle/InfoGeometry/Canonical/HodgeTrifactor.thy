theory HodgeTrifactor
  imports Complex_Main
begin

locale hodge_trifactor =
  fixes mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)
    and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 65)
    and sub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "-" 65)
    and smul :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
    and zero :: 'a
    and one :: 'a
    and T :: 'a
  assumes T_cubic: "T * T * T = T"
begin

end

theorem bosonic_times_harmonic_eq_one:
  fixes x :: real
  assumes "x \<noteq> 1"
  shows "(1 / (1 - x)) * (1 - x) = 1"
  using assms by simp

theorem fermionic_times_harmonic_eq_one_sub_sq:
  fixes x :: real
  shows "(1 + x) * (1 - x) = 1 - x^2"
proof -
  have "(1 + x) * (1 - x) = 1 - x * x" by (simp add: algebra_simps)
  also have "... = 1 - x^2" by (simp add: power2_eq_square)
  finally show ?thesis .
qed

end
