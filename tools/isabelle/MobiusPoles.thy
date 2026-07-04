theory MobiusPoles
  imports Main
begin

definition z_inf :: "'a::field \<Rightarrow> 'a \<Rightarrow> 'a" where
  "z_inf c d = - d / c"

definition Z_inf :: "'a::field \<Rightarrow> 'a \<Rightarrow> 'a" where
  "Z_inf a c = a / c"

lemma mobius_poles_sum:
  fixes a c d \<gamma>1 \<gamma>2 :: "'a::field"
  assumes "c \<noteq> 0"
      and "\<gamma>1 + \<gamma>2 = (a - d) / c"
  shows "\<gamma>1 + \<gamma>2 = z_inf c d + Z_inf a c"
proof -
  have "z_inf c d + Z_inf a c = - d / c + a / c"
    by (simp add: z_inf_def Z_inf_def)
  also have "\<dots> = (a - d) / c"
    using assms(1) by (simp add: field_simps)
  also have "\<dots> = \<gamma>1 + \<gamma>2"
    using assms(2) by simp
  finally show ?thesis by simp
qed

end
