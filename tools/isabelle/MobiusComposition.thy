theory MobiusComposition
  imports Main
begin

definition f1 :: "'a::field \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"f1 c d z = z + d / c"

definition f2 :: "'a::field \<Rightarrow> 'a" where
"f2 z = 1 / z"

definition f3 :: "'a::field \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"f3 a b c d z = (b * c - a * d) / (c * c) * z"

definition f4 :: "'a::field \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"f4 a c z = z + a / c"

lemma mobius_decomposition:
  fixes a b c d z :: "'a::field"
  assumes "c \<noteq> 0" and "z + d / c \<noteq> 0"
  shows "f4 a c (f3 a b c d (f2 (f1 c d z))) = (a * z + b) / (c * z + d)"
proof -
  have nz1: "c * z + d \<noteq> 0"
  proof -
    have "z * c + d = (z + d / c) * c"
      using assms(1) by (simp add: field_simps)
    also have "... \<noteq> 0"
      using assms by simp
    finally show ?thesis by (simp add: field_simps)
  qed
  have nz2: "c * c \<noteq> 0" using assms(1) by simp
  show ?thesis
    unfolding f4_def f3_def f2_def f1_def
    using assms nz1 nz2
    by (simp add: divide_simps, algebra)
qed

end
