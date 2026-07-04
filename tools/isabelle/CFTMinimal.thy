theory CFTMinimal
imports Complex_Main
begin

definition c_pq :: "real \<Rightarrow> real \<Rightarrow> real" where
  "c_pq p q = 1 - 6 * (p - q)^2 / (p * q)"

lemma ising_bound: "c_pq 4 3 = 1 / 2"
  unfolding c_pq_def
  by simp

end
