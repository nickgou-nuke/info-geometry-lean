theory CFTVirasoro
  imports Main
begin

definition c :: "int \<Rightarrow> int" where
  "c m = m * (m^2 - 1)"

lemma c_antisym: "c m = - c (-m)"
  unfolding c_def
  by (simp add: power2_eq_square)

end
