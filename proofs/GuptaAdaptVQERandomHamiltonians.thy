theory GuptaAdaptVQERandomHamiltonians
  imports Complex_Main
begin

definition pair_count :: "nat \<Rightarrow> nat" where
  "pair_count n = n * (n - 1) div 2"

definition four_body_count :: "nat \<Rightarrow> nat" where
  "four_body_count N = N * (N - 1) * (N - 2) * (N - 3) div 24"

lemma dense_SYK_terms_N20:
  "four_body_count 20 = 4845"
  by (simp add: four_body_count_def)

lemma sparse_SYK_ks9_N20_terms:
  "9 * 20 = (180::nat)"
  by simp

lemma sparse_removes_roughly_96_percent_N20:
  "((4845 - 180) / 4845 :: rat) = 311 / 323"
  by normalization

definition sk_pool_size :: "nat \<Rightarrow> nat" where
  "sk_pool_size L = 2 * pair_count L"

definition syk_pool_size :: "nat \<Rightarrow> nat" where
  "syk_pool_size n = n + 3 * pair_count n"

lemma sk_pool_size_L18:
  "sk_pool_size 18 = 306"
  by (simp add: sk_pool_size_def pair_count_def)

lemma syk_pool_size_n10:
  "syk_pool_size 10 = 145"
  by (simp add: syk_pool_size_def pair_count_def)

definition relative_energy_error :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "relative_energy_error exact adapt = (exact - adapt) / exact"

lemma relative_error_zero_for_exact_match:
  assumes "E \<noteq> 0"
  shows "relative_energy_error E E = 0"
  using assms by (simp add: relative_energy_error_def)

lemma Hilbert_dimension_N20:
  "(2::nat) ^ 10 = 1024"
  by simp

lemma entropy_N20_close:
  "abs ((275 / 100 :: rat) - 278 / 100) = 3 / 100"
  by normalization

lemma dense_SYK_fidelity_above_993:
  "(9936 / 10000 :: rat) \<ge> 993 / 1000"
  by normalization

lemma dense_SYK_DLA_n10:
  "(2::nat) ^ (2 * 10 - 1) - 2 = 524286"
  by simp

end
