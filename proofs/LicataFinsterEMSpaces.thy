theory LicataFinsterEMSpaces
  imports Complex_Main
begin

record 'g EMObject =
  pi_is_diagonal :: "nat \<Rightarrow> bool"
  pi_order :: "nat \<Rightarrow> nat"
  group_order :: nat
  diagonal_degree :: nat

definition EM_valid :: "'g EMObject \<Rightarrow> bool" where
  "EM_valid K \<longleftrightarrow>
    pi_order K (diagonal_degree K) = group_order K \<and>
    (\<forall>k. k \<noteq> diagonal_degree K \<longrightarrow> pi_order K k = 1)"

definition canonical_EM :: "nat \<Rightarrow> nat \<Rightarrow> unit EMObject" where
  "canonical_EM g n =
    \<lparr> pi_is_diagonal = (\<lambda>k. k = n),
      pi_order = (\<lambda>k. if k = n then g else 1),
      group_order = g,
      diagonal_degree = n \<rparr>"

lemma canonical_EM_valid:
  "EM_valid (canonical_EM g n)"
  by (simp add: EM_valid_def canonical_EM_def)

lemma canonical_EM_diagonal:
  "pi_order (canonical_EM g n) n = g"
  by (simp add: canonical_EM_def)

lemma canonical_EM_off_diagonal:
  "k \<noteq> n \<Longrightarrow> pi_order (canonical_EM g n) k = 1"
  by (simp add: canonical_EM_def)

definition product_EM_pi_order :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "product_EM_pi_order g h k =
    (if k = 1 then g else 1) * (if k = 2 then h else 1)"

lemma product_EM_pi1:
  "product_EM_pi_order g h 1 = g"
  by (simp add: product_EM_pi_order_def)

lemma product_EM_pi2:
  "product_EM_pi_order g h 2 = h"
  by (simp add: product_EM_pi_order_def)

lemma product_EM_pi_other:
  "k \<noteq> 1 \<Longrightarrow> k \<noteq> 2 \<Longrightarrow> product_EM_pi_order g h k = 1"
  by (simp add: product_EM_pi_order_def)

definition reduced_sphere_cohomology_rank :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "reduced_sphere_cohomology_rank k n = (if k = n then 1 else 0)"

lemma sphere_cohomology_diagonal:
  "reduced_sphere_cohomology_rank n n = 1"
  by (simp add: reduced_sphere_cohomology_rank_def)

lemma sphere_cohomology_off_diagonal:
  "k \<noteq> n \<Longrightarrow> reduced_sphere_cohomology_rank k n = 0"
  by (simp add: reduced_sphere_cohomology_rank_def)

definition suspension_shift_index :: "nat \<Rightarrow> nat" where
  "suspension_shift_index k = k + 1"

lemma suspension_shift_1_to_2:
  "suspension_shift_index 1 = 2"
  by (simp add: suspension_shift_index_def)

lemma suspension_shift_2_to_3:
  "suspension_shift_index 2 = 3"
  by (simp add: suspension_shift_index_def)

definition freudenthal_stable :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "freudenthal_stable n k \<longleftrightarrow> k \<le> 2 * n - 2"

lemma freudenthal_examples:
  "freudenthal_stable 2 2 \<and> freudenthal_stable 3 4 \<and> \<not> freudenthal_stable 2 3"
  by (simp add: freudenthal_stable_def)

end
