theory MobiusGeometry
  imports Main
begin

record ('a::comm_ring_1) mobius_matrix =
  a_val :: 'a
  b_val :: 'a
  c_val :: 'a
  d_val :: 'a

definition comp_mobius :: "'a::comm_ring_1 mobius_matrix \<Rightarrow> 'a mobius_matrix \<Rightarrow> 'a mobius_matrix" where
"comp_mobius M1 M2 =
  \<lparr> a_val = a_val M1 * a_val M2 + b_val M1 * c_val M2,
    b_val = a_val M1 * b_val M2 + b_val M1 * d_val M2,
    c_val = c_val M1 * a_val M2 + d_val M1 * c_val M2,
    d_val = c_val M1 * b_val M2 + d_val M1 * d_val M2 \<rparr>"

definition id_mobius :: "'a::comm_ring_1 \<Rightarrow> 'a mobius_matrix" where
"id_mobius k = \<lparr> a_val = k, b_val = 0, c_val = 0, d_val = k \<rparr>"

definition inv_mobius :: "'a::comm_ring_1 mobius_matrix \<Rightarrow> 'a mobius_matrix" where
"inv_mobius M = \<lparr> a_val = d_val M, b_val = - b_val M, c_val = - c_val M, d_val = a_val M \<rparr>"

definition det_mobius :: "'a::comm_ring_1 mobius_matrix \<Rightarrow> 'a" where
"det_mobius M = a_val M * d_val M - b_val M * c_val M"

lemma mobius_inv_right:
  "comp_mobius M (inv_mobius M) = id_mobius (det_mobius M)"
  unfolding comp_mobius_def inv_mobius_def id_mobius_def det_mobius_def
  by (simp add: algebra_simps)

lemma mobius_inv_left:
  "comp_mobius (inv_mobius M) M = id_mobius (det_mobius M)"
  unfolding comp_mobius_def inv_mobius_def id_mobius_def det_mobius_def
  by (simp add: algebra_simps)

end
