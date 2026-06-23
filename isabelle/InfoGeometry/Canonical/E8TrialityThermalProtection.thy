theory E8TrialityThermalProtection
  imports Complex_Main
begin

(* E8 Lie algebra dimensions *)
definition dim_E8 :: nat where "dim_E8 = 248"
definition rank_E8 :: nat where "rank_E8 = 8"
definition positive_roots_E8 :: nat where "positive_roots_E8 = 120"

datatype Spin8Representation = vector | spinor_plus | spinor_minus

fun spin8_rep_dim :: "Spin8Representation \<Rightarrow> nat" where
  "spin8_rep_dim vector = 8"
| "spin8_rep_dim spinor_plus = 8"
| "spin8_rep_dim spinor_minus = 8"

fun triality_sigma :: "Spin8Representation \<Rightarrow> Spin8Representation" where
  "triality_sigma vector = spinor_plus"
| "triality_sigma spinor_plus = spinor_minus"
| "triality_sigma spinor_minus = vector"

fun triality_tau :: "Spin8Representation \<Rightarrow> Spin8Representation" where
  "triality_tau vector = vector"
| "triality_tau spinor_plus = spinor_minus"
| "triality_tau spinor_minus = spinor_plus"

lemma triality_sigma_order_3:
  shows "triality_sigma (triality_sigma (triality_sigma rep)) = rep"
  by (cases rep) auto

lemma triality_tau_order_2:
  shows "triality_tau (triality_tau rep) = rep"
  by (cases rep) auto

consts e8_liouville_grading :: "nat \<Rightarrow> int"

lemma triality_preserves_grading:
  shows "e8_liouville_grading (spin8_rep_dim rep) =
         e8_liouville_grading (spin8_rep_dim (triality_sigma rep))"
  by (cases rep) auto

end
