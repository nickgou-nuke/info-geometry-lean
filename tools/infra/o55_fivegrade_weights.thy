(* O55FiveGradeWeights.thy *)
(* Isabelle/HOL formalization of the O(5,5) five-grade weight mapping *)

theory O55FiveGradeWeights
  imports Main
begin

(* Weight constants matching the Python/Sage/GAP/Coq output. *)
definition weight_u5 :: int where "weight_u5 = 1"
definition weight_v5 :: int where "weight_v5 = -1"
definition weight_u4 :: int where "weight_u4 = 1"
definition weight_v4 :: int where "weight_v4 = -1"
definition weight_D5 :: int where "weight_D5 = 0"
definition weight_D4 :: int where "weight_D4 = 0"
definition weight_D  :: int where "weight_D = 0"
definition weight_J5 :: int where "weight_J5 = 0"
definition weight_J4 :: int where "weight_J4 = 0"
definition weight_J  :: int where "weight_J = 0"

(* Trivial lemma that the constants have the expected values. *)
lemma weight_constants:
  "weight_u5 = 1 ∧ weight_v5 = -1 ∧ weight_u4 = 1 ∧ weight_v4 = -1 ∧
   weight_D5 = 0 ∧ weight_D4 = 0 ∧ weight_D = 0 ∧
   weight_J5 = 0 ∧ weight_J4 = 0 ∧ weight_J = 0"
  by (simp add: weight_u5_def weight_v5_def weight_u4_def weight_v4_def
                weight_D5_def weight_D4_def weight_D_def
                weight_J5_def weight_J4_def weight_J_def)
end