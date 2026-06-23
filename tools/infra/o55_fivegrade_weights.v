(* O55FiveGradeWeights.v *)
(* Coq formalization of the O(5,5) five-grade weight mapping. *)

Require Import ZArith.
Open Scope Z_scope.

(* Weight constants matching the Python/Sage/GAP output. *)
Definition weight_u5 : Z := 1.
Definition weight_v5 : Z := -1.
Definition weight_u4 : Z := 1.
Definition weight_v4 : Z := -1.
Definition weight_D5 : Z := 0.
Definition weight_D4 : Z := 0.
Definition weight_D  : Z := 0.
Definition weight_J5 : Z := 0.
Definition weight_J4 : Z := 0.
Definition weight_J  : Z := 0.

(* Trivial theorem that the constants have the expected values. *)
Theorem weight_constants :
  weight_u5 = 1 /\ weight_v5 = -1 /\ weight_u4 = 1 /\ weight_v4 = -1 /\
  weight_D5 = 0 /\ weight_D4 = 0 /\ weight_D = 0 /\
  weight_J5 = 0 /\ weight_J4 = 0 /\ weight_J = 0.
Proof.
  split; [split; [split; [split; [split; [split; [split; [split; [reflexivity; reflexivity]; reflexivity]; reflexivity]; reflexivity]; reflexivity]; reflexivity]; reflexivity]; reflexivity]; reflexivity]; reflexivity].
Qed.