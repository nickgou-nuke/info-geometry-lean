From Stdlib Require Import ZArith.
Open Scope Z_scope.

(* Representing chiral anomaly cancellation as a Z2 action on the integers.
   The involution property models the cancellation of the anomaly (torsion element). *)

Definition anomaly_action (g : Z) (x : Z) : Z :=
  if Z.even g then x else -x.

Theorem anomaly_cancellation_id : forall x : Z,
  anomaly_action 0 x = x.
Proof.
  intros x. unfold anomaly_action. reflexivity.
Qed.

Theorem anomaly_cancellation_involution : forall x : Z,
  anomaly_action 1 (anomaly_action 1 x) = x.
Proof.
  intros x. unfold anomaly_action. simpl. apply Z.opp_involutive.
Qed.

Theorem chiral_anomaly_cancellation : forall g1 g2 x : Z,
  (Z.even g1 = true /\ Z.even g2 = true) \/ (Z.even g1 = false /\ Z.even g2 = false) ->
  anomaly_action g1 (anomaly_action g2 x) = x.
Proof.
  intros g1 g2 x [ [H1 H2] | [H1 H2] ].
  - unfold anomaly_action. rewrite H1, H2. reflexivity.
  - unfold anomaly_action. rewrite H1, H2. apply Z.opp_involutive.
Qed.
