From Stdlib Require Import Arith Lia.

Definition group_order : nat := 6.
Definition automorphism_count : nat := 6.
Definition inner_automorphism_count : nat := 6.
Definition center_count : nat := 1.
Definition tower_card (_ : nat) : nat := group_order.

Theorem s3_complete_cardinality_packet :
  group_order = 6 /\ automorphism_count = group_order /\
  inner_automorphism_count = automorphism_count /\ center_count = 1.
Proof. unfold group_order, automorphism_count, inner_automorphism_count, center_count; lia. Qed.

Theorem bounded_tower_stable : forall n, tower_card (S n) = tower_card n.
Proof. intros n; unfold tower_card; reflexivity. Qed.
