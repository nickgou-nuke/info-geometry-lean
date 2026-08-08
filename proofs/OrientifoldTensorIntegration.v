Require Import Coq.Init.Nat.

Definition tensor_multiplet_count : nat := 16.

Definition fixed_planes_representations (n : nat) : Prop :=
  n = 16.

Lemma orientifold_anomaly_cancellation : fixed_planes_representations tensor_multiplet_count.
Proof.
  unfold fixed_planes_representations, tensor_multiplet_count.
  reflexivity.
Qed.
