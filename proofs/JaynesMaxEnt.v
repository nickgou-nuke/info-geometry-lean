Require Import Coq.Init.Logic.

Definition StateSpace := nat.
Definition RelativeEntropy (p q : StateSpace) : nat := 0.

Definition MaxEntPrinciple : Prop :=
  forall p q, RelativeEntropy p q = 0.

Lemma max_ent_trivial : True.
Proof.
  exact I.
Qed.
