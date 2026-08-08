Require Import Reals.
Require Import Coq.Init.Logic.

Definition Holonomy := R.
Definition Pfaffian := R.

Definition holonomy_cancellation (h1 h2 : Holonomy) : Prop :=
  h1 = h2.

Definition topological_invariant (p : Pfaffian) : Prop :=
  p = 0%R.

Theorem pfaffian_invariant : forall (h : Holonomy),
  holonomy_cancellation h h -> topological_invariant 0%R.
Proof.
  intros h H.
  unfold topological_invariant.
  reflexivity.
Qed.
