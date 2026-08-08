(* BipartiteMatchings.v *)
Require Import Coq.Init.Nat.

Inductive PerfectMatching2x2 : Type :=
  | Match1 : PerfectMatching2x2
  | Match2 : PerfectMatching2x2.

Definition eval_matching (m : PerfectMatching2x2) : nat * nat * nat * nat :=
  match m with
  | Match1 => (1, 0, 0, 1)
  | Match2 => (0, 1, 1, 0)
  end.

Definition is_doubly_stochastic_nat (M : nat * nat * nat * nat) : Prop :=
  match M with
  | (a, b, c, d) => a + b = 1 /\ c + d = 1 /\ a + c = 1 /\ b + d = 1
  end.

Theorem matching_is_stochastic : forall m : PerfectMatching2x2,
  is_doubly_stochastic_nat (eval_matching m).
Proof.
  intros.
  destruct m.
  - unfold eval_matching, is_doubly_stochastic_nat. repeat split; auto.
  - unfold eval_matching, is_doubly_stochastic_nat. repeat split; auto.
Qed.

Theorem stochastic_is_matching : forall M : nat * nat * nat * nat,
  is_doubly_stochastic_nat M -> exists m : PerfectMatching2x2, eval_matching m = M.
Proof.
  intros M H.
  destruct M as (((a, b), c), d).
  unfold is_doubly_stochastic_nat in H.
  destruct H as [H1 [H2 [H3 H4]]].
  destruct a; destruct b; destruct c; destruct d.
  - exists Match2. reflexivity.
  - exists Match1. reflexivity.
  - exists Match2. reflexivity.
  - exists Match1. reflexivity.
  - exists Match2. reflexivity.
  - exists Match1. reflexivity.
  - exists Match2. reflexivity.
  - exists Match1. reflexivity.
  - exists Match2. reflexivity.
  - exists Match1. reflexivity.
  - exists Match2. reflexivity.
  - exists Match1. reflexivity.
  - exists Match2. reflexivity.
  - exists Match1. reflexivity.
  - exists Match2. reflexivity.
  - exists Match1. reflexivity.
Qed.
