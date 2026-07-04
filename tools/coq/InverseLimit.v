From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Logic.FunctionalExtensionality.

Section InverseSystem.

  (* The sequence of types *)
  Variable A : nat -> Type.

  (* The transition maps: A_{n+1} -> A_n *)
  Variable f : forall n, A (S n) -> A n.

  (* A point in the product of all A_n *)
  Definition Product := forall n, A n.

  (* The condition to be in the inverse limit:
     x_n = f(x_{n+1}) *)
  Definition is_limit (x : Product) : Prop :=
    forall n, x n = f n (x (S n)).

  (* The inverse limit type *)
  Record InvLimit := mkInvLimit {
    seq : Product;
    cond : is_limit seq
  }.

  (* Projection maps from the limit to each component *)
  Definition proj (n : nat) (x : InvLimit) : A n :=
    seq x n.

  (* A basic property: proj n (x) = f (proj (S n) x) *)
  Lemma proj_commutes : forall (n : nat) (x : InvLimit),
    proj n x = f n (proj (S n) x).
  Proof.
    intros n x.
    unfold proj.
    destruct x as [s H].
    simpl.
    apply H.
  Qed.

  (* Universal property *)
  (* Let X be another type with maps g_n : X -> A_n such that g_n = f_n o g_{n+1}.
     Then there exists a unique map u : X -> InvLimit such that proj_n o u = g_n. *)
  Section UniversalProperty.
    Variable X : Type.
    Variable g : forall n, X -> A n.
    Hypothesis g_commutes : forall n (x : X), g n x = f n (g (S n) x).

    Definition u_seq (x : X) : Product := fun n => g n x.

    Lemma u_cond : forall x, is_limit (u_seq x).
    Proof.
      intro x. unfold is_limit. intro n. unfold u_seq.
      apply g_commutes.
    Qed.

    Definition u (x : X) : InvLimit := mkInvLimit (u_seq x) (u_cond x).

    Lemma u_factors : forall n (x : X), proj n (u x) = g n x.
    Proof.
      intros n x. reflexivity.
    Qed.

  End UniversalProperty.

End InverseSystem.
