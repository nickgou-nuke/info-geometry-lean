From Stdlib Require Import Reals.
From Stdlib Require Import Field.
From Stdlib Require Import Lra.
Open Scope R_scope.

Record Point := mkPoint { x : R; y : R }.

Definition norm_sqr (p : Point) : R :=
  x p * x p + y p * y p.

Definition invert (r : R) (p : Point) : Point :=
  let nsq := norm_sqr p in
  mkPoint (x p * r * r / nsq) (y p * r * r / nsq).

Ltac solve_r_zero Hr :=
  match goal with
  | H : ?a * ?b = 0 |- _ =>
      apply Rmult_integral in H; destruct H as [H | H]; solve_r_zero Hr
  | H : ?a = 0 |- _ => apply Hr; exact H
  end.

Lemma helper1 : forall px py r,
  r <> 0 -> px * px + py * py <> 0 ->
  px * r * r * (px * r * r) + py * r * r * (py * r * r) <> 0.
Proof.
  intros px py r Hr Hp H.
  assert (H1: px * r * r * (px * r * r) + py * r * r * (py * r * r) = (px * px + py * py) * (r * r * r * r)) by ring.
  rewrite H1 in H.
  apply Rmult_integral in H.
  destruct H as [H | H].
  - apply Hp; exact H.
  - solve_r_zero Hr.
Qed.

Lemma invert_involution :
  forall r p, r <> 0 -> norm_sqr p <> 0 -> invert r (invert r p) = p.
Proof.
  intros r p Hr Hp.
  unfold invert, norm_sqr in *.
  destruct p as [px py]. simpl in *.
  f_equal.
  - field.
    split.
    + exact Hp.
    + apply helper1; assumption.
  - field.
    split.
    + exact Hp.
    + apply helper1; assumption.
Qed.

Lemma invert_fixes_circle :
  forall r p, r <> 0 -> norm_sqr p = r * r -> invert r p = p.
Proof.
  intros r p Hr Hcirc.
  unfold invert, norm_sqr in *.
  destruct p as [px py]. simpl in *.
  rewrite Hcirc.
  f_equal.
  - field. intro H; solve_r_zero Hr.
  - field. intro H; solve_r_zero Hr.
Qed.
