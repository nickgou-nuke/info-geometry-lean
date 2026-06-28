From Stdlib Require Import Reals.
Open Scope R_scope.

Definition partitionQ (r beta : R) : R := exp (beta * r) + exp (-(beta * r)).

Lemma partitionQ_cosh : forall r beta,
  partitionQ r beta = 2 * cosh (beta * r).
Proof.
  intros r beta.
  unfold partitionQ, cosh.
  unfold Rdiv.
  rewrite (Rmult_comm (exp (beta * r) + exp (- (beta * r))) (/ 2)).
  rewrite <- Rmult_assoc.
  rewrite Rinv_r.
  - ring.
  - apply Rgt_not_eq.
    apply Rlt_0_2.
Qed.
