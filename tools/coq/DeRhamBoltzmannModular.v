From Stdlib Require Import Reals.
Open Scope R_scope.

Section DeRhamBoltzmannModular.

Definition partitionQ (r beta : R) : R := exp (beta * r) + exp (-(beta * r)).
Definition entropyPotential (r beta : R) : R := ln (partitionQ r beta).
Definition betaResponse (r beta : R) : R := r * (exp (beta * r) - exp (-(beta * r))) / partitionQ r beta.

Lemma partitionQ_pos : forall r beta, 0 < partitionQ r beta.
Proof.
  intros r beta.
  unfold partitionQ.
  apply Rplus_lt_0_compat.
  - apply exp_pos.
  - apply exp_pos.
Qed.

Lemma entropyPotential_well_defined : forall r beta,
  entropyPotential r beta = ln (exp (beta * r) + exp (-(beta * r))).
Proof.
  intros; reflexivity.
Qed.

Lemma betaResponse_def_lemma : forall r beta,
  betaResponse r beta = r * (exp (beta * r) - exp (-(beta * r))) / partitionQ r beta.
Proof.
  intros; reflexivity.
Qed.

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

End DeRhamBoltzmannModular.