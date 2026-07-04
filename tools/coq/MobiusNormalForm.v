From Stdlib Require Import Reals.
Open Scope R_scope.

Definition a (beta gamma : R) : R := 1 + gamma * beta.
Definition b (beta gamma : R) : R := - beta * (gamma * gamma).
Definition c (beta gamma : R) : R := beta.
Definition d (beta gamma : R) : R := 1 - gamma * beta.

Definition det (beta gamma : R) : R :=
  (a beta gamma) * (d beta gamma) - (b beta gamma) * (c beta gamma).

Lemma det_Mobius_Normal_Form : forall beta gamma : R, det beta gamma = 1.
Proof.
  intros beta gamma.
  unfold det, a, b, c, d.
  ring.
Qed.
