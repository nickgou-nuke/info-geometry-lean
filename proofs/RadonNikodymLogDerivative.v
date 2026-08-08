Require Import Reals.
Open Scope R_scope.

Parameter measure : Type.
Parameter radon_nikodym : measure -> measure -> R.
Parameter log_rn : measure -> measure -> R.

Axiom log_rn_def : forall m1 m2, log_rn m1 m2 = - ln (radon_nikodym m1 m2).
Axiom rn_chain_rule : forall m1 m2 m3, radon_nikodym m1 m3 = radon_nikodym m1 m2 * radon_nikodym m2 m3.
Axiom ln_mult : forall x y, ln (x * y) = ln x + ln y.

Lemma neg_log_rn_additivity : forall m1 m2 m3,
  log_rn m1 m3 = log_rn m1 m2 + log_rn m2 m3.
Proof.
  intros.
  rewrite log_rn_def.
  rewrite (rn_chain_rule m1 m2 m3).
  rewrite ln_mult.
  rewrite log_rn_def.
  rewrite log_rn_def.
  ring.
Qed.
