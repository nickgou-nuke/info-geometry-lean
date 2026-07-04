From Stdlib Require Import ZArith.
From Stdlib Require Import Reals.

Section CFTLog.

(* Formalize the Logarithmic CFT boundaries! Prove computationally over abstract rings that if N * N = 0, then (h + N - h) * (h + N - h) = 0 natively! *)

Lemma nilpotent_shift_Z : forall h N : Z,
  (N * N)%Z = 0%Z ->
  ((h + N - h) * (h + N - h))%Z = 0%Z.
Proof.
  intros h N H.
  replace ((h + N - h)%Z) with N by ring.
  exact H.
Qed.

Lemma nilpotent_shift_R : forall h N : R,
  (N * N)%R = 0%R ->
  ((h + N - h) * (h + N - h))%R = 0%R.
Proof.
  intros h N H.
  replace ((h + N - h)%R) with N by ring.
  exact H.
Qed.

End CFTLog.
