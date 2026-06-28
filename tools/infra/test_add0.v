Require Import Reals. Lemma test : forall x : R, x + 0 = x. Proof. intro x. now rewrite <- plus_0_r. Qed.
