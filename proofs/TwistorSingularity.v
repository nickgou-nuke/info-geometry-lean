Require Import Coq.Init.Logic.

Definition TwistorSpinor : Type := nat.
Definition SingularityPoint : Type := nat.
Definition p_infty : SingularityPoint := 0.

Theorem conformal_completion : forall (p : SingularityPoint), p = p_infty -> p = 0.
Proof.
  intros p H. exact H.
Qed.
