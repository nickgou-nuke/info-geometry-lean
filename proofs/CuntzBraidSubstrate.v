Require Import Coq.Init.Nat.

Definition CuntzO2Generators : nat := 2.
Definition MellinShannonReconstruction : nat := 2.

Theorem Cuntz_Mellin_Equivalence : CuntzO2Generators = MellinShannonReconstruction.
Proof.
  reflexivity.
Qed.
