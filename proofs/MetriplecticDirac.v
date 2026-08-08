Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition maximal_isotropy (D D_dagger I : R) : Prop :=
  D - I/2 = -(D_dagger - I/2).

Theorem metriplectic_dirac_equivalence :
  forall D D_dagger I : R,
  maximal_isotropy D D_dagger I <-> D + D_dagger = I.
Proof.
  intros D D_dagger I.
  unfold maximal_isotropy.
  split; intros H.
  - lra.
  - lra.
Qed.
