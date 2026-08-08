From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition is_balanced (D D_dagger : Z) := D + D_dagger = 1.

Definition InfinityState_D := 1.
Definition InfinityState_D_dagger := 0.

Lemma Infinity_is_balanced : is_balanced InfinityState_D InfinityState_D_dagger.
Proof. reflexivity. Qed.

Definition ZeroState_D := 0.
Definition ZeroState_D_dagger := 1.

Lemma Zero_is_balanced : is_balanced ZeroState_D ZeroState_D_dagger.
Proof. reflexivity. Qed.

Definition conformal_inversion_D (D D_dagger : Z) := D_dagger.
Definition conformal_inversion_D_dagger (D D_dagger : Z) := D.

Theorem inversion_preserves_balance : forall D D_dagger,
  is_balanced D D_dagger -> is_balanced (conformal_inversion_D D D_dagger) (conformal_inversion_D_dagger D D_dagger).
Proof.
  intros D D_dagger H.
  unfold is_balanced, conformal_inversion_D, conformal_inversion_D_dagger in *.
  rewrite Z.add_comm.
  exact H.
Qed.

Theorem inversion_involution_D : forall D D_dagger,
  conformal_inversion_D (conformal_inversion_D D D_dagger) (conformal_inversion_D_dagger D D_dagger) = D.
Proof.
  intros. reflexivity.
Qed.

Theorem inversion_maps_infinity_to_zero_D :
  conformal_inversion_D InfinityState_D InfinityState_D_dagger = ZeroState_D.
Proof. reflexivity. Qed.

Theorem inversion_maps_infinity_to_zero_D_dagger :
  conformal_inversion_D_dagger InfinityState_D InfinityState_D_dagger = ZeroState_D_dagger.
Proof. reflexivity. Qed.
