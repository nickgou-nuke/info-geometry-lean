From Stdlib Require Import ZArith Lia.

Open Scope Z_scope.

Definition tripotent (d : Z) : Prop := d * d * d = d.
Definition tripotentPolynomial (d : Z) : Z := d * d * d - d.

Lemma tripotent_roots : forall d : Z,
  tripotent d <-> d = 0 \/ d = 1 \/ d = -1.
Proof.
  intros d. unfold tripotent. nia.
Qed.

Definition su5AdjointDim : nat := 24.
Definition spinorDim : nat := 32.
Definition varlamovEven : nat := (1 + 10 + 5)%nat.
Definition varlamovOdd : nat := (5 + 10 + 1)%nat.
Definition weylA4Order : nat := 120.
Definition mobiusGroupOrder : nat := 2.
Definition wittenMoebiusIndex : Z :=
  Z.of_nat varlamovEven - Z.of_nat varlamovOdd.
Definition mobiusTwist (k : Z) : Z := -k.

Lemma varlamov_spinor_split :
  varlamovEven = 16%nat /\
  varlamovOdd = 16%nat /\
  (varlamovEven + varlamovOdd)%nat = spinorDim /\
  wittenMoebiusIndex = 0.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Lemma mobius_involutive : forall k,
  mobiusTwist (mobiusTwist k) = k.
Proof.
  intros k. unfold mobiusTwist. lia.
Qed.

Lemma tripotent_polynomial_roots :
  tripotentPolynomial (-1) = 0 /\
  tripotentPolynomial 0 = 0 /\
  tripotentPolynomial 1 = 0.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Lemma varlamov_klein_spectral_kernel :
  su5AdjointDim = 24%nat /\
  spinorDim = 32%nat /\
  weylA4Order = 120%nat /\
  mobiusGroupOrder = 2%nat /\
  varlamovEven = 16%nat /\
  varlamovOdd = 16%nat /\
  (varlamovEven + varlamovOdd)%nat = spinorDim /\
  wittenMoebiusIndex = 0 /\
  (forall k : Z, mobiusTwist (mobiusTwist k) = k) /\
  (forall d : Z, tripotent d <-> d = 0 \/ d = 1 \/ d = -1).
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split.
  - intro k. apply mobius_involutive.
  - intro z. apply tripotent_roots.
Qed.
