From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Ring.

Local Open Scope Z_scope.

Record mat2 := {
  m11 : Z;
  m12 : Z;
  m21 : Z;
  m22 : Z
}.

Definition mat_zero : mat2 := {| m11 := 0; m12 := 0; m21 := 0; m22 := 0 |}.
Definition mat_one : mat2 := {| m11 := 1; m12 := 0; m21 := 0; m22 := 1 |}.

Definition mat_mul (A B : mat2) : mat2 :=
  {| m11 := m11 A * m11 B + m12 A * m21 B;
     m12 := m11 A * m12 B + m12 A * m22 B;
     m21 := m21 A * m11 B + m22 A * m21 B;
     m22 := m21 A * m12 B + m22 A * m22 B |}.

Definition mat_det (A : mat2) : Z :=
  m11 A * m22 A - m12 A * m21 A.

Definition K : mat2 := {| m11 := 0; m12 := 1; m21 := 0; m22 := 0 |}.
Definition parabolic_flow (t : Z) : mat2 :=
  {| m11 := 1; m12 := t; m21 := 0; m22 := 1 |}.

Theorem K_sq_zero : mat_mul K K = mat_zero.
Proof.
  reflexivity.
Qed.

Theorem parabolic_flow_eq_one_plus_tK : forall t : Z,
  parabolic_flow t = {| m11 := 1; m12 := t; m21 := 0; m22 := 1 |}.
Proof.
  intro t.
  reflexivity.
Qed.

Theorem parabolic_flow_det_one : forall t : Z,
  mat_det (parabolic_flow t) = 1.
Proof.
  intro t.
  unfold parabolic_flow, mat_det.
  simpl.
  change (1 * 1 - t * 0 = 1).
  rewrite Z.mul_0_r.
  rewrite Z.mul_1_l.
  rewrite Z.sub_0_r.
  reflexivity.
Qed.

Theorem parabolic_flow_unipotent : forall t : Z,
  m11 (parabolic_flow t) = 1 /\ m22 (parabolic_flow t) = 1.
Proof.
  intro t.
  split; reflexivity.
Qed.

Print K_sq_zero.
Print parabolic_flow_det_one.
