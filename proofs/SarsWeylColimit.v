From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Record PhasePoint := mkP { q : Z; p : Z }.
Definition sigma (u v : PhasePoint) : Z := q u * p v - p u * q v.
Definition pad1to2_sigma (u v : PhasePoint) : Z := q u * p v + 0 - p u * q v - 0.
Definition block_dim (n : nat) : Z := 32 ^ (Z.of_nat n).
Definition cl55_dim : Z := 2 ^ 10.

Theorem sigma_pad_preserved : forall u v, pad1to2_sigma u v = sigma u v.
Proof. intros; unfold pad1to2_sigma, sigma; ring. Qed.

Theorem sigma_skew : forall u v, sigma v u = - sigma u v.
Proof. intros; unfold sigma; ring. Qed.

Theorem block_dim_0 : block_dim 0 = 1.
Proof. compute; reflexivity. Qed.

Theorem block_dim_1 : block_dim 1 = 32.
Proof. compute; reflexivity. Qed.

Theorem block_dim_2 : block_dim 2 = 1024.
Proof. compute; reflexivity. Qed.

Theorem cl55_dim_block2 : cl55_dim = block_dim 2.
Proof. compute; reflexivity. Qed.

Inductive parity := Even | Odd.
Definition super_target (a b : parity) : parity :=
  match a, b with
  | Odd, Odd => Even
  | Even, Even => Even
  | _, _ => Odd
  end.

Theorem odd_odd_even : super_target Odd Odd = Even.
Proof. compute; reflexivity. Qed.

Theorem weyl_colimit_kernel :
  (forall u v, pad1to2_sigma u v = sigma u v) /\
  block_dim 0 = 1 /\ block_dim 1 = 32 /\ block_dim 2 = 1024 /\
  cl55_dim = block_dim 2 /\ super_target Odd Odd = Even.
Proof.
  repeat split;
  try apply sigma_pad_preserved;
  try exact block_dim_0;
  try exact block_dim_1;
  try exact block_dim_2;
  try exact cl55_dim_block2;
  try exact odd_odd_even.
Qed.
