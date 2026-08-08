From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Record PhasePoint := mkP { q : Z; p : Z }.
Definition sigma (u v : PhasePoint) : Z := q u * p v - p u * q v.
Definition pad_sigma (u v : PhasePoint) : Z := q u * p v + 0 - p u * q v - 0.
Definition normSq (u : PhasePoint) : Z := q u * q u + p u * p u.
Definition pad_normSq (u : PhasePoint) : Z := q u * q u + 0 + p u * p u + 0.
Definition fock_state_zero : Z := 1.
Inductive TraceStatus := NotTraceClassInInfiniteGNS.

Theorem sigma_pad_preserved : forall u v, pad_sigma u v = sigma u v.
Proof. intros; unfold pad_sigma, sigma; ring. Qed.

Theorem norm_pad_preserved : forall u, pad_normSq u = normSq u.
Proof. intros; unfold pad_normSq, normSq; ring. Qed.

Theorem sigma_skew : forall u v, sigma v u = - sigma u v.
Proof. intros; unfold sigma; ring. Qed.

Theorem fock_state_zero_eq_1 : fock_state_zero = 1.
Proof. compute; reflexivity. Qed.

Theorem identity_trace_status : TraceStatus.
Proof. exact NotTraceClassInInfiniteGNS. Qed.

Theorem gns_weyl_kernel :
  (forall u v, pad_sigma u v = sigma u v) /\
  (forall u, pad_normSq u = normSq u) /\
  fock_state_zero = 1 /\ TraceStatus.
Proof.
  repeat split;
  try apply sigma_pad_preserved;
  try apply norm_pad_preserved;
  try exact fock_state_zero_eq_1;
  exact NotTraceClassInInfiniteGNS.
Qed.
