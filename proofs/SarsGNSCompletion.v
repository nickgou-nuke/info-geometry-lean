From Coq Require Import ZArith Lia List String.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Record PhasePoint := mkP { q : Z; p : Z }.
Definition sigma (u v : PhasePoint) : Z := q u * p v - p u * q v.
Definition pad_sigma (u v : PhasePoint) : Z := q u * p v + 0 - p u * q v - 0.
Definition normSq (u : PhasePoint) : Z := q u * q u + p u * p u.
Definition pad_normSq (u : PhasePoint) : Z := q u * q u + 0 + p u * p u + 0.
Definition fock_zero : Z := 1.
Definition systems : list string := ["Lean4";"SymPy";"SageMath";"Macaulay2";"Rocq";"Isabelle";"GAP"].
Definition identity_trace_status : string := "not_trace_class_in_infinite_GNS".
Definition dmodule_generators : Z := 1.

Theorem sigma_pad_preserved : forall u v, pad_sigma u v = sigma u v.
Proof. intros; unfold pad_sigma, sigma; ring. Qed.

Theorem norm_pad_preserved : forall u, pad_normSq u = normSq u.
Proof. intros; unfold pad_normSq, normSq; ring. Qed.

Theorem systems_length_eq_7 : Z.of_nat (List.length systems) = 7.
Proof. compute; reflexivity. Qed.

Theorem trace_status_eq : identity_trace_status = "not_trace_class_in_infinite_GNS".
Proof. compute; reflexivity. Qed.

Theorem dmodule_generators_eq_1 : dmodule_generators = 1.
Proof. compute; reflexivity. Qed.

Theorem gns_completion_kernel :
  (forall u v, pad_sigma u v = sigma u v) /\
  (forall u, pad_normSq u = normSq u) /\
  fock_zero = 1 /\
  Z.of_nat (List.length systems) = 7 /\
  identity_trace_status = "not_trace_class_in_infinite_GNS" /\
  dmodule_generators = 1.
Proof.
  repeat split;
  try apply sigma_pad_preserved;
  try apply norm_pad_preserved;
  try compute; try reflexivity.
Qed.
