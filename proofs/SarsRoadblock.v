From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Definition a4_roots : Z := 5 * 4.
Definition sm_roots : Z := 3 * 2 + 2 * 1.
Definition broken_roots : Z := a4_roots - sm_roots.
Definition su5_adjoint : Z := 4 + a4_roots.
Definition sm_adjoint : Z := 4 + sm_roots.
Definition fundamental_scalar : Z := 5 * 5.
Definition exterior_c5 : Z := 1 + 5 + 10 + 10 + 5 + 1.
Definition so10_adjoint : Z := 10 * (10 - 1) / 2.
Definition cl55_dim : Z := 2 ^ 10.
Definition m32_dim : Z := 32 * 32.
Definition trace_gamma32 : Z := 16 - 16.
Definition trace_identity32 : Z := 16 + 16.

Inductive parity := Even | Odd.
Definition super_bracket_target (a b : parity) : parity :=
  match a, b with
  | Odd, Odd => Even
  | Even, Even => Even
  | _, _ => Odd
  end.

Theorem a4_roots_eq_20 : a4_roots = 20. Proof. compute; reflexivity. Qed.
Theorem sm_roots_eq_8 : sm_roots = 8. Proof. compute; reflexivity. Qed.
Theorem broken_roots_eq_12 : broken_roots = 12. Proof. compute; reflexivity. Qed.
Theorem su5_adjoint_eq_24 : su5_adjoint = 24. Proof. compute; reflexivity. Qed.
Theorem sm_adjoint_eq_12 : sm_adjoint = 12. Proof. compute; reflexivity. Qed.
Theorem fundamental_scalar_eq_25 : fundamental_scalar = 25. Proof. compute; reflexivity. Qed.
Theorem fundamental_scalar_not_adjoint : fundamental_scalar <> su5_adjoint. Proof. compute; discriminate. Qed.
Theorem dimension_gap_eq_1 : fundamental_scalar - su5_adjoint = 1. Proof. compute; reflexivity. Qed.
Theorem exterior_c5_eq_32 : exterior_c5 = 32. Proof. compute; reflexivity. Qed.
Theorem so10_adjoint_eq_45 : so10_adjoint = 45. Proof. compute; reflexivity. Qed.
Theorem cl55_m32_eq_1024 : cl55_dim = m32_dim /\ m32_dim = 1024. Proof. compute; split; reflexivity. Qed.
Theorem trace_gamma32_eq_0 : trace_gamma32 = 0. Proof. compute; reflexivity. Qed.
Theorem trace_identity32_eq_32 : trace_identity32 = 32. Proof. compute; reflexivity. Qed.
Theorem odd_odd_target_even : super_bracket_target Odd Odd = Even. Proof. compute; reflexivity. Qed.

Theorem sars_roadblock_kernel :
  a4_roots = 20 /\ sm_roots = 8 /\ broken_roots = 12 /\
  su5_adjoint = 24 /\ sm_adjoint = 12 /\ fundamental_scalar = 25 /\
  fundamental_scalar <> su5_adjoint /\ fundamental_scalar - su5_adjoint = 1 /\
  exterior_c5 = 32 /\ so10_adjoint = 45 /\ cl55_dim = m32_dim /\
  m32_dim = 1024 /\ trace_gamma32 = 0 /\ trace_identity32 = 32 /\
  super_bracket_target Odd Odd = Even.
Proof.
  repeat split;
  try exact a4_roots_eq_20; try exact sm_roots_eq_8; try exact broken_roots_eq_12;
  try exact su5_adjoint_eq_24; try exact sm_adjoint_eq_12;
  try exact fundamental_scalar_eq_25; try exact fundamental_scalar_not_adjoint;
  try exact dimension_gap_eq_1; try exact exterior_c5_eq_32; try exact so10_adjoint_eq_45;
  try exact (proj1 cl55_m32_eq_1024); try exact (proj2 cl55_m32_eq_1024);
  try exact trace_gamma32_eq_0; try exact trace_identity32_eq_32; try exact odd_odd_target_even.
Qed.
