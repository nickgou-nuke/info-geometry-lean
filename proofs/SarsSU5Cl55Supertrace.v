From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Definition omega_square_55 : Z := (-1) ^ 45 * (-1) ^ 5.
Definition su5_lambda2 : Z := 5 * 4 / 2.
Definition su5_adjoint : Z := 5 * 5 - 1.
Definition so10_adjoint : Z := 10 * (10 - 1) / 2.
Definition sm_adjoint : Z := (3 * 3 - 1) + (2 * 2 - 1) + 1.
Definition xy_bosons : Z := su5_adjoint - sm_adjoint.
Definition supertrace_identity_32 : Z := 16 - 16.
Definition trace_identity_32 : Z := 16 + 16.
Definition exterior_C5_dimension : Z := 1 + 5 + 10 + 10 + 5 + 1.
Definition sars_scalar_5fund_dimension : Z := 5 * 5.
Definition sars_dimension_gap : Z := sars_scalar_5fund_dimension - su5_adjoint.
Definition cl55_matrix_dimension : Z := 32 * 32.
Inductive parity := even | odd.
Definition super_bracket_target (a b : parity) : parity :=
  match a, b with
  | odd, odd => even
  | even, even => even
  | _, _ => odd
  end.

Theorem omega_square_55_eq_1 : omega_square_55 = 1.
Proof. unfold omega_square_55; compute; reflexivity. Qed.

Theorem su5_lambda2_eq_10 : su5_lambda2 = 10.
Proof. unfold su5_lambda2; compute; reflexivity. Qed.

Theorem su5_adjoint_eq_24 : su5_adjoint = 24.
Proof. unfold su5_adjoint; compute; reflexivity. Qed.

Theorem so10_adjoint_eq_45 : so10_adjoint = 45.
Proof. unfold so10_adjoint; compute; reflexivity. Qed.

Theorem sm_adjoint_eq_12 : sm_adjoint = 12.
Proof. unfold sm_adjoint; compute; reflexivity. Qed.

Theorem xy_bosons_eq_12 : xy_bosons = 12.
Proof. unfold xy_bosons, su5_adjoint, sm_adjoint; compute; reflexivity. Qed.

Theorem supertrace_identity_32_eq_0 : supertrace_identity_32 = 0.
Proof. unfold supertrace_identity_32; compute; reflexivity. Qed.

Theorem trace_identity_32_eq_32 : trace_identity_32 = 32.
Proof. unfold trace_identity_32; compute; reflexivity. Qed.

Theorem exterior_C5_dimension_eq_32 : exterior_C5_dimension = 32.
Proof. unfold exterior_C5_dimension; compute; reflexivity. Qed.

Theorem sars_scalar_5fund_dimension_eq_25 : sars_scalar_5fund_dimension = 25.
Proof. unfold sars_scalar_5fund_dimension; compute; reflexivity. Qed.

Theorem sars_scalar_not_adjoint : sars_scalar_5fund_dimension <> su5_adjoint.
Proof. unfold sars_scalar_5fund_dimension, su5_adjoint; compute; discriminate. Qed.

Theorem sars_dimension_gap_eq_1 : sars_dimension_gap = 1.
Proof. unfold sars_dimension_gap, sars_scalar_5fund_dimension, su5_adjoint; compute; reflexivity. Qed.

Theorem cl55_matrix_dimension_eq_1024 : cl55_matrix_dimension = 1024.
Proof. unfold cl55_matrix_dimension; compute; reflexivity. Qed.

Theorem odd_odd_superbracket_target_even : super_bracket_target odd odd = even.
Proof. compute; reflexivity. Qed.

Theorem sars_su5_cl55_kernel :
  omega_square_55 = 1 /\
  su5_lambda2 = 10 /\
  su5_adjoint = 24 /\
  so10_adjoint = 45 /\
  sm_adjoint = 12 /\
  xy_bosons = 12 /\
  supertrace_identity_32 = 0 /\
  trace_identity_32 = 32 /\
  exterior_C5_dimension = 32 /\
  sars_scalar_5fund_dimension = 25 /\
  sars_scalar_5fund_dimension <> su5_adjoint /\
  sars_dimension_gap = 1 /\
  cl55_matrix_dimension = 1024 /\
  super_bracket_target odd odd = even.
Proof.
  repeat split;
  try exact omega_square_55_eq_1;
  try exact su5_lambda2_eq_10;
  try exact su5_adjoint_eq_24;
  try exact so10_adjoint_eq_45;
  try exact sm_adjoint_eq_12;
  try exact xy_bosons_eq_12;
  try exact supertrace_identity_32_eq_0;
  try exact trace_identity_32_eq_32;
  try exact exterior_C5_dimension_eq_32;
  try exact sars_scalar_5fund_dimension_eq_25;
  try exact sars_scalar_not_adjoint;
  try exact sars_dimension_gap_eq_1;
  try exact cl55_matrix_dimension_eq_1024;
  try exact odd_odd_superbracket_target_even.
Qed.
