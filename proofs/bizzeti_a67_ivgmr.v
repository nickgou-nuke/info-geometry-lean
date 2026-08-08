From Coq Require Import QArith.
Open Scope Q_scope.

Definition mirror_asymmetry_ratio (eps : Q) : Q :=
  ((1 + eps) * (1 + eps)) / ((1 - eps) * (1 - eps)).

Definition uniform_one_body : Q := 752 # 1000.
Definition uniform_two_body : Q := 410 # 1000.
Definition uniform_eta : Q :=
  (uniform_one_body - uniform_two_body) / uniform_one_body.

Lemma uniform_eta_exact : uniform_eta == 171 # 376.
Proof. native_compute; reflexivity. Qed.

Definition eps_uniform_A1_negligible : Q := - (872 # 10000).
Definition eps_uniform_A0_negligible : Q := 120 # 1000.
Definition eps_ws_A1_negligible : Q := - (852 # 10000).
Definition eps_ws_A0_negligible : Q := 116 # 1000.

Definition R_uniform_A1_negligible : Q :=
  mirror_asymmetry_ratio eps_uniform_A1_negligible.

Definition R_uniform_A0_negligible : Q :=
  mirror_asymmetry_ratio eps_uniform_A0_negligible.

Lemma R_uniform_A1_negligible_exact :
  R_uniform_A1_negligible == 1301881 # 1846881.
Proof. native_compute; reflexivity. Qed.

Lemma R_uniform_A0_negligible_exact :
  R_uniform_A0_negligible == 196 # 121.
Proof. native_compute; reflexivity. Qed.

Definition higher_order_upper_relative : Q := 1 # 1000.

Lemma higher_order_three_orders :
  higher_order_upper_relative == (1#10) * (1#10) * (1#10).
Proof. native_compute; reflexivity. Qed.

Definition pf_average_lower_shell : Q := 615 # 1000.

Lemma two_body_coefficient_exact :
  (2#3) * pf_average_lower_shell == 41 # 100.
Proof. native_compute; reflexivity. Qed.
