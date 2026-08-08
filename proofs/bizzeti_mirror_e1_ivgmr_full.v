Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.Strings.String.

Open Scope Q_scope.

Definition T3 (Z N : Q) : Q := (Z - N) / 2.

Lemma T3_As67 : T3 33 34 == - 1 / 2.
Proof. unfold T3; field. Qed.

Lemma T3_Se67 : T3 34 33 == 1 / 2.
Proof. unfold T3; field. Qed.

Definition As725_BE1 : Q := 14 / 10000000.
Definition Se717_BE1 : Q := 4 / 10000000.
Definition As725_ME1 : Q := 37 / 10000.
Definition Se717_ME1 : Q := 20 / 10000.
Definition As319_BE1 : Q := 83 / 10000000.
Definition Se303_BE1_upper : Q := 14 / 10000000.
Definition As319_ME1 : Q := 91 / 10000.
Definition Se303_ME1_upper : Q := 37 / 10000.

Lemma tableI_first_BE1_ratio : As725_BE1 / Se717_BE1 == 7 / 2.
Proof. unfold As725_BE1, Se717_BE1; field. Qed.

Lemma tableI_first_ME1_ratio : As725_ME1 / Se717_ME1 == 37 / 20.
Proof. unfold As725_ME1, Se717_ME1; field. Qed.

Lemma tableI_second_BE1_ratio_upper : As319_BE1 / Se303_BE1_upper == 83 / 14.
Proof. unfold As319_BE1, Se303_BE1_upper; field. Qed.

Lemma tableI_second_ME1_ratio_upper : As319_ME1 / Se303_ME1_upper == 91 / 37.
Proof. unfold As319_ME1, Se303_ME1_upper; field. Qed.

Definition MIV : Q := 29 / 10000.
Definition MIS : Q := 9 / 10000.

Lemma isoscalar_fraction : MIS / MIV == 9 / 29.
Proof. unfold MIS, MIV; field. Qed.

Definition radial_cubic_siegert_ratio : Q := 834 / 1000.
Definition charge_correction_1MeV : Q := 190 / 10000000.
Definition magnetic_correction_1MeV : Q := 53 / 100000.

Lemma radial_cubic_siegert_exact : radial_cubic_siegert_ratio == 417 / 500.
Proof. unfold radial_cubic_siegert_ratio; field. Qed.

Lemma correction_charge_subpermille : charge_correction_1MeV < 1 / 1000.
Proof. unfold charge_correction_1MeV; vm_compute; reflexivity. Qed.

Lemma correction_magnetic_subpermille : magnetic_correction_1MeV < 1 / 1000.
Proof. unfold magnetic_correction_1MeV; vm_compute; reflexivity. Qed.

Definition C : Q := 116 / 1000.
Definition one_body : Q := 752 / 1000.
Definition two_body : Q := 410 / 1000.
Definition eta : Q := (one_body - two_body) / one_body.
Definition pf_average_r2 : Q := 615 / 1000.

Lemma eta_exact : eta == 171 / 376.
Proof. unfold eta, one_body, two_body; field. Qed.

Lemma two_body_from_pf_average : (2 / 3) * pf_average_r2 == two_body.
Proof. unfold pf_average_r2, two_body; field. Qed.

Definition mirror_ratio (eps : Q) : Q := ((1 + eps) / (1 - eps)) ^ 2.

Definition eps_A1_negligible : Q := - 872 / 10000.
Definition eps_A0_negligible : Q := 120 / 1000.

Lemma ratio_A1_negligible_exact :
  mirror_ratio eps_A1_negligible == 1301881 / 1846881.
Proof. unfold mirror_ratio, eps_A1_negligible; field. Qed.

Lemma ratio_A0_negligible_exact :
  mirror_ratio eps_A0_negligible == 196 / 121.
Proof. unfold mirror_ratio, eps_A0_negligible; field. Qed.

Definition eq60_epsilon_kernel (C0 radial_ratio eta0 A1 A0 : Q) : Q :=
  3 * C0 * radial_ratio * ((eta0 * A1 - A0) / (A1 + 3 * A0)).

Lemma eq60_A0_negligible_epsilon :
  eq60_epsilon_kernel C one_body eta 1 0 == 14877 / 125000.
Proof. unfold eq60_epsilon_kernel, C, one_body, eta, two_body; vm_compute; reflexivity. Qed.

Lemma A67_IVGMR_unit_kernel :
  ((67 - 1) / (4 * 20)) * (1 + 1) == 33 / 20.
Proof. field. Qed.
