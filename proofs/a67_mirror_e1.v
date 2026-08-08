Require Import QArith.
Open Scope Q_scope.

Definition spin_denominator (two_Ji : Q) : Q := two_Ji + 1.

Definition BE1_plus (two_Ji MIV MIS : Q) : Q :=
  ((MIV + MIS) * (MIV + MIS)) / spin_denominator two_Ji.

Definition BE1_minus (two_Ji MIV MIS : Q) : Q :=
  ((MIV - MIS) * (MIV - MIS)) / spin_denominator two_Ji.

Definition two_Ji_9half : Q := 9.
Definition MIV_725_717 : Q := 29 # 10000.
Definition MIS_725_717 : Q := 9 # 10000.

Definition BE1_As67_725 : Q := BE1_plus two_Ji_9half MIV_725_717 MIS_725_717.
Definition BE1_Se67_717 : Q := BE1_minus two_Ji_9half MIV_725_717 MIS_725_717.
Definition ratio_725_717 : Q := BE1_As67_725 / BE1_Se67_717.
Definition isoscalar_fraction_725_717 : Q := MIS_725_717 / MIV_725_717.

Lemma spin_denominator_9half : spin_denominator two_Ji_9half == 10.
Proof. native_compute; reflexivity. Qed.

Lemma BE1_As67_725_exact : BE1_As67_725 == 361 # 250000000.
Proof. native_compute; reflexivity. Qed.

Lemma BE1_Se67_717_exact : BE1_Se67_717 == 1 # 2500000.
Proof. native_compute; reflexivity. Qed.

Lemma ratio_725_717_exact : ratio_725_717 == 361 # 100.
Proof. native_compute; reflexivity. Qed.

Lemma isoscalar_fraction_exact : isoscalar_fraction_725_717 == 9 # 29.
Proof. native_compute; reflexivity. Qed.

Definition IVGMR_coefficient (A e R DeltaE0 : Q) : Q :=
  ((A - 1) * e * e) / (4 * R * DeltaE0).

Definition IVGMR_one_body (ri R : Q) : Q := (ri * ri * ri) / (R * R).

Definition IVGMR_two_body (ri rj R : Q) : Q := (ri * rj * rj) / (R * R * R).

Definition induced_isoscalar_kernel (A e R DeltaE0 ri rj : Q) : Q :=
  IVGMR_coefficient A e R DeltaE0 *
    (IVGMR_one_body ri R + IVGMR_two_body ri rj R).

Lemma IVGMR_unit_kernel_A67 :
  induced_isoscalar_kernel 67 1 1 20 1 1 == 33 # 20.
Proof. native_compute; reflexivity. Qed.
