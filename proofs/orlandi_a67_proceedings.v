From Stdlib Require Import QArith.
Open Scope Q_scope.

Definition centroid_shift_time (c_forward c_reverse : Q) : Q :=
  ((c_reverse - c_forward) * (56#100)) / 2.

Lemma raw_centroid_lifetime_As67_943_725 :
  centroid_shift_time (409497#100) (409805#100) == 1078#1250.
Proof. vm_compute; reflexivity. Qed.

Lemma branching_Se67_sum :
  (10#100) + (84#100) + (6#100) == 1.
Proof. vm_compute; reflexivity. Qed.

Lemma BE1_first_ratio_prelim :
  (13#10) / 1 == 13#10.
Proof. vm_compute; reflexivity. Qed.

Lemma BE1_second_ratio_prelim :
  (81#10) / (17#10) == 81#17.
Proof. vm_compute; reflexivity. Qed.

Lemma lifetime_difference_exact :
  (13#10) - (7#10) == 3#5.
Proof. vm_compute; reflexivity. Qed.

Lemma As67_12ns_gap_exact :
  (12 / 4) - (7#10) == 23#10.
Proof. vm_compute; reflexivity. Qed.
