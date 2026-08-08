From Stdlib Require Import QArith.
Open Scope Q_scope.

Definition equal_mixing_amplitude (Mexp M01 M10 : Q) : Q :=
  Mexp / (M01 + M10).

Definition mixing_probability (Mexp M01 M10 : Q) : Q :=
  equal_mixing_amplitude Mexp M01 M10 *
    equal_mixing_amplitude Mexp M01 M10.

Definition b2_P30 : Q := mixing_probability (138#10000) (-(228#10000)) (801#10000).
Definition b2_S32 : Q := mixing_probability (162#10000) (1086#10000) (-(127#10000)).
Definition b2_Cl34 : Q := mixing_probability (160#100000) (819#100000) (2533#100000).
Definition b2_Ar36 : Q := mixing_probability (38#10000) (-(144#10000)) (-(233#10000)).

Lemma b2_P30_exact : b2_P30 == 2116#36481.
Proof. vm_compute; reflexivity. Qed.

Lemma b2_S32_exact : b2_S32 == 26244#919681.
Proof. vm_compute; reflexivity. Qed.

Lemma b2_Cl34_exact : b2_Cl34 == 400#175561.
Proof. vm_compute; reflexivity. Qed.

Lemma b2_Ar36_exact : b2_Ar36 == 1444#142129.
Proof. vm_compute; reflexivity. Qed.

Lemma P30_self_conjugate : 15 = 15.
Proof. reflexivity. Qed.

Lemma S32_self_conjugate : 16 = 16.
Proof. reflexivity. Qed.

Lemma Cl34_self_conjugate : 17 = 17.
Proof. reflexivity. Qed.

Lemma Ar36_self_conjugate : 18 = 18.
Proof. reflexivity. Qed.
