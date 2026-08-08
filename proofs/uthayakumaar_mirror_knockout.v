From Stdlib Require Import QArith.
Open Scope Z_scope.

Definition two_tz (Zp Nn : Z) : Z := Nn - Zp.

Lemma two_tz_Mn47 : two_tz 25 22 = -3.
Proof. vm_compute; reflexivity. Qed.

Lemma two_tz_Ti47 : two_tz 22 25 = 3.
Proof. vm_compute; reflexivity. Qed.

Lemma two_tz_Cr45 : two_tz 24 21 = -3.
Proof. vm_compute; reflexivity. Qed.

Lemma two_tz_Sc45 : two_tz 21 24 = 3.
Proof. vm_compute; reflexivity. Qed.

Open Scope Q_scope.

Definition med (e_proton_rich e_neutron_rich : Q) : Q :=
  e_proton_rich - e_neutron_rich.

Definition suppression_line (deltaS : Q) : Q :=
  (61#100) - (2#125) * deltaS.

Definition Rs_Ti47 : Q := suppression_line (1916#1000).
Definition Rs_Mn47 : Q := suppression_line (1442#100).

Lemma Rs_Ti47_exact : Rs_Ti47 == 72418 # 125000.
Proof. vm_compute; reflexivity. Qed.

Lemma Rs_Mn47_exact : Rs_Mn47 == 4741 # 12500.
Proof. vm_compute; reflexivity. Qed.

Lemma first_excited_energy_MED_A47 :
  med (1226#10) (1594#10) == - (184#5).
Proof. vm_compute; reflexivity. Qed.

Definition BM1_ratio : Q := 97#100.

Lemma BM1_ratio_minus_one_exact :
  BM1_ratio - 1 == - (3#100).
Proof. vm_compute; reflexivity. Qed.
