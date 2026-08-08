Require Import Stdlib.QArith.QArith.
Open Scope Q_scope.
Definition tauAs : Q := 7#10.
Definition tauSe : Q := 13#10.
Definition BE1As1 : Q := 13#10.
Definition BE1Se1 : Q := 1#1.
Definition BE1As2 : Q := (81#10) / (1000000#1).
Definition BE1Se2 : Q := (17#10) / (1000000#1).
Theorem tau_ratio : tauSe / tauAs == 13#7. Proof. native_compute; reflexivity. Qed.
Theorem BE1_first_ratio : BE1As1 / BE1Se1 == 13#10. Proof. native_compute; reflexivity. Qed.
Theorem BE1_second_ratio : BE1As2 / BE1Se2 == 81#17. Proof. native_compute; reflexivity. Qed.
Theorem BE1_second_delta : BE1As2 - BE1Se2 == (32#5)/(1000000#1). Proof. native_compute; reflexivity. Qed.
