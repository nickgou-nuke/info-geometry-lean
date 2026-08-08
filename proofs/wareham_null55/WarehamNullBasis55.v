Require Import Stdlib.QArith.QArith.
Open Scope Q_scope.
Record SplitPair := mkPair { p : Q; m : Q }.
Definition q11 (x:SplitPair) : Q := p x * p x - m x * m x.
Definition bil11 (x y:SplitPair) : Q := p x * p y - m x * m y.
Definition negPair (x:SplitPair) : SplitPair := mkPair (-p x) (-m x).
Definition reflectE (x:SplitPair) : SplitPair := mkPair (-p x) (m x).
Definition e : SplitPair := mkPair 1 0.
Definition ebar : SplitPair := mkPair 0 1.
Definition n : SplitPair := mkPair 1 1.
Definition nbar : SplitPair := mkPair 1 (-1).
Theorem e_sq : q11 e == 1. Proof. vm_compute; reflexivity. Qed.
Theorem ebar_sq : q11 ebar == -1. Proof. vm_compute; reflexivity. Qed.
Theorem e_orth_ebar : bil11 e ebar == 0. Proof. vm_compute; reflexivity. Qed.
Theorem n_null : q11 n == 0. Proof. vm_compute; reflexivity. Qed.
Theorem nbar_null : q11 nbar == 0. Proof. vm_compute; reflexivity. Qed.
Theorem n_dot_nbar : bil11 n nbar == 2. Proof. vm_compute; reflexivity. Qed.
Theorem mass_split : forall dP dT, dT == 1#25 -> (dP+dT) - (dP-dT) == 2#25 + 0. Proof. intros; subst; ring. Qed.
