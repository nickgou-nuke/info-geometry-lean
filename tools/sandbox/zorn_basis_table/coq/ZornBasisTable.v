From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Module ZornBasisTableMod.
Record Cell := mk { r:Z; s:Z; x1:Z; x2:Z; x3:Z; y1:Z; y2:Z; y3:Z }.
Definition mulZ X Y := mk
 (r X*r Y + x1 X*y1 Y + x2 X*y2 Y + x3 X*y3 Y)
 (y1 X*x1 Y + y2 X*x2 Y + y3 X*x3 Y + s X*s Y)
 (r X*x1 Y + s Y*x1 X - (y2 X*y3 Y - y3 X*y2 Y))
 (r X*x2 Y + s Y*x2 X - (y3 X*y1 Y - y1 X*y3 Y))
 (r X*x3 Y + s Y*x3 X - (y1 X*y2 Y - y2 X*y1 Y))
 (r Y*y1 X + s X*y1 Y + (x2 X*x3 Y - x3 X*x2 Y))
 (r Y*y2 X + s X*y2 Y + (x3 X*x1 Y - x1 X*x3 Y))
 (r Y*y3 X + s X*y3 Y + (x1 X*x2 Y - x2 X*x1 Y)).
Definition negZ X := mk (-r X) (-s X) (-x1 X) (-x2 X) (-x3 X) (-y1 X) (-y2 X) (-y3 X).
Definition Z0:=mk 0 0 0 0 0 0 0 0. Definition E11:=mk 1 0 0 0 0 0 0 0. Definition E22:=mk 0 1 0 0 0 0 0 0.
Definition U1:=mk 0 0 1 0 0 0 0 0. Definition U2:=mk 0 0 0 1 0 0 0 0. Definition U3:=mk 0 0 0 0 1 0 0 0.
Definition V1:=mk 0 0 0 0 0 1 0 0. Definition V2:=mk 0 0 0 0 0 0 1 0. Definition V3:=mk 0 0 0 0 0 0 0 1.
Ltac zc := vm_compute; reflexivity.
Lemma T_E11_E11 : mulZ E11 E11 = E11. Proof. zc. Qed.
Lemma T_E11_E22 : mulZ E11 E22 = Z0. Proof. zc. Qed.
Lemma T_E11_U1 : mulZ E11 U1 = U1. Proof. zc. Qed.
Lemma T_E11_U2 : mulZ E11 U2 = U2. Proof. zc. Qed.
Lemma T_E11_U3 : mulZ E11 U3 = U3. Proof. zc. Qed.
Lemma T_E11_V1 : mulZ E11 V1 = Z0. Proof. zc. Qed.
Lemma T_E11_V2 : mulZ E11 V2 = Z0. Proof. zc. Qed.
Lemma T_E11_V3 : mulZ E11 V3 = Z0. Proof. zc. Qed.
Lemma T_E22_E11 : mulZ E22 E11 = Z0. Proof. zc. Qed.
Lemma T_E22_E22 : mulZ E22 E22 = E22. Proof. zc. Qed.
Lemma T_E22_U1 : mulZ E22 U1 = Z0. Proof. zc. Qed.
Lemma T_E22_U2 : mulZ E22 U2 = Z0. Proof. zc. Qed.
Lemma T_E22_U3 : mulZ E22 U3 = Z0. Proof. zc. Qed.
Lemma T_E22_V1 : mulZ E22 V1 = V1. Proof. zc. Qed.
Lemma T_E22_V2 : mulZ E22 V2 = V2. Proof. zc. Qed.
Lemma T_E22_V3 : mulZ E22 V3 = V3. Proof. zc. Qed.
Lemma T_U1_E11 : mulZ U1 E11 = Z0. Proof. zc. Qed.
Lemma T_U1_E22 : mulZ U1 E22 = U1. Proof. zc. Qed.
Lemma T_U1_U1 : mulZ U1 U1 = Z0. Proof. zc. Qed.
Lemma T_U1_U2 : mulZ U1 U2 = V3. Proof. zc. Qed.
Lemma T_U1_U3 : mulZ U1 U3 = negZ V2. Proof. zc. Qed.
Lemma T_U1_V1 : mulZ U1 V1 = E11. Proof. zc. Qed.
Lemma T_U1_V2 : mulZ U1 V2 = Z0. Proof. zc. Qed.
Lemma T_U1_V3 : mulZ U1 V3 = Z0. Proof. zc. Qed.
Lemma T_U2_E11 : mulZ U2 E11 = Z0. Proof. zc. Qed.
Lemma T_U2_E22 : mulZ U2 E22 = U2. Proof. zc. Qed.
Lemma T_U2_U1 : mulZ U2 U1 = negZ V3. Proof. zc. Qed.
Lemma T_U2_U2 : mulZ U2 U2 = Z0. Proof. zc. Qed.
Lemma T_U2_U3 : mulZ U2 U3 = V1. Proof. zc. Qed.
Lemma T_U2_V1 : mulZ U2 V1 = Z0. Proof. zc. Qed.
Lemma T_U2_V2 : mulZ U2 V2 = E11. Proof. zc. Qed.
Lemma T_U2_V3 : mulZ U2 V3 = Z0. Proof. zc. Qed.
Lemma T_U3_E11 : mulZ U3 E11 = Z0. Proof. zc. Qed.
Lemma T_U3_E22 : mulZ U3 E22 = U3. Proof. zc. Qed.
Lemma T_U3_U1 : mulZ U3 U1 = V2. Proof. zc. Qed.
Lemma T_U3_U2 : mulZ U3 U2 = negZ V1. Proof. zc. Qed.
Lemma T_U3_U3 : mulZ U3 U3 = Z0. Proof. zc. Qed.
Lemma T_U3_V1 : mulZ U3 V1 = Z0. Proof. zc. Qed.
Lemma T_U3_V2 : mulZ U3 V2 = Z0. Proof. zc. Qed.
Lemma T_U3_V3 : mulZ U3 V3 = E11. Proof. zc. Qed.
Lemma T_V1_E11 : mulZ V1 E11 = V1. Proof. zc. Qed.
Lemma T_V1_E22 : mulZ V1 E22 = Z0. Proof. zc. Qed.
Lemma T_V1_U1 : mulZ V1 U1 = E22. Proof. zc. Qed.
Lemma T_V1_U2 : mulZ V1 U2 = Z0. Proof. zc. Qed.
Lemma T_V1_U3 : mulZ V1 U3 = Z0. Proof. zc. Qed.
Lemma T_V1_V1 : mulZ V1 V1 = Z0. Proof. zc. Qed.
Lemma T_V1_V2 : mulZ V1 V2 = negZ U3. Proof. zc. Qed.
Lemma T_V1_V3 : mulZ V1 V3 = U2. Proof. zc. Qed.
Lemma T_V2_E11 : mulZ V2 E11 = V2. Proof. zc. Qed.
Lemma T_V2_E22 : mulZ V2 E22 = Z0. Proof. zc. Qed.
Lemma T_V2_U1 : mulZ V2 U1 = Z0. Proof. zc. Qed.
Lemma T_V2_U2 : mulZ V2 U2 = E22. Proof. zc. Qed.
Lemma T_V2_U3 : mulZ V2 U3 = Z0. Proof. zc. Qed.
Lemma T_V2_V1 : mulZ V2 V1 = U3. Proof. zc. Qed.
Lemma T_V2_V2 : mulZ V2 V2 = Z0. Proof. zc. Qed.
Lemma T_V2_V3 : mulZ V2 V3 = negZ U1. Proof. zc. Qed.
Lemma T_V3_E11 : mulZ V3 E11 = V3. Proof. zc. Qed.
Lemma T_V3_E22 : mulZ V3 E22 = Z0. Proof. zc. Qed.
Lemma T_V3_U1 : mulZ V3 U1 = Z0. Proof. zc. Qed.
Lemma T_V3_U2 : mulZ V3 U2 = Z0. Proof. zc. Qed.
Lemma T_V3_U3 : mulZ V3 U3 = E22. Proof. zc. Qed.
Lemma T_V3_V1 : mulZ V3 V1 = negZ U2. Proof. zc. Qed.
Lemma T_V3_V2 : mulZ V3 V2 = U1. Proof. zc. Qed.
Lemma T_V3_V3 : mulZ V3 V3 = Z0. Proof. zc. Qed.
End ZornBasisTableMod.
