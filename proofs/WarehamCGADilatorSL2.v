From Stdlib Require Import QArith List String.
Import ListNotations.
Open Scope Q_scope.
Open Scope string_scope.

Record M2Q := mkM { a00:Q; a01:Q; a10:Q; a11:Q }.
Definition madd A B := mkM (a00 A+a00 B) (a01 A+a01 B) (a10 A+a10 B) (a11 A+a11 B).
Definition mneg A := mkM (-a00 A) (-a01 A) (-a10 A) (-a11 A).
Definition msub A B := madd A (mneg B).
Definition smul c A := mkM (c*a00 A) (c*a01 A) (c*a10 A) (c*a11 A).
Definition mmul A B := mkM
  (a00 A*a00 B + a01 A*a10 B) (a00 A*a01 B + a01 A*a11 B)
  (a10 A*a00 B + a11 A*a10 B) (a10 A*a01 B + a11 A*a11 B).
Definition meq A B := a00 A == a00 B /\ a01 A == a01 B /\ a10 A == a10 B /\ a11 A == a11 B.
Definition I2 := mkM 1 0 0 1.
Definition Z2 := mkM 0 0 0 0.
Definition e := mkM 1 0 0 (-1).
Definition ebar := mkM 0 1 (-1) 0.
Definition S := mmul e ebar.
Definition nvec := madd e ebar.
Definition nbar := msub e ebar.
Definition comm A B := msub (mmul A B) (mmul B A).
Definition anticomm A B := madd (mmul A B) (mmul B A).
Definition H := mneg S.
Definition E := smul (1/2) nvec.
Definition F := smul (1/2) nbar.
Definition Casimir := madd (mmul H H) (smul 2 (madd (mmul E F) (mmul F E))).

Theorem wareham_dilator_sl2_kernel :
  meq (mmul e e) I2 /\ meq (mmul ebar ebar) (mneg I2) /\ meq (anticomm e ebar) Z2 /\
  meq (mmul S S) I2 /\ meq (mmul S nvec) (mneg nvec) /\ meq (mmul nvec S) nvec /\
  meq (mmul S nbar) nbar /\ meq (mmul nbar S) (mneg nbar) /\
  meq (anticomm S nvec) Z2 /\ meq (anticomm S nbar) Z2 /\ meq (anticomm nvec nbar) (smul 4 I2) /\
  meq (comm S nvec) (smul (-2) nvec) /\ meq (comm S nbar) (smul 2 nbar) /\ meq (comm nvec nbar) (smul (-4) S) /\
  meq (comm H E) (smul 2 E) /\ meq (comm H F) (smul (-2) F) /\ meq (comm E F) H /\
  meq Casimir (smul 3 I2) /\ meq (comm Casimir H) Z2 /\ meq (comm Casimir E) Z2 /\ meq (comm Casimir F) Z2.
Proof. vm_compute; repeat split; reflexivity. Qed.

Inductive Concept := Wareham_CGA_Dilator | Null_Basis_n_nbar | SL2R_Subalgebra | SO21_Isomorphic_Form | Quadratic_Casimir_3.
Inductive Edge := generated_by | anticommutes_with | closes_to | has_casimir | isomorphic_to.
Definition edgeHolds a e b :=
  match a,e,b with
  | Wareham_CGA_Dilator, generated_by, Null_Basis_n_nbar => true
  | Wareham_CGA_Dilator, closes_to, SL2R_Subalgebra => true
  | SL2R_Subalgebra, isomorphic_to, SO21_Isomorphic_Form => true
  | SL2R_Subalgebra, has_casimir, Quadratic_Casimir_3 => true
  | Null_Basis_n_nbar, anticommutes_with, Wareham_CGA_Dilator => true
  | _,_,_ => false
  end.

Theorem graph_kernel :
  edgeHolds Wareham_CGA_Dilator generated_by Null_Basis_n_nbar = true /\
  edgeHolds Wareham_CGA_Dilator closes_to SL2R_Subalgebra = true /\
  edgeHolds SL2R_Subalgebra isomorphic_to SO21_Isomorphic_Form = true /\
  edgeHolds SL2R_Subalgebra has_casimir Quadratic_Casimir_3 = true /\
  edgeHolds Null_Basis_n_nbar anticommutes_with Wareham_CGA_Dilator = true.
Proof. compute; repeat split; reflexivity. Qed.
