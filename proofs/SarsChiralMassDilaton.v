From Coq Require Import ZArith List String Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Record M2Z := mkM { a00:Z; a01:Z; a10:Z; a11:Z }.
Definition madd A B := mkM (a00 A+a00 B) (a01 A+a01 B) (a10 A+a10 B) (a11 A+a11 B).
Definition mmul A B := mkM
  (a00 A*a00 B + a01 A*a10 B) (a00 A*a01 B + a01 A*a11 B)
  (a10 A*a00 B + a11 A*a10 B) (a10 A*a01 B + a11 A*a11 B).
Definition smul m A := mkM (m*a00 A) (m*a01 A) (m*a10 A) (m*a11 A).
Definition PR := mkM 1 0 0 0.
Definition PL := mkM 0 0 0 1.
Definition I2 := mkM 1 0 0 1.
Definition Jmod := mkM 0 1 1 0.
Definition zeroM := mkM 0 0 0 0.
Definition diracMassCoupling m := smul m Jmod.
Definition diagBlock A := mkM (a00 A) 0 0 (a11 A).
Definition offBlock A := mkM 0 (a01 A) (a10 A) 0.
Definition springPotential2 (m lam : Z) := m*m*lam*lam.
Definition restoringForce (m lam : Z) := - m*m*lam.
Definition entropyQuadratic2 (x : Z) := x*x.

Inductive Concept := Left_Weyl_Sheet | Right_Weyl_Sheet | Tomita_Modular_Swap | Dirac_Mass_Coupling | Zitterbewegung | Dilaton_Weyl_Scale | Conformal_Spring | Orthogonal_Entropy_Transport.
Inductive Edge := swapped_by | couples_to | generates | breaks_weyl_scale_by | realizes_as | drives_orthogonal_transport.
Definition edgeHolds a e b :=
  match a,e,b with
  | Left_Weyl_Sheet, swapped_by, Tomita_Modular_Swap => true
  | Left_Weyl_Sheet, couples_to, Right_Weyl_Sheet => true
  | Dirac_Mass_Coupling, generates, Zitterbewegung => true
  | Dirac_Mass_Coupling, breaks_weyl_scale_by, Dilaton_Weyl_Scale => true
  | Dilaton_Weyl_Scale, realizes_as, Conformal_Spring => true
  | Conformal_Spring, drives_orthogonal_transport, Orthogonal_Entropy_Transport => true
  | _,_,_ => false
  end.

Theorem matrix_kernel :
  mmul PR PL = zeroM /\ madd PR PL = I2 /\ mmul (mmul Jmod PL) Jmod = PR /\
  (forall m, a00 (diracMassCoupling m) = 0 /\ a01 (diracMassCoupling m) = m /\ a10 (diracMassCoupling m) = m /\ a11 (diracMassCoupling m) = 0) /\
  (forall m, a00 (diagBlock (diracMassCoupling m)) = 0 /\ a01 (diagBlock (diracMassCoupling m)) = 0 /\ a10 (diagBlock (diracMassCoupling m)) = 0 /\ a11 (diagBlock (diracMassCoupling m)) = 0) /\
  (forall m, a00 (offBlock (diracMassCoupling m)) = a00 (diracMassCoupling m) /\ a01 (offBlock (diracMassCoupling m)) = a01 (diracMassCoupling m) /\ a10 (offBlock (diracMassCoupling m)) = a10 (diracMassCoupling m) /\ a11 (offBlock (diracMassCoupling m)) = a11 (diracMassCoupling m)).
Proof.
  repeat split; intros; unfold PR, PL, I2, Jmod, zeroM, diracMassCoupling, smul, diagBlock, offBlock, mmul, madd; simpl; try lia; reflexivity.
Qed.

Theorem spring_entropy_kernel :
  (forall m lam, 0 <= springPotential2 m lam) /\
  (forall m, springPotential2 m 0 = 0) /\
  (forall x, 0 <= entropyQuadratic2 x) /\
  entropyQuadratic2 0 = 0.
Proof.
  repeat split; intros; unfold springPotential2, entropyQuadratic2; try nia; reflexivity.
Qed.

Theorem graph_kernel :
  edgeHolds Left_Weyl_Sheet swapped_by Tomita_Modular_Swap = true /\
  edgeHolds Left_Weyl_Sheet couples_to Right_Weyl_Sheet = true /\
  edgeHolds Dirac_Mass_Coupling generates Zitterbewegung = true /\
  edgeHolds Dirac_Mass_Coupling breaks_weyl_scale_by Dilaton_Weyl_Scale = true /\
  edgeHolds Dilaton_Weyl_Scale realizes_as Conformal_Spring = true /\
  edgeHolds Conformal_Spring drives_orthogonal_transport Orthogonal_Entropy_Transport = true.
Proof. compute; repeat split; reflexivity. Qed.
