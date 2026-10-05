From Coq Require Import ZArith List String Lia Ring.
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
Definition det2 (A : M2Z) := a00 A * a11 A - a01 A * a10 A.

Theorem matrix_kernel :
  mmul PR PL = zeroM /\ madd PR PL = I2 /\ mmul (mmul Jmod PL) Jmod = PR /\
  (forall m, a00 (diracMassCoupling m) = 0 /\ a01 (diracMassCoupling m) = m /\ a10 (diracMassCoupling m) = m /\ a11 (diracMassCoupling m) = 0) /\
  (forall m, a00 (diagBlock (diracMassCoupling m)) = 0 /\ a01 (diagBlock (diracMassCoupling m)) = 0 /\ a10 (diagBlock (diracMassCoupling m)) = 0 /\ a11 (diagBlock (diracMassCoupling m)) = 0) /\
  (forall m, a00 (offBlock (diracMassCoupling m)) = a00 (diracMassCoupling m) /\ a01 (offBlock (diracMassCoupling m)) = a01 (diracMassCoupling m) /\ a10 (offBlock (diracMassCoupling m)) = a10 (diracMassCoupling m) /\ a11 (offBlock (diracMassCoupling m)) = a11 (diracMassCoupling m)).
Proof.
  repeat split; intros; unfold PR, PL, I2, Jmod, zeroM, diracMassCoupling, smul, diagBlock, offBlock, mmul, madd; simpl; try lia; reflexivity.
Qed.

(* The mass matrix determines a rest-energy splitting; it does not alone
   assert time-dependent Zitterbewegung. *)
Theorem dirac_mass_characteristic : forall m E,
  det2 (madd (diracMassCoupling m) (smul (-E) I2)) = (E-m)*(E+m).
Proof. intros; unfold det2, madd, diracMassCoupling, smul, I2, Jmod; simpl; ring. Qed.

Theorem spring_entropy_kernel :
  (forall m lam, 0 <= springPotential2 m lam) /\
  (forall m, springPotential2 m 0 = 0) /\
  (forall x, 0 <= entropyQuadratic2 x) /\
  entropyQuadratic2 0 = 0.
Proof.
  repeat split; intros; unfold springPotential2, entropyQuadratic2; try nia; reflexivity.
Qed.
