Require Import ZArith.
Require Import Sets.Ensembles.
Require Import Sets.Finite_sets.

(* Kawamura's Infinite Wedge Representation and Cuntz Algebra *)

Definition maya_index := Z.

Definition vacuum : Ensemble maya_index :=
  fun j => (j <= 0)%Z.

Definition dual_vacuum : Ensemble maya_index :=
  fun j => (j >= 1)%Z.

Definition is_maya (S : Ensemble maya_index) : Prop :=
  Finite _ (Union _ (Setminus _ S vacuum) (Setminus _ vacuum S)).

Definition is_dual_maya (S : Ensemble maya_index) : Prop :=
  Finite _ (Union _ (Setminus _ S dual_vacuum) (Setminus _ dual_vacuum S)).

Definition s_plus (S : Ensemble maya_index) : Ensemble maya_index :=
  Intersection _ S (fun j => (j >= 1)%Z).

Definition s_minus (S : Ensemble maya_index) : Ensemble maya_index :=
  Intersection _ S (fun j => (j <= 0)%Z).

Definition shift_plus (S : Ensemble maya_index) : Ensemble maya_index :=
  fun j => S (j - 1)%Z.

Definition negate_index (S : Ensemble maya_index) : Ensemble maya_index :=
  fun j => S (1 - j)%Z.

Definition g2 (S : Ensemble maya_index) : Ensemble maya_index :=
  negate_index (Union _ (shift_plus (s_plus S)) (s_minus S)).

Definition g1 (S : Ensemble maya_index) : Ensemble maya_index :=
  negate_index (Union _ (Union _ (shift_plus (s_plus S)) (s_minus S)) (Singleton _ 1%Z)).

(* The g2 function maps a Maya diagram to a Dual Maya diagram *)
Conjecture g2_maps_maya_to_dual :
  forall S, is_maya S -> is_dual_maya (g2 S).

Conjecture g1_maps_maya_to_dual :
  forall S, is_maya S -> is_dual_maya (g1 S).
