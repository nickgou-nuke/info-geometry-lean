Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Record AddCommGroup : Type := {
  carrier : Type;
  zero : carrier;
  add : carrier -> carrier -> carrier;
  neg : carrier -> carrier;
  add_assoc : forall x y z, add (add x y) z = add x (add y z);
  zero_add : forall x, add zero x = x;
  add_zero : forall x, add x zero = x;
  add_left_neg : forall x, add (neg x) x = zero;
  add_comm : forall x y, add x y = add y x
}.

Record AddEquiv (G H : AddCommGroup) : Type := {
  to_fun : carrier G -> carrier H;
  inv_fun : carrier H -> carrier G;
  left_inv : forall x, inv_fun (to_fun x) = x;
  right_inv : forall y, to_fun (inv_fun y) = y;
  map_add : forall x y, to_fun (add G x y) = add H (to_fun x) (to_fun y)
}.

Definition trivial_type := unit.

Definition trivial_group : AddCommGroup.
Proof.
  refine {| carrier := unit; zero := tt; add := fun _ _ => tt; neg := fun _ => tt |};
  intros; destruct x; try destruct y; try destruct z; reflexivity.
Defined.

Record EMObject (G : AddCommGroup) (n : nat) : Type := {
  pi : nat -> AddCommGroup;
  diagonal : AddEquiv (pi n) G;
  off_diagonal : forall k, k <> n -> forall x y : carrier (pi k), x = y
}.

Definition KGn_has_correct_homotopy_groups (G : AddCommGroup) (n : nat) : Type :=
  EMObject G n.

Definition sphere_cohomology_carrier (k n : nat) : Type :=
  if Nat.eq_dec k n then Z else unit.

Definition sphere_cohomology_rank (k n : nat) : nat :=
  if Nat.eq_dec k n then 1 else 0.

Lemma sphere_cohomology_diagonal_rank :
  forall n, sphere_cohomology_rank n n = 1.
Proof.
  intro n; unfold sphere_cohomology_rank.
  destruct (Nat.eq_dec n n) as [_|h].
  - reflexivity.
  - contradiction.
Qed.

Lemma sphere_cohomology_off_diagonal_rank :
  forall k n, k <> n -> sphere_cohomology_rank k n = 0.
Proof.
  intros k n h; unfold sphere_cohomology_rank.
  destruct (Nat.eq_dec k n) as [hk|_].
  - contradiction.
  - reflexivity.
Qed.

Definition freudenthal_stable (n k : nat) : Prop :=
  k <= 2 * n - 2.

Lemma freudenthal_2_2 : freudenthal_stable 2 2.
Proof. unfold freudenthal_stable; lia. Qed.

Lemma freudenthal_3_4 : freudenthal_stable 3 4.
Proof. unfold freudenthal_stable; lia. Qed.

Lemma suspension_shift_index : forall k, S k = k + 1.
Proof. intro k; lia. Qed.

Lemma product_EM_pi1_order : 5 * 1 = 5.
Proof. reflexivity. Qed.

Lemma product_EM_pi2_order : 1 * 11 = 11.
Proof. reflexivity. Qed.
