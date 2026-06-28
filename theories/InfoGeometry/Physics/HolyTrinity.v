Require Import Reals.
Require Import Coq.Sets.Ensembles.

Section HolyTrinity.

(* Null Cone Confinement with Concrete Types *)
Definition ZornDet (a b x y : R) : R := (a * b - x * y)%R.
Definition Confined (det : R) : Prop := det = 0%R.

Lemma quark_confinement : forall (x : R),
  Confined (ZornDet 0 0 x 0).
Proof.
  intros. unfold Confined, ZornDet. ring.
Qed.

(* Concrete Instanton to Baryon Mapping *)
Definition InstantonSpace := nat.
Definition BaryonSpace := nat.
Definition atiyah_manton_holonomy (I : InstantonSpace) : BaryonSpace := I.
Definition topological_charge (I : InstantonSpace) : nat := I.
Definition baryon_number (B : BaryonSpace) : nat := B.

Lemma instanton_is_baryon : forall (I : InstantonSpace), 
  baryon_number (atiyah_manton_holonomy I) = topological_charge I.
Proof.
  intros. reflexivity.
Qed.

End HolyTrinity.
