Require Import Reals.
Require Import Coq.Sets.Ensembles.

(* Formulate the consistent choice of orientation across tangent spaces. *)

Record TangentSpace (M : Type) (x : M) := mkTangentSpace {
  vec_space : Type;
  dimension : nat
}.

Definition Orientation (M : Type) (x : M) (Tx : TangentSpace M x) := R.

Record OrientableManifold (M : Type) := mkOrientableManifold {
  tangent_space : forall x : M, TangentSpace M x;
  orientation : forall x : M, Orientation M x (tangent_space x);
  consistency : forall x y : M, (orientation x (tangent_space x) > 0)%R <-> (orientation y (tangent_space y) > 0)%R
}.

Lemma orientability_consistent : forall (M : Type) (OM : OrientableManifold M) (x y : M),
  (orientation M OM x (tangent_space M OM x) > 0)%R -> (orientation M OM y (tangent_space M OM y) > 0)%R.
Proof.
  intros M OM x y H.
  apply (consistency M OM x y).
  exact H.
Qed.
