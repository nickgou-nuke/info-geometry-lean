From Stdlib Require Import Reals.
From Stdlib Require Import Init.Datatypes.

(* Space of states in 2D CFT *)

(* Conformal dimensions for a generic state *)
Record ConformalDimension := {
  delta : R; (* left dimension \Delta *)
  delta_bar : R (* right dimension \bar{\Delta} *)
}.

(* Conformal spin \Delta - \bar{\Delta} *)
Definition conformal_spin (d : ConformalDimension) : R :=
  Rminus (delta d) (delta_bar d).

(* Virasoro representations *)
Parameter Representation : Type.
Parameter tensor_product : Representation -> Representation -> Representation.
Parameter direct_sum : Representation -> Representation -> Representation.

(* Primary fields *)
Parameter PrimaryField : Type.
Parameter left_rep : PrimaryField -> Representation.
Parameter right_rep : PrimaryField -> Representation.

(* Diagonal CFT condition: left and right representations match *)
Axiom diagonal_cft_condition : forall (p : PrimaryField), left_rep p = right_rep p.

(* Hilbert space *)
Parameter HilbertSpace : Type.
Parameter construct_space : (PrimaryField -> Representation) -> HilbertSpace.

(* R \otimes \bar{R} for diagonal CFT *)
Definition diagonal_cft_space :=
  construct_space (fun p => tensor_product (left_rep p) (right_rep p)).

(* Functional extensionality for the proof *)
Axiom functional_extensionality : forall A B (f g : A -> B), (forall x, f x = g x) -> f = g.

Lemma diagonal_cft_space_struct :
  diagonal_cft_space = construct_space (fun p => tensor_product (left_rep p) (left_rep p)).
Proof.
  unfold diagonal_cft_space.
  f_equal.
  apply functional_extensionality.
  intro p.
  rewrite diagonal_cft_condition.
  reflexivity.
Qed.
