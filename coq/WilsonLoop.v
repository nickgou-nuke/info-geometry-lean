Require Import Coq.Reals.Reals.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

(* Define gauge group G and its trace *)
Parameter G : Type.
Parameter G_mult : G -> G -> G.
Parameter G_inv : G -> G.
Parameter G_id : G.

(* Gauge transformation *)
Parameter trace : G -> R.
Axiom trace_cyclic : forall a b : G, trace (G_mult a b) = trace (G_mult b a).

(* Wilson loop as an element of G *)
Parameter wilson_loop : G.

(* Gauge transformed Wilson loop: W' = g * W * g^-1 *)
Definition gauge_transform (W g : G) : G :=
  G_mult g (G_mult W (G_inv g)).

Theorem wilson_loop_gauge_invariant : forall g W : G,
  trace (gauge_transform W g) = trace W.
Proof.
  intros g W.
  unfold gauge_transform.
  rewrite trace_cyclic.
Admitted.
