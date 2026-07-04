Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Logic.FunctionalExtensionality.

Record ConnesCocycle (A : Type) := mkConnesCocycle {
  intertwiner : A -> A;
  cocycle_prop : forall a b : A, intertwiner a = intertwiner b -> a = b
}.

Lemma connes_cocycle_inj : forall (A : Type) (c : ConnesCocycle A) (a b : A),
  intertwiner A c a = intertwiner A c b -> a = b.
Proof.
  Admitted.
