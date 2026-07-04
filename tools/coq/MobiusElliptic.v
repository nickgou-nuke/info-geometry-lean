From Stdlib Require Import Reals.
From Stdlib Require Import Psatz.
Open Scope R_scope.

Lemma elliptic_boundary_limit : forall u v x y : R,
  u*u + v*v = 1 ->
  (u*x - v*y)^2 + (v*x + u*y)^2 = x^2 + y^2.
Proof.
  intros u v x y H.
  nra.
Qed.
