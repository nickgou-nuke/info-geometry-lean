Require Import Reals.
Require Import Psatz.

Open Scope R_scope.

(* Legendre-Fenchel Pairing *)
Definition inner_prod (eta1 eta2 theta1 theta2 : R) : R :=
  eta1 * theta1 + eta2 * theta2.

(* Contragredient Mapping under SL(2, R) *)
Definition M_theta (a b c d theta1 theta2 : R) : R * R :=
  (a * theta1 + b * theta2, c * theta1 + d * theta2).

Definition MinvT_eta (a b c d eta1 eta2 : R) : R * R :=
  (d * eta1 - c * eta2, -b * eta1 + a * eta2).

(* Proof that the Legendre-Fenchel contact relation is strictly invariant under the dual representation *)
Theorem contragredient_invariance :
  forall a b c d eta1 eta2 theta1 theta2 : R,
  a * d - b * c = 1 ->
  let (theta1', theta2') := M_theta a b c d theta1 theta2 in
  let (eta1', eta2') := MinvT_eta a b c d eta1 eta2 in
  inner_prod eta1' eta2' theta1' theta2' = inner_prod eta1 eta2 theta1 theta2.
Proof.
  intros.
  unfold inner_prod, M_theta, MinvT_eta.
  nra.
Qed.
