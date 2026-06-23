Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Definition of Legendre Model on Real Numbers *)
Record LegendreModel : Type := {
  psi : R -> R;
  phi : R -> R;
  grad : R -> R;
  fenchel_ineq : forall theta eta : R, theta * eta <= psi theta + phi eta;
  contact : forall theta : R, phi (grad theta) = theta * grad theta - psi theta
}.

(* Fenchel Gap definition *)
Definition fenchelGap (L : LegendreModel) (theta eta : R) : R :=
  L.(psi) theta + L.(phi) eta - theta * eta.

(* Proof that Fenchel Gap is nonnegative *)
Theorem fenchelGap_nonneg : forall (L : LegendreModel) (theta eta : R),
  0 <= fenchelGap L theta eta.
Proof.
  intros L theta eta.
  unfold fenchelGap.
  generalize (L.(fenchel_ineq) theta eta).
  intro H.
  lra.
Qed.

(* Proof that Fenchel Gap is 0 at contact locus *)
Theorem fenchelGap_zero_at_contact : forall (L : LegendreModel) (theta : R),
  fenchelGap L theta (L.(grad) theta) = 0.
Proof.
  intros L theta.
  unfold fenchelGap.
  rewrite L.(contact) theta.
  ring.
Qed.
