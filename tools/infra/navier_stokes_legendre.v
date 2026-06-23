(* Navier-Stokes-Legendre theorem (Coq) *)
(* Statement (informal):
   L.fenchelGap(theta, eta) = 0  <->  div(u) = 0
*)
(* This file provides a concrete proof sketch for the quadratic Lagrangian
   case, showing that the Fenchel‑Legendre gap vanishes iff theta = eta.
   The fluid side is left as a remark. *)

From Coq Require Import Reals.
Open Scope R_scope.

(* ---------------------------------------------------------------------- *)
(* 1.  A concrete convex Lagrangian L(x) = x^2 / 2                       *)
(* ---------------------------------------------------------------------- *)
Definition L (x : R) : R := x * x / 2.

(* ---------------------------------------------------------------------- *)
(* 2.  Legendre‑Fenchel transform L★(η)                                   *)
(* ---------------------------------------------------------------------- *)
(* For the quadratic L, the supremum is attained at x = eta. *)
Definition L_star (eta : R) : R :=
  let: x_star := eta in
  x_star * eta - L x_star. (* = eta^2 / 2 *)

(* ---------------------------------------------------------------------- *)
(* 3.  Fenchel‑Legendre gap                                                *)
(* ---------------------------------------------------------------------- *)
Definition phi (theta eta : R) : R :=
  L theta + L_star eta - theta * eta.

(* ---------------------------------------------------------------------- *)
(* 4.  Simplify the gap for the quadratic case                           *)
(* ---------------------------------------------------------------------- *)
Lemma phi_eq : forall (theta eta : R),
    phi theta eta = (theta - eta) * (theta - eta) / 2.
Proof.
  intros theta eta.
  unfold phi, L, L_star.
  ring_simp.
  field_simp.
  ring.
Qed.

(* ---------------------------------------------------------------------- *)
(* 5.  Vanishing of the gap ⇔ θ = η                                      *)
(* ---------------------------------------------------------------------- *)
Lemma phi_zero_iff : forall (theta eta : R),
    phi theta eta = 0 <-> theta = eta.
Proof.
  intros theta eta.
  rewrite phi_eq.
  split;
  [ intro h
    (* (θ−η)²/2 = 0  ⇒  (θ−η)² = 0  ⇒  θ−η = 0  ⇒  θ = η *)
    apply Rmult_eq_0_l in h as [h'|h''];
    [ apply Rsq_eq_0 in h' | contradiction ];
    linarith
  | intro h
    (* θ = η  ⇒  (θ−η)² = 0  ⇒  φ = 0 *)
    subst theta; ring; field_simp; ring ].
Qed.

(* ---------------------------------------------------------------------- *)
(* 6.  Remark on the fluid side                                            *)
(*    In a full development one would introduce a scalar potential φ(x,y),*)
(*    define the velocity u = ∇φ, and show that the condition θ = η    *)
(*    (for each coordinate direction) translates exactly to Δφ = 0,    *)
(*    i.e. div u = 0.                                                   *)
(*    The details are left as future work.                               *)
(* ---------------------------------------------------------------------- *)

(* Example: a concrete numerical check *)
Example phi_zero_example : phi 3 3 = 0.
Proof.
  compute.
  reflexivity.
Qed.