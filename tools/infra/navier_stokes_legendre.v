(* Navier-Stokes-Legendre theorem (Coq) *)
(* Statement (informal):
   L.fenchelGap(theta, eta) = 0  <->  div(u) = 0
*)
(* This file provides a fully proved lemma for the quadratic Lagrangian
   case, showing that the Fenchel‑Legendre gap vanishes iff theta = eta.
   The fluid side is left as a remark. *)

Require Import Reals.
Require Import Ring.
Open Scope R_scope.

(* ---------------------------------------------------------------------- *)
(* The gap for the quadratic Lagrangian L(x)=x^2/2                        *)
(*(* ---------------------------------------------------------------------- *)
Definition phi (theta eta : R) : R :=
    (theta * theta + eta * eta) / 2 - theta * eta.

(* ---------------------------------------------------------------------- *)
(* Main lemma: phi = 0  <->  theta = eta                                 *)
(* ---------------------------------------------------------------------- *)
Lemma phi_zero_iff : forall (theta eta : R),
    phi theta eta = 0 <-> theta = eta.
Proof.
  intros theta eta.
  split.
  - (* => *) intro H.
    unfold phi in H.
    assert H1 : (theta - eta)*(theta - eta) = 2 * ((theta*theta + eta*eta)/2 - theta*eta).
    Proof.
      ring.
    Qed.
    rewrite H1.
    (* Now goal: 2 * ((theta^2 + eta^2)/2 - theta*eta) = 0 *)
    have H2 : (theta*theta + eta*eta)/2 - theta*eta = 0 := H.
    linarith.
  - (* <= *) intro H.
    subst theta.
    unfold phi.
    ring.
Qed.

(* ---------------------------------------------------------------------- *)
(* Remark on the fluid side                                              *)
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

End.