Require Import Reals.

(* Wareham Conformal Geometric Algebra in Coq *)

Axiom CGA : Type.
Axiom wedge : CGA -> CGA -> CGA.
Axiom dot : CGA -> CGA -> CGA.
Axiom e1 : CGA.
Axiom e2 : CGA.
Axiom e : CGA.
Axiom e_bar : CGA.
Axiom scalar_mul : R -> CGA -> CGA.
Axiom add : CGA -> CGA -> CGA.
Axiom sub : CGA -> CGA -> CGA.

Definition n := add e e_bar.
Definition n_bar := sub e e_bar.

(* F(x) = 1/2 (x^2 n + 2x - n_bar) *)
Definition F (x : CGA) (x_sq : R) : CGA :=
  scalar_mul 0.5 (sub (add (scalar_mul x_sq n) (scalar_mul 2.0 x)) n_bar).

(* C* = B - 1/2 rho^2 n *)
Definition circle_dual (B : CGA) (rho : R) : CGA :=
  sub B (scalar_mul (0.5 * rho * rho) n).
