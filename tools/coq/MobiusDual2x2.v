From Stdlib Require Import Reals Psatz.

Open Scope R_scope.

Definition pairing (eta1 eta2 theta1 theta2 : R) : R :=
  eta1 * theta1 + eta2 * theta2.

Definition fixed_poly (a b c d z : R) : R :=
  c * z * z + (d - a) * z - b.

Definition multiplier_at_zero (c d : R) : R := / (d * d).
Definition multiplier_at_infinity (a : R) : R := / (a * a).

Theorem hyperbolic_pairing_example :
  pairing (/2 * 3 - 0 * 5) (- 0 * 3 + 2 * 5) (2 * 7 + 0 * 11) (0 * 7 + /2 * 11)
    = pairing 3 5 7 11.
Proof.
  unfold pairing.
  nra.
Qed.

Theorem hyperbolic_fixed_zero :
  fixed_poly 2 0 0 (/2) 0 = 0.
Proof.
  unfold fixed_poly.
  ring.
Qed.

Theorem hyperbolic_fixed_polynomial_factor :
  forall z, fixed_poly 2 0 0 (/2) z = (-3/2) * z.
Proof.
  intro z.
  unfold fixed_poly.
  nra.
Qed.

Theorem hyperbolic_multipliers :
  multiplier_at_zero 0 (/2) = 4 /\ multiplier_at_infinity 2 = /4.
Proof.
  unfold multiplier_at_zero, multiplier_at_infinity.
  split; field.
Qed.
