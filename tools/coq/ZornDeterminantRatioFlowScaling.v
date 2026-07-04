Require Import Stdlib.QArith.QArith.
Require Import Stdlib.setoid_ring.Ring.
Open Scope Q_scope.

Definition detZ
  (a b u1 u2 u3 v1 v2 v3 : Q) : Q :=
  a * b - (u1 * v1 + u2 * v2 + u3 * v3).

Theorem detZ_scale :
  forall r a b u1 u2 u3 v1 v2 v3 : Q,
    detZ (r*a) (r*b) (r*u1) (r*u2) (r*u3) (r*v1) (r*v2) (r*v3)
    == r*r * detZ a b u1 u2 u3 v1 v2 v3.
Proof.
  intros; unfold detZ; ring.
Qed.

Theorem common_scaling_ratio_cleared :
  forall r a b u1 u2 u3 v1 v2 v3 c d x1 x2 x3 y1 y2 y3 : Q,
    detZ (r*c) (r*d) (r*x1) (r*x2) (r*x3) (r*y1) (r*y2) (r*y3)
      * detZ a b u1 u2 u3 v1 v2 v3
    == detZ c d x1 x2 x3 y1 y2 y3
      * detZ (r*a) (r*b) (r*u1) (r*u2) (r*u3) (r*v1) (r*v2) (r*v3).
Proof.
  intros; repeat rewrite detZ_scale; ring.
Qed.

Theorem unequal_scaling_ratio_factor_cleared :
  forall s t a b u1 u2 u3 v1 v2 v3 c d x1 x2 x3 y1 y2 y3 : Q,
    s*s * detZ (t*c) (t*d) (t*x1) (t*x2) (t*x3) (t*y1) (t*y2) (t*y3)
      * detZ a b u1 u2 u3 v1 v2 v3
    == t*t * detZ c d x1 x2 x3 y1 y2 y3
      * detZ (s*a) (s*b) (s*u1) (s*u2) (s*u3) (s*v1) (s*v2) (s*v3).
Proof.
  intros; repeat rewrite detZ_scale; ring.
Qed.
