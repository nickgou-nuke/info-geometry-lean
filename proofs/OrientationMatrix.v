Require Import ZArith.
Open Scope Z_scope.

Record Point : Type := mkPoint {
  x : Z;
  y : Z
}.

Definition orientation_det (p q r : Point) : Z :=
  (x q - x p) * (y r - y p) - (y q - y p) * (x r - x p).

Definition is_collinear (p q r : Point) : Prop :=
  orientation_det p q r = 0.

Definition is_convex (p q r : Point) : Prop :=
  orientation_det p q r > 0.

Definition is_concave (p q r : Point) : Prop :=
  orientation_det p q r < 0.

Lemma collinear_det_zero : forall p q r : Point,
  is_collinear p q r -> orientation_det p q r = 0.
Proof.
  intros p q r H.
  exact H.
Qed.
