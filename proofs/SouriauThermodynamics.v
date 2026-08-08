Require Import ZArith.
Require Import Lia.

(* Thermodynamic formulation over conservative symplectic leaves *)

Definition jordan_product (a b : Z) : Z :=
  a * b + b * a.

Definition lie_bracket (a b : Z) : Z :=
  a * b - b * a.

Definition metriplectic_flow (f H S : Z) : Z :=
  lie_bracket f H + jordan_product f S.

Lemma metric_symplectic_split : forall a b : Z,
  a * b + a * b = jordan_product a b + lie_bracket a b.
Proof.
  intros a b.
  unfold jordan_product, lie_bracket.
  lia.
Qed.
