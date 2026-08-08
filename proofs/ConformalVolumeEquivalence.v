(* Coq Abstract Formalization *)

Inductive DiscreteManifold : Type :=
  | DManifold (points: nat).

Inductive ContinuousManifold : Type :=
  | CManifold (volume: nat).

Inductive ConformalGauge : Type :=
  | CGauge (scale: nat).

Definition relative_volume_form (d: DiscreteManifold) (c: ContinuousManifold) (g: ConformalGauge) : Prop :=
  match d, c, g with
  | DManifold p, CManifold v, CGauge s => p * s = v
  end.

Theorem exact_volume_form : forall (p s: nat),
  relative_volume_form (DManifold p) (CManifold (p * s)) (CGauge s).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.
