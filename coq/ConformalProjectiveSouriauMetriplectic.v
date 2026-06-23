Require Import Reals.

Local Open Scope R_scope.

(* The Metriplectic bracket structure *)
Record MetriplecticStructure : Type := {
  poisson : R -> R -> R;
  metric : R -> R -> R;
  H : R;
  S : R;
  
  poisson_anti_symm : forall f g, poisson f g = - poisson g f;
  metric_symm : forall f g, metric f g = metric g f;
  poisson_self_zero : forall f, poisson f f = 0;
  metric_H_left_zero : forall f, metric H f = 0;
  poisson_S_left_zero : forall f, poisson S f = 0;
}.

(* Total evolution *)
Definition totalEvolution (M : MetriplecticStructure) (f : R) : R :=
  poisson M f (H M) + metric M f (S M).

(* Energy conservation theorem *)
Theorem energy_conservation (M : MetriplecticStructure) :
  totalEvolution M (H M) = 0.
Proof.
  unfold totalEvolution.
  rewrite (poisson_self_zero M).
  rewrite (metric_H_left_zero M).
  ring.
Qed.

(* Einstein Anomaly representation *)
Record EinsteinAnomalyContext : Type := {
  P_MP : R;
  P_D : R;
  anomaly : R;
  star : R -> R;
  
  anomaly_def : anomaly = P_MP * P_D - P_D * P_MP;
  star_mul : forall f g, star (f * g) = star g * star f;
  star_sub : forall f g, star (f - g) = star f - star g;
  star_P_MP : star P_MP = P_MP;
  star_P_D : star P_D = P_D;
}.

Theorem einstein_anomaly_skew_adjoint (C : EinsteinAnomalyContext) :
  star C (anomaly C) = - anomaly C.
Proof.
  destruct C.
  subst.
  rewrite star_sub.
  rewrite !star_mul.
  rewrite star_P_MP.
  rewrite star_P_D.
  ring.
Qed.
