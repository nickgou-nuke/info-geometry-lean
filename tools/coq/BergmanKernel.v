From Stdlib Require Import Reals.
Open Scope R_scope.

(* Formalizing the Bergman kernel scaling on the unit disk *)

Definition hermitian_metric_scaling (r : R) : R := 1 / (1 - r^2)^2.
Definition poincare_disk_boundary_scaling (r : R) : R := 1 / (1 - r^2)^2.

Theorem metric_scaling_matches :
  forall r : R, -1 < r -> r < 1 ->
  hermitian_metric_scaling r = poincare_disk_boundary_scaling r.
Proof.
  intros r H1 H2.
  unfold hermitian_metric_scaling, poincare_disk_boundary_scaling.
  reflexivity.
Qed.
