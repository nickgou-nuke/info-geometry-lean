Require Import Reals.
Require Import ZArith.

Open Scope R_scope.

Record Path := {
  gamma : R -> R * R;
  closed : gamma 0 = gamma 1
}.

(* Parameterizing the winding number of a continuous path around a point in R^2 *)
Parameter winding_number : Path -> (R * R) -> Z.

(* Positive orientation in relation to winding number *)
Definition positively_oriented (p : Path) (interior_pt : R * R) : Prop :=
  (winding_number p interior_pt > 0)%Z.
