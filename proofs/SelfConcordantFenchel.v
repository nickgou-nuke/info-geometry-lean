Require Import Reals.
Open Scope R_scope.

(* Self-concordant bounds of the logarithmic optimization basin under Fenchel duality. *)

Definition fenchel_dual (f : R -> R) (y : R) : R -> R :=
  fun x => x * y - f x.

Definition is_upper_bound (f : R -> R) (M : R) :=
  forall x, f x <= M.

Definition log_basin_bound (x : R) :=
  x <= 1.

Lemma fenchel_dual_eval : forall (f : R -> R) (y x : R),
  fenchel_dual f y x = x * y - f x.
Proof.
  intros. unfold fenchel_dual. reflexivity.
Qed.
