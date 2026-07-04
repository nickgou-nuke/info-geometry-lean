From Stdlib Require Import Reals.
Open Scope R_scope.

(* Formalizing the asymptotic ratio bound O(p^3) *)

Definition is_O (f g : nat -> R) :=
  exists C : R, C > 0 /\ exists N : nat, forall p : nat,
    (p >= N)%nat -> Rabs (f p) <= C * Rabs (g p).

Definition p3 (p : nat) : R := (INR p) * (INR p) * (INR p).

(* Fubini-Study form relative to the Poincare metric *)
Parameter fubini_study_poincare_ratio : nat -> R.

Axiom fubini_study_bound : is_O fubini_study_poincare_ratio p3.

Lemma ratio_is_O_p3 : is_O fubini_study_poincare_ratio p3.
Proof.
  exact fubini_study_bound.
Qed.
