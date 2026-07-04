From Stdlib Require Import Reals.
Open Scope R_scope.

Definition C := (R * R)%type.

Definition C0 : C := (0, 0).
Definition C1 : C := (1, 0).
Definition Ci : C := (0, 1).

Definition Cadd (z w : C) : C :=
  (fst z + fst w, snd z + snd w).

Definition Cmul (z w : C) : C :=
  (fst z * fst w - snd z * snd w, fst z * snd w + snd z * fst w).

Definition Cdiv (z w : C) : C :=
  let d := fst w * fst w + snd w * snd w in
  ( (fst z * fst w + snd z * snd w) / d,
    (snd z * fst w - fst z * snd w) / d ).

Lemma mobius_eval_0 : Cdiv (Cadd C0 Ci) (Cadd (Cmul Ci C0) C1) = Ci.
Proof.
  unfold Cdiv, Cadd, Cmul, C0, C1, Ci.
  simpl.
  f_equal; field.
Qed.
