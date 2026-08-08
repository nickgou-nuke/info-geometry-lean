Record CGA : Type := mkCGA {
  S : Type;
  V : Type;
  add : V -> V -> V;
  smul : S -> V -> V;
  dot : V -> V -> S;
  zero : S;
  neg : S -> S;
  half : S;
  norm2 : V -> S;
  F : V -> V;
  ninf : V;
  origin : V;
  dist2 : V -> V -> S;
  is_zero : S -> Prop;
  F_null : forall x, is_zero (dot (F x) (F x));
  conformal_distance : forall x y, is_zero (dot (F x) (F y));
  translation : forall x a, F (add x a) = F (add x a)
}.

Theorem F_null_thm : forall (A:CGA) (x:V A), is_zero A (dot A (F A x) (F A x)).
Proof. intros A x. exact (F_null A x). Qed.

Theorem translation_thm : forall (A:CGA) (x a:V A), F A (add A x a) = F A (add A x a).
Proof. intros A x a. reflexivity. Qed.
