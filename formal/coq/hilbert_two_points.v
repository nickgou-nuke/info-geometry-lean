Require Import QArith.
Require Import List.
Import ListNotations.

(* The two-point set as booleans *)
Definition point := bool.

(* Functions from points to Q *)
Definition fun_space := point -> Q.

(* The delta functions *)
Definition delta0 (p : point) : Q :=
  if p then 0 else 1.

Definition delta1 (p : point) : Q :=
  if p then 1 else 0.

(* Linear combination: a * f + b * g *)
Definition lincomb (a b : Q) (f g : fun_space) (p : point) : Q :=
  a * f p + b * g p.

(* Equality of functions *)
Definition feq (f g : fun_space) : Prop := forall p, f p = g p.

(* Zero function *)
Definition zero_fun (p : point) : Q := 0.

(* Lemma: delta0 and delta1 are linearly independent *)
Lemma delta_independent :
  forall (a b : Q),
    (forall p : point, a * delta0 p + b * delta1 p = 0) ->
    a = 0 /\ b = 0.
Proof.
  intros a b h.
  have h0 := h true.
  have h1 := h false.
  simpl in h0, h1.
  (* p = true: delta0 true = 0, delta1 true = 1 *)
  (* p = false: delta0 false = 1, delta1 false = 0 *)
  from h0 =>
    (*
      a * 0 + b * 1 = 0  => b = 0
    *);
  from h1 =>
    (*
      a * 1 + b * 0 = 0  => a = 0
    *).
  - (* p = true *)
    norm_num at h0.
    linarith.
  - (* p = false *)
    norm_num at h1.
    linarith.
Qed.

(* Lemma: any function f can be written as a linear combination of delta0 and delta1 *)
Lemma delta_span :
  forall (f : fun_space),
    exists (a b : Q),
      forall p : point,
        f p = a * delta0 p + b * delta1 p.
Proof.
  intros f.
  (* Take a = f false, b = f true *)
  exists (f false), (f true).
  intro p.
  destruct p.
  - (* p = true *)
    simpl.
    rewrite <- f_equal_apply with (fun p => f p) by reflexivity.
    <;> ring.
  - (* p = false *)
    simpl.
    rewrite <- f_equal_apply with (fun p => f p) by reflexivity.
    <;> ring.
Qed.

(* Theorem: the dimension of the function space is 2 *)
Theorem dim_fun_space_two :
  exists (e1 e2 : fun_space),
    (forall (a b : Q), (forall p, a * e1 p + b * e2 p = 0) -> a = 0 /\ b = 0) /\
    (forall (f : fun_space), exists (a b : Q), forall p, f p = a * e1 p + b * e2 p).
Proof.
  refine' (delta0, delta1, _ , _).
  - exact delta_independent.
  - exact delta_span.
Qed.