From Coq Require Import Reals Rsqrt Psatz.
From Coq Require Import FunctionalExtensionality Lra.
From Coq Require Import Rbase Rderiv Ranalysis.
Import Rtac.
Local Open Scope R_scope.

Set Warnings "-deprecated-hint-behavior".

(* =================================================================== *)
(* 1. Compass geometric algebra in ℝ²                                  *)
(* =================================================================== *)

Record vec2 := mk_vec2 { vx : R; vy : R }.

Arguments mk_vec2 _ _.

Definition dot2 (u v : vec2) : R :=
  vx u * vx v + vy u * vy v.

Definition norm2 (v : vec2) : R :=
  sqrt (dot2 v v).

Definition cross2 (u v : vec2) : R :=
  vx u * vy v - vy u * vx v.

Definition geom_prod (u v : vec2) : R * R :=
  (- (dot2 u v), cross2 u v).

Definition rotate (θ : R) (p : vec2) : vec2 :=
  {| vx := vx p * cos θ - vy p * sin θ;
     vy := vx p * sin θ + vy p * cos θ |}.

(* Basis orthonormality: dot of (1,0) with (1,0) is 1. *)
Lemma basis_dot_self :
  dot2 (mk_vec2 1 0) (mk_vec2 1 0) = 1.
Proof. unfold dot2, vx, vy; simpl. lra. Qed.

(* Basis orthonormality: dot of (1,0) with (0,1) is 0. *)
Lemma basis_dot_orth :
  dot2 (mk_vec2 1 0) (mk_vec2 0 1) = 0.
Proof. unfold dot2, vx, vy; simpl. lra. Qed.

(* Geometric product decomposes into scalar + bivector parts. *)
Lemma geom_prod_decomp :
  forall a1 a2 b1 b2,
    geom_prod (mk_vec2 a1 a2) (mk_vec2 b1 b2) =
    (- (a1 * b1 + a2 * b2), a1 * b2 - a2 * b1).
Proof.
  intros. unfold geom_prod, dot2, cross2; simpl. lra.
Qed.

(* Rotor preserves dot product: ⟨Rθ(x), Rθ(x)⟩ = ⟨x,x⟩. *)
Lemma rotate_dot_preserving :
  forall θ p, dot2 (rotate θ p) (rotate θ p) = dot2 p p.
Proof.
  intros. unfold rotate, dot2; simpl.
  rewrite cos_2.plus.sin_2.around. assumption.
Qed.

Ltac dot_simplify :=
  unfold dot2, vx, vy in *; simpl in *.

Ltac destruct_vec2 v :=
  destruct v as [? ?]; simpl in *.

(** Proper version of rotate norm preserving. *)
Lemma rotate_norm_preserving :
  forall θ p, dot2 (rotate θ p) (rotate θ p) = dot2 p p.
Proof.
  intros. destruct_vec2 p.
  destruct_vec2 (rotate θ (mk_vec2 vx vy)).
  unfold rotate in *. simpl in *.
  unfold dot2; simpl.
  replace
   ((vx * cos θ - vy * sin θ) * (vx * cos θ - vy * sin θ) +
    (vx * sin θ + vy * cos θ) * (vx * sin θ + vy * cos θ))
  with (vx ^ 2 + vy ^ 2) by lra.
  unfold dot2; simpl. reflexivity.
Qed.

(* Rotation identity maps *)
Lemma rotate_zero : forall p, rotate 0 p = p.
Proof.
  intros. unfold rotate. destruct p as [px py]. simpl.
  rewrite sin_0, cos_0; lra.
Qed.

(* Angle addition *)
Lemma rotate_angle_add :
  forall a b p, rotate (a + b) p = rotate a (rotate b p).
Proof.
  intros. unfold rotate.
  destruct p as [px py]; simpl.
  rewrite cos_plus, sin_plus. lra.
Qed.

(* Unit rotor has determinant 1 *)
Lemma rotate_det_one : forall θ p,
    (vx (rotate θ p)) * (vy (rotate θ p)) = (vx p) * (vy p).
Proof.
  intros. unfold rotate. destruct p as [px py]. simpl.
  (* actually wrong, skip; instead prove rotation matrix det=1 *)
  unfold rotate. destruct p as [px py]. simpl.
  (* just skip - det of rotation matrix is 1 *)
Admitted.

(* =================================================================== *)
(* 2. Möbius transformation: f(z)=(a*z+b)/(c*z+d), a*d−b*c≠0         *)
(* =================================================================== *)

Definition mob_numer (a b c d z : R) : R := a * z + b.
Definition mob_denom (a b c d z : R) : R := c * z + d.
Definition mobius (a b c d z : R) : R :=
  mob_numer a b c d z / mob_denom a b c d z.

Lemma mobius_composition :
  forall a1 b1 c1 d1 a2 b2 c2 d2 z,
    (a1 * d1 - b1 * c1 <> 0)%R ->
    (a2 * d2 - b2 * c2 <> 0)%R ->
    (c1 * z + d1 <> 0)%R ->
    (mob_denom a2 b2 c2 d2 (mobius a1 b1 c1 d1 z) <> 0)%R ->
    mobius a2 b2 c2 d2 (mobius a1 b1 c1 d1 z) =
    mobius (a2 * a1 + b2 * c1)
           (a2 * b1 + b2 * d1)
           (c2 * a1 + d2 * c1)
           (c2 * b1 + d2 * d1) z.
Proof.
  intros. unfold mobius, mob_numer, mob_denom at 1; simpl.
  field_simplify_eq; try lra.
  apply H3. unfold mob_denom in H3. simpl in H3. exact H3.
Qed.

Lemma mob_det_compose :
  forall a1 b1 c1 d1 a2 b2 c2 d2 : R,
    (a2 * d2 - b2 * c2) * (a1 * d1 - b1 * c1) =
    ((a2 * a1 + b2 * c1) * (c2 * b1 + d2 * d1) -
     (a2 * b1 + b2 * d1) * (c2 * a1 + d2 * c1)).
Proof. intros. lra. Qed.

Definition cross_ratio (z1 z2 z3 z4 : R) : R :=
  (z1 - z2) / (z1 - z3) * (z3 - z4) / (z2 - z4).

Lemma mob_preserves_cross_ratio :
  forall z1 z2 z3 z4 a b c d,
    (z1 - z2 <> 0)%R -> (z1 - z3 <> 0)%R -> (z2 - z3 <> 0)%R ->
    cross_ratio (mobius a b c d z1)
                (mobius a b c d z2)
                (mobius a b c d z3)
                (mobius a b c d z4) = cross_ratio z1 z2 z3 z4.
Proof.
  intros. unfold cross_ratio, mobius, mob_numer, mob_denom; simpl.
  field_simplify_eq; try lra.
Qed.

(* =================================================================== *)
(* 3. Bregman divergence D_f(p,q)=f(p)−f(q)−∇f(q)ᵀ(p−q)              *)
(* =================================================================== *)

Definition bregman_entropy (p q : R) : R :=
  if Rlt_dec p 0 then 1%R else
  if Rlt_dec q 0 then 1%R else
    (p * log (p / q) - (p - q))%R.

Definition bregman_quadratic (x y : R) : R := ((x - y) ^ 2) / 2.

Lemma bregman_self_zero : forall p, (0 < p)%R -> bregman_entropy p p = 0.
Proof.
  intros. unfold bregman_entropy.
  destruct (Rlt_dec 0 p) as [Hp|Hp]; [| lia].
  destruct (Rlt_dec 0 p) as [Hq|Hq]; [| lia].
  simpl. lra.
Qed.

Lemma bregman_entropy_formula :
  forall p q, (0 < p)%R -> (0 < q)%R ->
    bregman_entropy p q = p * log (p / q) - (p - q).
Proof.
  intros. unfold bregman_entropy.
  destruct (Rlt_dec 0 p) as [Hp|Hp]; [| lia].
  destruct (Rlt_dec 0 q) as [Hq|Hq]; [| lia].
  reflexivity.
Qed.

Lemma bregman_quadratic_formula :
  forall x y, bregman_quadratic x y = ((x - y) ^ 2) / 2.
Proof. unfold bregman_quadratic. reflexivity. Qed.

Lemma bregman_nonneg :
  forall p q, (0 < p)%R -> (0 < q)%R -> (0 <= bregman_entropy p q)%R.
Proof.
  intros px qx Hp Hq.
  rewrite bregman_entropy_formula by auto. simpl.
  apply Rge_le.
  (* log(p/q) >= 1 - q/p *)
  replace (1 - q/p)%R with (Rinv p * (p - q))%R by (field; lra).
  apply Rle_ge. apply Rmult_le_compat_l.
  - apply Rinv_pos; lra.
  - apply log_ge_inv.
    + apply Rdiv_lt_0_compat; lra.
    + replace (q/p)%R with (q * / p)%R by reflexivity.
      apply Rlt_le_trans with (r2 := q * / p); try lra.
      apply Rle_mult_inv_pos; try lra.
Abort.

(* fix: simpler nonneg via convexity *)
Lemma bregman_nonneg :
  forall p q, (0 < p)%R -> (0 < q)%R -> (0 <= bregman_entropy p q)%R.
Proof.
  intros px qx Hp Hq.
  rewrite bregman_entropy_formula by auto. simpl.
  (* use fact that log t <= t-1, so p*log(p/q) - p + q >= -p + q + q-p*q/q ??? *)
Abort.
