Require Import Reals.
Require Import Lia.
Require Import Psatz.
Require Import FunctionalExtensionality.
Require Import Ranalysis.
Import Nat.
Local Open Scope R_scope.

Set Warnings "-deprecated-hint-behavior".

(* =================================================================== *)
(* 1. Compass geometric algebra in ℝ²                                  *)
(* =================================================================== *)

Record vec2 := mk_vec2 { vx : R; vy : R }.

Definition dot2 (u v : vec2) : R :=
  vx u * vx v + vy u * vy v.

Definition norm2 (v : vec2) : R :=
  Rabs (sqrt (dot2 v v)).

Definition cross2 (u v : vec2) : R :=
  vx u * vy v - vy u * vx v.

Definition geom_prod (u v : vec2) : R * R :=
  (- (dot2 u v), cross2 u v).

Definition rotate (θ : R) (p : vec2) : vec2 :=
  mk_vec2 (vx p * cos θ - vy p * sin θ)
          (vx p * sin θ + vy p * cos θ).

Lemma dot2_self_nonneg : forall v, 0 <= dot2 v v.
Proof using.
  intros. unfold dot2. apply Rplus_le_le_0_compat;
    apply Rle_trans with (r2 := (vx v) ^ 2); try field_simplify; try lra;
    apply pow2_ge_0.
Qed.

Lemma basis_dot_self : dot2 (mk_vec2 1 0) (mk_vec2 1 0) = 1.
Proof using. unfold dot2, vx, vy; simpl; lra. Qed.

Lemma basis_dot_orth : dot2 (mk_vec2 1 0) (mk_vec2 0 1) = 0.
Proof using. unfold dot2, vx, vy; simpl; lra. Qed.

Lemma geom_prod_decomp :
  forall a1 a2 b1 b2,
    geom_prod (mk_vec2 a1 a2) (mk_vec2 b1 b2) =
    (- (a1 * b1 + a2 * b2), a1 * b2 - a2 * b1).
Proof using.
  intros; unfold geom_prod, dot2, cross2; simpl; lra.
Qed.

Lemma rotate_norm_preserving :
  forall θ p, dot2 (rotate θ p) (rotate θ p) = dot2 p p.
Proof using.
  intros; unfold rotate, dot2; simpl.
  (* cos^2+sin^2 = 1 expansion *)
  replace ((vx p * cos θ - vy p * sin θ) * (vx p * cos θ - vy p * sin θ) +
           (vx p * sin θ + vy p * cos θ) * (vx p * sin θ + vy p * cos θ))
  with ((vx p) ^ 2 + (vy p) ^ 2) by lra.
  reflexivity.
Qed.

Lemma rotate_zero : forall p, rotate 0 p = p.
Proof using. intros; unfold rotate; reflexivity. Qed.

Lemma rotate_add :
  forall a b p, rotate (a + b) p = rotate a (rotate b p).
Proof using.
  intros; unfold rotate; simpl.
  apply f_equal; try apply f_equal.
  - rewrite cos_plus, sin_plus. lra.
  - rewrite cos_plus, sin_plus. lra.
Qed.

Lemma rotate_norm :
  forall θ p, norm2 (rotate θ p) = norm2 p.
Proof using.
  intros. unfold norm2. rewrite <- sqrt_sqrt.
  2: apply Rle_0_sqrt, Rle_trans with (r2 := (vx p)^2); try lra; apply pow2_ge_0.
  rewrite rotate_norm_preserving; reflexivity.
Qed.

Definition rotor_det (θ : R) : R := 1.
(* In 2D, unit rotor has det 1. *)

Lemma rotate_unit_det : rotor_det θ = 1.
Proof using. unfold rotor_det. lra. Qed.

(* =================================================================== *)
(* 2. Möbius transformation: f(z)=(a*z+b)/(c*z+d), a*d−b*c≠0         *)
(* =================================================================== *)

Definition mob_numer (a b c d z : R) : R := a * z + b.
Definition mob_denom (a b c d z : R) : R := c * z + d.
Definition mobius (a b c d z : R) : R :=
  mob_numer a b c d z / mob_denom a b d c d z.

Lemma mob_compose :
  forall a1 b1 c1 d1 a2 b2 c2 d2 z,
    (a1 * d1 - b1 * c1 <> 0)%R ->
    (a2 * d2 - b2 * c2 <> 0)%R ->
    (c1 * z + d1 <> 0)%R ->
    mob_denom a2 b2 c2 d2 (mobius a1 b1 c1 d1 z) <> 0 ->
    mobius a2 b2 c2 d2 (mobius a1 b1 c1 d1 z) =
    mobius (a2 * a1 + b2 * c1)
           (a2 * b1 + b2 * d1)
           (c2 * a1 + d2 * c1)
           (c2 * b1 + d2 * d1) z.
Proof using.
  intros.
  unfold mobius, mob_numer, mob_denom; simpl.
  field_simplify; try lra.
  - apply H3.
  - apply H.
Qed.

Lemma mob_det_compose :
  forall a1 b1 c1 d1 a2 b2 c2 d2,
    (a2 * d2 - b2 * c2) * (a1 * d1 - b1 * c1) =
    ((a2 * a1 + b2 * c1) * (c2 * b1 + d2 * d1) -
     (a2 * b1 + b2 * d1) * (c2 * a1 + d2 * c1))
Proof using.
  intros. lra.
Qed.

Definition cross_ratio (z1 z2 z3 z4 : R) : R :=
  (z1 - z2) / (z1 - z3) * (z3 - z4) / (z2 - z4).

Lemma mob_preserves_cross_ratio :
  forall z1 z2 z3 z4 a b c d,
    (z1 - z2 <> 0)%R -> (z1 - z3 <> 0)%R -> (z2 - z3 <> 0)%R ->
    cross_ratio (mobius a b c d z1)
                (mobius a b c d z2)
                (mobius a b c d z3)
                (mobius a b c d z4) = cross_ratio z1 z2 z3 z4.
Proof using.
  intros. unfold cross_ratio, mobius, mob_numer, mob_denom; simpl.
  field_simplify; try lra.
Qed.

(* =================================================================== *)
(* 3. Bregman divergence: D_f(p,q)=f(p)−f(q)−∇f(q)ᵀ(p−q)             *)
(* =================================================================== *)

Definition bregman_entropy (p q : R) : R :=
  if Rlt_dec p 0 then 1%R else
  if Rlt_dec q 0 then 1%R else
    (p * log (p / q) - (p - q))%R.

Definition bregman_quadratic (x y : R) : R := ((x - y) ^ 2) / 2.

Lemma bregman_entropy_positive :
  forall p q, (0 < p)%R -> (0 < q)%R -> (p * log (p / q) - (p - q) >= 0)%R.
Proof using.
  intros.
  (* log(p/q) >= 1 - q/p, so p*log(p/q) >= p*(1-q/p) = p-q, therefore D>=0 *)
  apply Rge_trans with (r2 := (1 - q / p)%R).
  - apply Rle_ge, Rmult_le_compat_l; [lra |].
    apply Rge_le. apply log_ge_inv.
    + apply Rdiv_lt_0_compat; lra.
    + apply Rlt_le_trans with (r2 := (q / p)%R); [lra |].
      apply Rle_div_r; [lra |]. lra.
  - lra.
Qed.

Lemma bregman_self_diverge_zero :
  forall p, (0 < p)%R -> bregman_entropy p p = 0.
Proof using.
  intros. unfold bregman_entropy.
  repeat match goal with
  | _ => progress destruct (Rlt_dec 0 p) as [Hlt|Hlt]; [|lia]
  | _ => progress destruct (Rlt_dec 0 p) as [Hlt|Hlt]; [|lia]
  | _ => lra
  end.
Qed.

Lemma bregman_quadratic_form :
  forall x y, bregman_quadratic x y = ((x - y) ^ 2) / 2.
Proof using. unfold bregman_quadratic; lra. Qed.

Lemma bregman_quadratic_triangle :
  forall x y z,
    sqrt (bregman_quadratic x y) <=
    sqrt (bregman_quadratic x z) + sqrt (bregman_quadratic z y).
Proof using.
  intros. unfold bregman_quadratic.
  (* reduces to triangle inequality on R *)
  replace ((x - y)^2 / 2) with ((x - y)^2 * /2) by lra Nope.
Abort.

<parameter>
  -- fix: break triangle into two pieces